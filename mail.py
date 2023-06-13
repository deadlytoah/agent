#
# Reliable Interface to GPT via Gmail
# Copyright (C) 2023  Hee Shin
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.
#

import asyncio
from asyncio import Queue
from sys import stderr
from typing import AsyncIterator

from openai import InvalidRequestError

from controller.email import EmailController, SetOfAddresses
from controller.msgq import EmailMessage, EmailMsgqController, EmailStatus
from proxy import gpt, mail
from proxy.gpt import GptMessageSeq, GptService
from proxy.msgq import DatabaseConstraintException

AGENT_EMAIL_ADDRESS = 'thevoicekorea+chat@gmail.com'


class Poller:
    """
    Polls the mail service for new threads.

    :param email_controller: The email controller to use for polling.
    :type email_controller: EmailController
    :param interval: The interval to poll the mail service.
    :type interval: int
    """

    def __init__(self, email_controller: EmailController, interval: int) -> None:
        self.email_controller = email_controller
        self.interval = interval

    async def poll(self) -> AsyncIterator[mail.Thread]:
        """
        Polls the mail service for new threads, and generates each thread.

        :return: An asynchronous iterator of threads.
        :rtype: AsyncIterator[mail.Thread]
        """
        while True:
            print("polling for incoming emails...")
            thread = await self.email_controller.next_thread()
            if thread:
                yield thread
            else:
                await asyncio.sleep(self.interval)


class Enqueuer:
    """
    Enqueues incoming email threads to the message queue service.

    :param poller: The poller to use to get new threads.
    :type poller: Poller
    :param email_controller: The email controller to use to archive threads.
    :type email_controller: EmailController
    :param msgq_service: The message queue service to enqueue threads to.
    :type msgq_service: msgq.Service
    """

    def __init__(self, channel: Queue[None], poller: Poller, email_controller: EmailController, email_msgq_controller: EmailMsgqController) -> None:
        self.channel = channel
        self.email_msgq_controller = email_msgq_controller
        self.email_controller = email_controller
        self.poller = poller

    async def loop(self) -> None:
        """
        Loops forever, polling the mail service for new threads, and enqueuing
        them to the message queue service.  Archives each thread after
        enqueuing it.
        """
        async for thread in self.poller.poll():
            if not await self.email_msgq_controller.is_queued(thread):
                message = EmailMessage(
                    id=None,
                    status=EmailStatus.Arrived,
                    thread=thread,
                    completion=None,
                )
                await self.email_msgq_controller.push(message)

                # Signal the completion task.
                await self.channel.put(None)

            # Without archiving the thread, we will get the same thread again
            # the next time we poll.
            await self.email_controller.archive_thread(thread.id)


class EmailHandler:
    """
    Processes e-mails in the queue one by one.

    :param email_msgq_sync: The channel used to synchronize with the enqueuer.
    :type email_msgq_sync: Queue[None]
    :param email_msgq_controller: The message queue controller to use to
                                  process e-mails.
    :type email_msgq_controller: EmailMsgqController
    :param gpt_service: The GPT service to use to process e-mails.
    :type gpt_service: gpt.Service
    :param email_controller: The e-mail controller to use to send responses.
    :type email_controller: EmailController
    """

    def __init__(self, email_msgq_sync: Queue[None], email_msgq_controller: EmailMsgqController, gpt_service: GptService, email_controller: EmailController) -> None:
        self.email_msgq_sync = email_msgq_sync
        self.email_msgq_controller: EmailMsgqController = email_msgq_controller
        self.gpt_service = gpt_service
        self.email_controller = email_controller

    async def loop(self):
        while True:
            if message := await self.email_msgq_controller.get_current_or_next():
                if message.status == EmailStatus.Arrived:
                    try:
                        prepared_message = self.__prepare_for_completion(
                            message)
                    except Exception as e:
                        await self.__abandon(message, str(e))
                        raise
                    await self.__push(prepared_message)
                    await self.email_msgq_controller.archive(message)

                elif message.status == EmailStatus.Queued:
                    # Have QUEUED message submitted for completion.  The message
                    # status is kept up-to-date in the message queue.  In cases of
                    # restarts, the handler can pick up and carry on with the message.

                    if await self.__is_not_in_status(message, EmailStatus.Arrived):
                        # Sometimes there may be a duplicate in ARRIVED.  For example,
                        # a crash may leave a message in ARRIVED after it finds its
                        # way to QUEUED.  In any case, we must deal with the duplicate
                        # in ARRIVED before moving on to the message in QUEUED.
                        # Otherwise, a sneaky case may cause the message to be sent or
                        # completed more than once.  This may not have been critical,
                        # but very annoying nonetheless.  This was discovered and fixed
                        # in the TLA+ specification, Agent.tla.
                        try:
                            completion_message = await self.__gpt_complete(message)
                        except InvalidRequestError as e:
                            # The request was malformed or the maximum allowed number of
                            # tokens were exceeded.  This error is not transient.
                            await self.__abandon(message, str(e))
                            raise
                        except Exception as e:
                            await self.__fail(message, str(e))
                            raise
                        await self.__push(completion_message)
                        await self.email_msgq_controller.archive(message)

                    else:
                        # Process this message after archiving the duplicate in
                        # ARRIVED.
                        await self.__postpone(message)

                elif message.status == EmailStatus.Completed:
                    # Envelop COMPLETED messages in e-mails, sent and finally archived.

                    if await self.__is_not_in_status(message, EmailStatus.Queued):
                        # Sometimes there may be a duplicate in QUEUED.  For example,
                        # a crash may leave a message in QUEUED after it finds its
                        # way to COMPLETED.  In any case, we must deal with the duplicate
                        # in QUEUED before moving on to the message in COMPLETED.
                        # Otherwise, a sneaky case may cause the message to be sent more
                        # than once.  This may not have been critical, but very annoying
                        # nonetheless.  This was discovered and fixed in the TLA+
                        # specification, Agent.tla.
                        try:
                            response = self.__compose_response(message)
                        except Exception as e:
                            await self.__abandon(message, str(e))
                            raise

                        try:
                            await self.email_controller.reply(message.thread, response)
                        except Exception as e:
                            await self.__fail(message, str(e))
                            raise

                        await self.email_msgq_controller.archive(message)

                    else:
                        # Process this message after archiving the duplicate in
                        # QUEUED.
                        await self.__postpone(message)

                else:
                    raise ValueError(
                        f"unknown message status: {message.status}")
            else:
                # Wait for a new e-mail thread.
                await self.email_msgq_sync.get()

    def __compose_response(self, message: EmailMessage) -> str:
        if completion := message.completion:
            return completion.messages[-1].text
        else:
            raise ValueError("Message hasn't been completed yet.")

    async def __is_not_in_status(self, message: EmailMessage, status: EmailStatus) -> bool:
        thread_messages = await self.email_msgq_controller.find_by_thread_id(message.thread.id)
        return all(m.status != status for m in thread_messages)

    async def __postpone(self, message: EmailMessage) -> None:
        await self.__fail(message, 'attempt to push a message in the QUEUED status that is also in the ARRIVAL status')

    async def __gpt_complete(self, message: EmailMessage) -> EmailMessage:
        if request := message.completion:
            assert (len(request) >= 2)
            response = await self.gpt_service.complete(request)
        else:
            raise ValueError(
                "Message hasn't been prepared for completion yet.")

        return EmailMessage(
            id=None,
            status=EmailStatus.Completed,
            thread=message.thread,
            completion=response,
        )

    def __prepare_for_completion(self, message: EmailMessage) -> EmailMessage:
        thread = message.thread
        message_seq = GptMessageSeq()
        message_seq.append(gpt.SystemMessage("You are a helpful assistant."))
        for email in thread.messages:
            try:
                from_set = SetOfAddresses(email.headers['from'])
                to_set = SetOfAddresses(email.headers['to'])
                if AGENT_EMAIL_ADDRESS in from_set:
                    message_seq.append(gpt.AssistantMessage(email.body))
                elif AGENT_EMAIL_ADDRESS in to_set:
                    message_seq.append(gpt.UserMessage(email.body))
                else:
                    print(
                        f"skip email: [{email.body[:45]}...] in thread ID [{thread.id}]; reason: the agent's email address was not present as From or To addresses.", file=stderr)
            except KeyError:
                print(
                    f'expected from and to headers.  Message with problem: {email.body[:45]}', file=stderr)
                raise

        if len(message_seq) >= 2:
            return EmailMessage(
                id=None,
                status=EmailStatus.Queued,
                thread=thread,
                completion=message_seq,
            )
        else:
            raise RuntimeError(
                'email resulted in an incomplete completion request')

    async def __push(self, message: EmailMessage) -> None:
        try:
            await self.email_msgq_controller.push(message)
        except DatabaseConstraintException:
            # This would be a case of hash collision if the message
            # is already in the queue.  If it's not such a case, a
            # crash may have caused an old message to linger.
            # Someone needs to handle the hash collision case.  But
            # the latter is handled by the flow of logic.
            # TODO: check for a hash collision.
            pass

    async def __abandon(self, message: EmailMessage, reason: str) -> None:
        await self.email_msgq_controller.abandon(message, reason)

    async def __fail(self, message: EmailMessage, reason: str) -> None:
        if header := await self.email_msgq_controller.find(message):
            if header.num_attempts < 3:
                await self.email_msgq_controller.fail(message, reason)
            else:
                await self.email_msgq_controller.abandon(message, reason)
        else:
            raise ValueError(
                f"message with ID {message.id} not found in the queue")

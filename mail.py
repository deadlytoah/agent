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
from typing import AsyncIterator

from controller.msgq.email import EmailMsgqController
from proxy import mail


class Poller:
    """
    Polls the mail service for new threads.

    :param mail_service: The mail service to poll.
    :type mail_service: mail.Service
    :param interval: The interval to poll the mail service.
    :type interval: int
    """

    def __init__(self, mail_service: mail.Service, interval: int) -> None:
        self.mail_service = mail_service
        self.interval = interval

    async def poll(self) -> AsyncIterator[mail.Thread]:
        """
        Polls the mail service for new threads, and generates each thread.

        :return: An asynchronous iterator of threads.
        :rtype: AsyncIterator[mail.Thread]
        """
        while True:
            thread = await self.mail_service.next_thread()
            if thread:
                yield thread
            else:
                await asyncio.sleep(self.interval)


class Enqueuer:
    """
    Enqueues incoming email threads to the message queue service.

    :param poller: The poller to use to get new threads.
    :type poller: Poller
    :param mail_service: The mail service to use to archive threads.
    :type mail_service: mail.Service
    :param msgq_service: The message queue service to enqueue threads to.
    :type msgq_service: msgq.Service
    """

    def __init__(self, poller: Poller, mail_service: mail.Service, email_msgq_controller: EmailMsgqController) -> None:
        self.email_msgq_controller = email_msgq_controller
        self.mail_service = mail_service
        self.poller = poller

    async def loop(self) -> None:
        """
        Loops forever, polling the mail service for new threads, and enqueuing
        them to the message queue service.  Archives each thread after
        enqueuing it.
        """
        async for thread in self.poller.poll():
            if not await self.email_msgq_controller.is_queued(thread):
                await self.email_msgq_controller.push(thread)

            # Without archiving the thread, we will get the same thread again
            # the next time we poll.
            await self.mail_service.archive_thread(thread.id)

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

import json
from dataclasses import dataclass
from enum import Enum
from typing import Any, Optional

from proxy import mail, msgq
from proxy.gpt import GptMessageSeq
from proxy.mail import Thread
from proxy.msgq import Message, Status


class EmailStatus(Enum):
    Arrived = "ARRIVED",
    Completed = "COMPLETED",
    Queued = "QUEUED",


@dataclass
class EmailMessage:
    id: Optional[str]
    status: EmailStatus
    thread: Thread
    completion: Optional[GptMessageSeq]

    def to_dict(self) -> dict[str, Any]:
        return {
            'status': self.status.name,
            'thread': self.thread.to_dict(),
            'completion': self.completion.to_dict() if self.completion else None
        }

    @staticmethod
    def from_dict(data: dict[str, Any]) -> 'EmailMessage':
        return EmailMessage(
            id=data['id'],
            status=EmailStatus[data['status']],
            thread=Thread.from_dict(data['thread']),
            completion=GptMessageSeq.from_dict(
                data['completion']) if data['completion'] else None
        )


class EmailMsgqController:
    """
    Controls the message queue service for incoming emails.  The emails
    are queued for the GPT chat completion service.  Messages in the queue
    advance through each EmailStatus as they complete each stage of the
    process.

    :param msgq_service: The incoming email message queue service to control.
    :type msgq_service: msgq.Service
    """

    def __init__(self, msgq_service: msgq.Service):
        self.msgq_service = msgq_service

    async def find_by_id(self, thread_id: str) -> Optional[dict]:
        """
        Finds a thread in the message queue by thread ID.

        :param thread_id: The ID of the thread to find.
        :type thread_id: str
        :return: The email thread in the message queue with the given
                 thread ID.  Returns None if none found.
        :rtype: Optional[dict]
        :raises VerificationError: A message failed verification.
        """
        for message in await self.msgq_service.find_by_status([msgq.Status.PROCESSING, msgq.Status.QUEUED]):
            message.verify()
            payload: dict[str, Any] = json.loads(message.payload)
            if payload['thread_id'] == thread_id:
                return payload
        return None

    async def is_queued(self, thread: mail.Thread) -> bool:
        """
        Checks if a thread is queued in the message queue service.

        :param thread: The thread to check.
        :type thread: mail.Thread
        :return: True if the thread is queued, False otherwise.
        :rtype: bool
        """
        return await self.find_by_id(thread.id) is not None

    async def push(self, message: EmailMessage) -> None:
        """
        Pushes in the message queue an incoming thread of emails or a
        message that has advanced to the next stage.

        :param message: The message to push.
        :type message: Message
        :raise DatabaseConstraintException: The message already exists
                                            in the queue.
        """
        await self.msgq_service.push(json.dumps(message.to_dict()))

    async def get_current_or_next(self) -> Optional[EmailMessage]:
        """
        Gets the current message in the message queue service, or the next
        message if there is no current message.

        :return: The current message in the message queue service, or the
                 next message if there is no current message.  Returns None
                 if there is no current message and no next message.
        :rtype: Optional[Message]
        """
        if response := await self.msgq_service.process():
            id, payload = response
            return EmailMessage.from_dict(dict(id=id, **json.loads(payload)))
        else:
            return None

    async def archive(self, message: EmailMessage) -> None:
        """
        Archives the given message in the message queue.

        :param message: The message to archive.
        :type message: Message
        """
        if message.id:
            await self.msgq_service.archive(message.id)
        else:
            raise ValueError("Message has no ID.")

    async def find_by_status(self, status: list[Status]) -> list[EmailMessage]:
        """
        Finds all messages in the message queue that are in one of the
        given set of status.

        :param status: The set of status to look for.
        :type status: list[EmailStatus]
        :return: All messages in the message queue matching the given
                 set of status.
        :rtype: list[EmailMessage]
        :raises VerificationError: The message failed verification.
        """
        messages = await self.msgq_service.find_by_status(status)
        email_messages = []
        for message in messages:
            message.verify()
            email_message = EmailMessage.from_dict(
                dict(id=message.csid, **json.loads(message.payload)))
            email_messages.append(email_message)
        return email_messages

    async def find_by_thread_id(self, thread_id: str) -> list[EmailMessage]:
        """
        Finds all QUEUED or PROCESSING messages in the message queue with
        the given thread ID of the email thread.  Thread IDs uniquely identify
        an email thread in the queue and the remote email service.

        :param thread_id: The thread ID to look for.
        :type thread_id: str
        :return: All messages in the message queue with the given thread ID.
        :rtype: list[EmailMessage]
        :raises VerificationError: The message failed verification.
        """
        messages = await self.find_by_status([Status.PROCESSING, Status.QUEUED])
        return [m for m in messages if m.thread.id == thread_id]

    async def find(self, message: EmailMessage) -> Optional[Message]:
        if id := message.id:
            return await self.msgq_service.find(id)
        else:
            raise ValueError("Message has no ID.")

    async def fail(self, message: EmailMessage, reason: str) -> None:
        """
        Fails the given message in the message queue for the specified reason.
        Since the message must exist in the message queue, the message ID must
        not be None.

        :param message: The message to fail.
        :type message: Message
        :param reason: The reason for the failure.
        :type reason: str
        :raises ValueError: The message has no ID.
        """
        if id := message.id:
            await self.msgq_service.fail(id, reason)
        else:
            raise ValueError("Message has no ID.")

    async def abandon(self, message: EmailMessage, reason: str) -> None:
        """
        Abandons the given message in the message queue for the specified
        reason.  Since the message must exist in the message queue, the
        message ID must not be None.

        :param message: The message to abandon.
        :type message: Message
        :param reason: The reason for the abandonment.
        :type reason: str
        :raises ValueError: The message has no ID.
        """
        if id := message.id:
            await self.msgq_service.abandon(id, reason)
        else:
            raise ValueError("Message has no ID.")

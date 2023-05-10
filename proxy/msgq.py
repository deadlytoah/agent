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

import hashlib
import json
from dataclasses import dataclass
from datetime import datetime
from enum import Enum
from typing import Any, Optional

from pyservice import ServiceException, client


class MsgqErrorCode(Enum):
    """
    Represents the error codes for the message queue service.
    """
    DATABASE_CONSTRAINT = 'ERROR_DATABASE_CONSTRAINT'
    MSGQ_STATE = 'ERROR_MSGQ_STATE'


class DatabaseConstraintException(ServiceException):
    """
    Indicates a database constraint has been violated.

    :param inner: The inner exception.
    :type inner: Exception
    """

    def __init__(self, message: str):
        super(DatabaseConstraintException, self).__init__(
            MsgqErrorCode.DATABASE_CONSTRAINT, message)


class StateException(ServiceException):
    """
    Indicates the state of the queue is invalid.

    """

    def __init__(self, message: str):
        super(StateException, self).__init__(MsgqErrorCode.MSGQ_STATE, message)


class VerificationError(Exception):
    """
    Indicates a message failed verification.
    """

    def __init__(self, csid: str):
        super(VerificationError, self).__init__(
            f'Verification failed for message with ID {csid}')
        self.csid = csid


class Status(Enum):
    """
    Represents the status of a message in the queue.
    """
    QUEUED = 1
    PROCESSING = 2
    ARCHIVED = 3
    ABANDONED = 4
    CANCELLED = 5


@dataclass
class Message:
    """
    Represents a message in the queue.

    :param csid: The checksum ID of the message.
    :type csid: ChecksumID
    :param payload: The message payload.
    :type payload: bytes
    :param status: The status of the message.
    :type status: Status
    :param when_pushed: The date/time the message was pushed onto the queue.
    :type when_pushed: datetime
    :param when_deleted: The date/time the message was deleted from the queue.
    :type when_deleted: datetime
    :param when_delivered: The date/time the message was delivered.
    :type when_delivered: datetime
    :param when_error: The date/time the message encountered an error.
    :type when_error: datetime
    :param num_attempts: The number of times the message has been attempted.
    :type num_attempts: int
    :param last_error: The last error that occurred.
    :type last_error: str
    """

    csid: str
    payload: bytes
    status: Status
    when_pushed: datetime
    when_deleted: Optional[datetime]
    when_delivered: Optional[datetime]
    when_error: Optional[datetime]
    num_attempts: int
    last_error: Optional[str]

    @staticmethod
    def from_dictionary(dictionary: dict[str, Any]) -> 'Message':
        """
        Creates a message from a dictionary.

        :param dictionary: The dictionary to create the message from.
        :type dictionary: dict
        :return: The created message.
        :rtype: Message
        """
        return Message(
            csid=dictionary['csid'],
            payload=bytes.fromhex(dictionary['payload']),
            status=Status[dictionary['status']],
            when_pushed=datetime.fromisoformat(dictionary['when_pushed']),
            when_deleted=(datetime.fromisoformat(dictionary['when_deleted'])
                          if dictionary['when_deleted'] is not None else None),
            when_delivered=(datetime.fromisoformat(dictionary['when_delivered'])
                            if dictionary['when_delivered'] is not None else None),
            when_error=(datetime.fromisoformat(dictionary['when_error'])
                        if dictionary['when_error'] is not None else None),
            num_attempts=dictionary['num_attempts'],
            last_error=dictionary['last_error']
        )

    def verify(self) -> None:
        """
        Verifies the message.

        :return: None
        :rtype: None
        :raises VerificationError: The message failed verification.
        """
        if hashlib.sha512(self.payload, usedforsecurity=False).hexdigest() != self.csid:
            raise VerificationError(self.csid)


class Service:
    def __init__(self, endpoint: str) -> None:
        self.endpoint = endpoint

    async def push(self, payload: str) -> None:
        """
        Pushes a payload to the queue.

        :param payload: The payload to push to the queue.
        :type payload: str
        :return: None
        :rtype: None
        :raises DatabaseConstraintException: The given payload is already
                                             in the queue.
        """
        try:
            await client.call(self.endpoint, 'push', [payload])
        except ServiceException as e:
            if e.error_code == MsgqErrorCode.DATABASE_CONSTRAINT:
                raise DatabaseConstraintException(e.args[0]) from e
            else:
                raise

    async def process(self) -> Optional[tuple[str, str]]:
        """
        Processes the next message in the queue.

        :return: The message ID and payload.
        :rtype: Optional[(str, str)]]
        """
        response = await client.call(self.endpoint, 'process', [])
        assert len(response) == 0 or len(response) == 2, \
            f'expected 0 or 2 elements in response, got {len(response)}'
        if len(response) == 2:
            return (response[0], response[1])
        else:
            return None

    async def archive(self, message_id: str) -> None:
        """
        Archives the message with the given ID.  The message must be in the
        PROCESSING state.

        :param message_id: The ID of the message to archive.
        :type message_id: str
        :return: None
        :rtype: None
        :raises StateException: The message is not in the queue or not in
                                the PROCESSING status.
        """
        try:
            await client.call(self.endpoint, 'archive', [message_id])
        except ServiceException as e:
            if e.error_code == MsgqErrorCode.MSGQ_STATE:
                raise StateException(e.args[0]) from e
            else:
                raise

    async def fail(self, message_id: str) -> None:
        """
        Fails the message with the given ID.  The message must be in the
        PROCESSING state.

        :param message_id: The ID of the message to fail.
        :type message_id: str
        :return: None
        :rtype: None
        :raises StateException: The message is not in the queue or not in
                                the PROCESSING status.
        """
        try:
            await client.call(self.endpoint, 'fail', [message_id])
        except ServiceException as e:
            if e.error_code == MsgqErrorCode.MSGQ_STATE:
                raise StateException(e.args[0]) from e
            else:
                raise

    async def cancel(self, message_id: str) -> None:
        """
        Cancels the message with the given ID.  The message must be in the
        QUEUED state.

        :param message_id: The ID of the message to cancel.
        :type message_id: str
        :return: None
        :rtype: None
        :raises StateException: The message is not in the queue or not in
                                the QUEUED status.
        """
        try:
            await client.call(self.endpoint, 'cancel', [message_id])
        except ServiceException as e:
            if e.error_code == MsgqErrorCode.MSGQ_STATE:
                raise StateException(e.args[0]) from e
            else:
                raise

    async def abandon(self, message_id: str) -> None:
        """
        Abandons the message with the given ID.  The message must be in the
        PROCESSING state.

        :param message_id: The ID of the message to abandon.
        :type message_id: str
        :return: None
        :rtype: None
        :raises StateException: The message is not in the queue or not in
                                the PROCESSING status.
        """
        try:
            await client.call(self.endpoint, 'abandon', [message_id])
        except ServiceException as e:
            if e.error_code == MsgqErrorCode.MSGQ_STATE:
                raise StateException(e.args[0]) from e
            else:
                raise

    async def find_by_status(self, status: list[Status]) -> list[Message]:
        """
        Finds all messages with the given status.

        :param status: The status of the messages to find.
        :type status: [Status]
        :return: The messages with the given status.
        :rtype: list[Message]
        """
        response = await client.call(self.endpoint, 'find_by_status', [s.name for s in status])
        return [Message.from_dictionary(json.loads(message)) for message in response]

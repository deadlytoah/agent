from enum import Enum
from typing import Optional

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

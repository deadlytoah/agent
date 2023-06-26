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

from enum import Enum
import json
from typing import Any, Dict, List

from pyservice import client
from pyservice.client import ServiceException


class GptErrorCode(Enum):
    INVALID_REQUEST = "ERROR_INVALID_REQUEST"


class InvalidRequestException(ServiceException):
    def __init__(self, reason: str):
        super(ServiceException, self).__init__(
            GptErrorCode.INVALID_REQUEST, reason)


class Message:
    """
    Represents a message in the chat.

    Use the `build_message` function to create a message of the
    appropriate role.

    :param role: The role of the message, which can be one of "system", "user", or "assistant".
    :type role: str
    :param text: The text content of the message.
    :type text: str
    """

    def __init__(self, role: str, text: str):
        self.role = role
        self.text = text

    def to_dict(self) -> Dict[str, str]:
        """
        Converts the message to a dictionary containing the message
        role and text content.

        Returns:
            A dictionary containing the message role and text content.
        """
        return {"role": self.role, "content": self.text}

    @staticmethod
    def from_dict(data: Dict[str, str]) -> 'Message':
        """
        Converts the given dictionary to an instance of Message.

        :arg data: A dictionary representing a message.
        :type data: Dict[str, str]
        :return: A message.
        :rtype: Message
        """
        role = data['role']
        text = data['content']
        return Message(role=role, text=text)

    def to_json(self) -> str:
        """
        Converts the message to a JSON string.

        :return: A JSON string representation of the message.
        :rtype: str
        """
        return json.dumps(self.to_dict())

    @staticmethod
    def from_json(source: str) -> 'Message':
        """
        Converts a JSON string to a message.

        :arg json: A JSON string representation of the message.
        :type json: str
        :return: A message.
        :rtype: Message
        """
        return Message.from_dict(json.loads(source))


class SystemMessage(Message):
    """Represents a system message."""

    def __init__(self, text: str):
        super().__init__("system", text)


class UserMessage(Message):
    """Represents a user message."""

    def __init__(self, text: str):
        super().__init__("user", text)


class AssistantMessage(Message):
    """Represents an assistant message."""

    def __init__(self, text: str):
        super().__init__("assistant", text)


class GptMessageSeq:
    """
    Represents a sequence of messages for completion.

    :param messages: An optional sequence of messages.  If unspecified,
                     GptMessageSeq prepares an empty sequence.
    :type messages: List[Message]
    """

    def __init__(self: 'GptMessageSeq', messages: List[Message] = []):
        self.messages = messages

    def __len__(self) -> int:
        return self.messages.__len__()

    def append(self, message: Message):
        """
        Appends a message to the sequence.

        :param message: The message to append.
        :type message: Message
        """
        self.messages.append(message)

    def to_dict(self) -> Dict[str, Any]:
        """
        Converts the message sequence to a dictionary.

        Returns:
            A dictionary representation of the message sequence.
        """
        return {'messages': [message.to_dict() for message in self.messages]}

    @staticmethod
    def from_dict(dict: Dict[str, Any]) -> 'GptMessageSeq':
        """
        Converts a dictionary to an instance of GptMessageSeq.

        :arg dict: A dictionary representation of the message sequence.
        :type dict: Dict[str, Any]
        :return: A message sequence.
        :rtype: GptMessageSeq
        """
        return GptMessageSeq([Message.from_dict(message) for message in dict['messages']])

    def to_list(self) -> List[str]:
        """
        Converts the instance of GptMessageSeq to a list of messages.

        :return: A list representation of the message sequence.
        :rtype: List[str]
        """
        return [message.text for message in self.messages]

    @staticmethod
    def from_json_list(list: List[str]) -> 'GptMessageSeq':
        """
        Converts a list to an instance of GptMessageSeq.

        :arg list: A list representation of the message sequence.
        :type list: List[str]
        :return: A message sequence.
        :rtype: GptMessageSeq
        """
        return GptMessageSeq([Message.from_json(json) for json in list])


class GptService:
    """
    Acts as a proxy to the GPT service that interfaces with the OpenAI's
    GPT-3 chat completion API.

    :param endpoint: The endpoint of the GPT-3 API.
    :type endpoint: str
    """

    def __init__(self, endpoint: str):
        self.endpoint = endpoint

    async def complete(self, messages: GptMessageSeq) -> GptMessageSeq:
        """
        Sends a list of messages for a chat completion.

        :param messages: A list of messages to send.  This is a leading
                         system message followed by an alternating
                         sequence of user and assistant messages.
        :type messages: GptMessageSeq
        :return: A list of messages in the completion response.
        :rtype: GptMessageSeq
        :raises InvalidRequestError: The request was malformed or missing
                                     some required parameters, such as a
                                     token or an input.
        The request exceeded the maximum allowed number of tokens.
        """
        try:
            response = await client.call(self.endpoint, 'complete', messages.to_list())
        except ServiceException as e:
            if e.error_code == GptErrorCode.INVALID_REQUEST.value:
                raise InvalidRequestException(e.reason)
            else:
                raise
        role = response[1]
        content = response[2]
        messages.append(Message(role, content))
        return messages

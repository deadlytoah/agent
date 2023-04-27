import json
from typing import Dict, List

from pyservice import client


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

    def to_dictionary(self) -> Dict[str, str]:
        """
        Converts the message to a dictionary containing the message
        role and text content.

        Returns:
            A dictionary containing the message role and text content.
        """
        return {"role": self.role, "content": self.text}

    @staticmethod
    def from_dictionary(data: Dict[str, str]) -> 'Message':
        role = data['role']
        text = data['text']
        return Message(role=role, text=text)


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


class Service:
    def __init__(self, endpoint):
        self.endpoint = endpoint

    async def complete(self, messages: List[Message]) -> List[Message]:
        """
        Sends a list of messages to the GPT-3 API.

        Args:
            messages (List[Message]): A list of messages.

        Returns:
            List[Message]: A list of messages.

        Raises:
            GptException: If an error occurs while sending the
                          messages to the GPT-3 API.
        """
        messages_as_string = [json.dumps(
            message.to_dictionary()) for message in messages]
        response = await client.call(self.endpoint, 'complete', messages_as_string)
        return [Message.from_dictionary(json.loads(message)) for message in response]

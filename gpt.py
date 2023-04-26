import json
from typing import List

from pyservice import client
from pyservice.gpt import Message


class GptService:
    def __init__(self, endpoint):
        self.endpoint = endpoint

    def complete(self, messages: List[Message]) -> List[Message]:
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
        response = client.call(self.endpoint, 'complete', messages_as_string)
        return [Message.from_dictionary(json.loads(message)) for message in response]

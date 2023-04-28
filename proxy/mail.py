import json
from dataclasses import dataclass
from json import JSONDecodeError
from typing import Any, Dict, List, Optional

from pyservice import ProtocolException, client


class Headers(dict):
    @staticmethod
    def from_email_headers(headers: List[Dict[str, str]]) -> 'Headers':
        instance = Headers()
        for header in headers:
            instance[header["name"]] = header["value"]
        return instance

    @staticmethod
    def from_dictionary(headers: Dict[str, str]) -> 'Headers':
        instance = Headers()
        for key, value in headers.items():
            instance[key] = value
        return instance

    def __getitem__(self, key):
        return super().__getitem__(key.lower())

    def __setitem__(self, key, value):
        super().__setitem__(key.lower(), value)


@dataclass
class Message:
    headers: Headers
    body: str

    def to_dictionary(self) -> Dict[str, Any]:
        """
        Converts the message to a dictionary.

        :return: The dictionary representation of the message.
        :rtype: Dict[str, Any]
        """
        return {
            "headers": self.headers,
            "body": self.body
        }


@dataclass
class Thread:
    id: str
    messages: List[Message]

    def to_dictionary(self) -> Dict[str, Any]:
        """
        Converts the thread to a dictionary.

        :return: The dictionary representation of the thread.
        :rtype: Dict[str, Any]
        """
        messages = []
        for message in self.messages:
            messages.append(message.to_dictionary())
        return {
            "id": self.id,
            "messages": messages
        }


class Service:
    def __init__(self, endpoint: str, address_of_sender: str):
        self.endpoint = endpoint
        self.address_of_sender = address_of_sender

    async def next_thread(self) -> Optional[Thread]:
        """
        Gets the next thread from the Gmail account.

        Returns:
            Optional[Thread]: A thread containing a list of messages.
                              None if there are no more threads
                              available.

        Raises:
            GmailException: If an error occurs while fetching the next
                            thread from the Gmail API.
        """
        response = await client.call(self.endpoint, 'thread')
        if len(response) > 0:
            thread_id = response[0]
            thread_messages: List[str] = response[1:]
            pairs = [(thread_messages[i], thread_messages[i+1])
                     for i in range(0, len(thread_messages)-1, 2)]
            messages: List[Message] = []
            for pair in pairs:
                headers = pair[0]
                body = pair[1]
                try:
                    messages.append(
                        Message(headers=Headers.from_dictionary(json.loads(headers)), body=body))
                except JSONDecodeError:
                    raise ProtocolException(
                        f"couldn't parse headers: {headers}")
            return Thread(id=thread_id, messages=messages)
        else:
            return None

    async def reply(self, thread: Thread, body: str):
        """
        Replies to a thread with a message.

        Args:
            thread (Thread): The thread to reply to.
            body (str): The message body.

        Raises:
            GmailException: If an error occurs while replying to the
                            thread.
        """

        # Get the list of emails in the thread.
        last_message = thread.messages[-1]
        from_emails = [email.strip()
                       for email in last_message.headers['From'].split(',')]
        to_emails = [email.strip()
                     for email in last_message.headers['To'].split(',')]
        list_of_emails = list(set(from_emails + to_emails))
        list_of_emails.remove(self.address_of_sender)
        mailto = ', '.join(list_of_emails)

        # TODO: Unescape Unicode characters in the subject.
        # TODO: CC and BCC

        arguments = [
            thread.id,
            last_message.headers['Message-ID'],
            mailto,
            last_message.headers['Subject'],
            body,
        ]
        await client.call(self.endpoint, 'reply', arguments)

    async def archive_thread(self, thread_id: str):
        """
        Archives a thread.

        Args:
            thread_id (int): The ID of the thread to archive.

        Raises:
            GmailException: If an error occurs while archiving the
                            thread.
        """
        await client.call(self.endpoint, 'archive', [str(thread_id)])

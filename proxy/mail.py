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

from collections import UserDict
import json
from dataclasses import dataclass
from json import JSONDecodeError
from typing import Any, Dict, List, Optional

from pyservice import ProtocolException, client


class Headers(dict):
    def __init__(self, *args):
        super(Headers, self).__init__(*args)

    @staticmethod
    def from_email_headers(headers: List[Dict[str, str]]) -> 'Headers':
        instance = Headers()
        for header in headers:
            instance[header["name"].lower()] = header["value"]
        return instance

    @staticmethod
    def from_dictionary(headers: Dict[str, str]) -> 'Headers':
        instance = Headers()
        for key, value in headers.items():
            instance[key.lower()] = value
        return instance


@dataclass
class Message:
    headers: Headers
    body: str

    def to_dict(self) -> Dict[str, Any]:
        """
        Converts the message to a dictionary.

        :return: The dictionary representation of the message.
        :rtype: Dict[str, Any]
        """
        return {
            "headers": self.headers,
            "body": self.body
        }

    @staticmethod
    def from_dict(dict: Dict[str, Any]) -> 'Message':
        """
        Creates a message from the given dictionary.

        :param dict: The dictionary to create the message from.
        :type dict: Dict[str, Any]
        :return: The message created from the dictionary.
        :rtype: Message
        """
        return Message(headers=dict['headers'], body=dict['body'])


@ dataclass
class Thread:
    id: str
    messages: List[Message]

    def to_dict(self) -> Dict[str, Any]:
        """
        Converts the thread to a dictionary.

        :return: The dictionary representation of the thread.
        :rtype: Dict[str, Any]
        """
        messages = []
        for message in self.messages:
            messages.append(message.to_dict())
        return {
            "id": self.id,
            "messages": messages
        }

    @ staticmethod
    def from_dict(dict: Dict[str, Any]) -> 'Thread':
        """
        Creates the thread from a dictionary.

        :param dict: The dictionary to create the thread from.
        :type dict: Dict[str, Any]
        :return: The thread created from the dictionary.
        """
        thread = Thread(dict['id'], [])
        for message_dict in dict['messages']:
            thread.messages.append(Message.from_dict(message_dict))
        return thread


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
                       for email in last_message.headers['from'].split(',')]
        to_emails = [email.strip()
                     for email in last_message.headers['to'].split(',')]
        list_of_emails = list(set(from_emails + to_emails))
        list_of_emails.remove(self.address_of_sender)
        mailto = ', '.join(list_of_emails)

        # TODO: Unescape Unicode characters in the subject.
        # TODO: CC and BCC

        arguments = [
            thread.id,
            last_message.headers['message-id'],
            mailto,
            last_message.headers['subject'],
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

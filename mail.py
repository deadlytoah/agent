import json
from json import JSONDecodeError
from typing import List, Optional

from pyservice import ProtocolException, client
from pyservice.email import Headers, Message, Thread


class MailService:
    def __init__(self, endpoint: str, address_of_sender: str):
        self.endpoint = endpoint
        self.address_of_sender = address_of_sender

    def next_thread(self) -> Optional[Thread]:
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
        response = client.call(self.endpoint, 'thread')
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

    def reply(self, thread: Thread, body: str):
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
        client.call(self.endpoint, 'reply', arguments)

    def archive_thread(self, thread_id: str):
        """
        Archives a thread.

        Args:
            thread_id (int): The ID of the thread to archive.

        Raises:
            GmailException: If an error occurs while archiving the
                            thread.
        """
        client.call(self.endpoint, 'archive', [str(thread_id)])

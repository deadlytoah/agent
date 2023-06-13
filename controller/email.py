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

import re
from typing import Optional

from proxy.mail import Service, Thread


class SetOfAddresses(set):
    """
    Parses the specified content of an addresses field in the email header
    and produces a set of email addresses.  If an address contains the name
    of sender or recipient, the name is stripped off, and only the email
    address is kept.

    :param server_address: A string representing a list of email addresses
                           joined by a comma.
    :type server_address: str
    """
    def __init__(self, server_address: str) -> None:
        super(SetOfAddresses, self).__init__()
        for addr_string in server_address.split(','):
            if match := re.match('[^<>]*<([^<>]*)>', addr_string):
                self.add(match[1])
            else:
                self.add(addr_string)


class EmailController:
    """
    Controls the email service for the app.

    :param email_service: The email service.
    :type email_service: Service
    """

    def __init__(self, email_service: Service):
        self.email_service = email_service

    async def next_thread(self) -> Optional[Thread]:
        """
        Gets the next thread from the Gmail account.

        :return: A thread containing a list of messages. None if there
                 are no more threads available.
        :rtype: Optional[Thread]
        :raises GmailException: If an error occurs while fetching the
                                next thread from the Gmail API.
        """
        return await self.email_service.next_thread()

    async def archive_thread(self, thread_id: str) -> None:
        """
        Archives a thread.

        :param thread_id: The ID of the thread to archive.
        :type thread_id: str
        :raises GmailException: If an error occurs while archiving the
                                thread.
        """
        return await self.email_service.archive_thread(thread_id)

    async def reply(self, thread: Thread, body: str) -> None:
        """
        Replies to the given thread with the specified message body.

        :param thread: The thread to reply to.
        :type thread: Thread
        :param body: The message body.
        :type body: str
        """
        await self.email_service.reply(thread, body)

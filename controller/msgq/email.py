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
from typing import Optional

from proxy import mail, msgq
from proxy.msgq import Status


class EmailMsgqController:
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
        for message in await self.msgq_service.find_by_status([Status.PROCESSING, Status.QUEUED]):
            message.verify()
            payload = json.loads(message.payload)
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

    async def push(self, thread: mail.Thread) -> None:
        """
        Pushes a thread to the message queue service.

        :param thread: The thread to push.
        :type thread: mail.Thread
        """
        message = {
            'status': 'ARRIVED',
            'thread_id': thread.id,
            'payload': thread.to_dictionary(),
        }
        await self.msgq_service.push(json.dumps(message))

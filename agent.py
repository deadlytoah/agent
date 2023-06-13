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

import asyncio
from asyncio import Queue

import mail
from configuration import Configuration
from controller.email import EmailController
from controller.msgq import EmailMsgqController
from mail import AGENT_EMAIL_ADDRESS, EmailHandler
from proxy import mail as mail_proxy
from proxy import msgq
from proxy.gpt import GptService

# The maximum size of channel before an equeue operation blocks.
MAXIMUM_CHANNEL_SIZE = 128


def __create_email_controller() -> EmailController:
    mail_service = mail_proxy.Service(
        configuration['email_service_endpoint'], AGENT_EMAIL_ADDRESS)
    return EmailController(mail_service)


async def main(configuration: Configuration) -> None:
    mail_msgq_service = msgq.Service(
        configuration['email_queue_service_endpoint'])
    gpt_service = GptService(configuration['gpt_service_endpoint'])

    email_msgq_sync: Queue[None] = Queue(MAXIMUM_CHANNEL_SIZE)

    email_polling_interval: int = configuration['email_polling_interval']
    email_poller = mail.Poller(
        __create_email_controller(), interval=email_polling_interval)
    email_msgq_controller = EmailMsgqController(mail_msgq_service)
    email_enqueuer = mail.Enqueuer(
        email_msgq_sync, email_poller, __create_email_controller(), email_msgq_controller)
    email_handler = EmailHandler(email_msgq_sync, email_msgq_controller,
                                 gpt_service, __create_email_controller())

    async with asyncio.TaskGroup() as task_group:
        task_group.create_task(email_enqueuer.loop())
        task_group.create_task(email_handler.loop())


if __name__ == '__main__':
    configuration = Configuration.read('agent.json')
    configuration.validate()
    asyncio.run(main(configuration))

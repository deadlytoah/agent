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

import mail
from configuration import Configuration
from controller.msgq.email import EmailMsgqController
from proxy import gpt
from proxy import mail as mail_proxy
from proxy import msgq

AGENT_EMAIL_ADDRESS = 'thevoicekorea+chat@gmail.com'


async def main(configuration: Configuration) -> None:
    mail_service = mail_proxy.Service(
        configuration['email_service_endpoint'], AGENT_EMAIL_ADDRESS)
    mail_msgq_service = msgq.Service(
        configuration['email_queue_service_endpoint'])
    gpt_service = gpt.Service(configuration['gpt_service_endpoint'])
    gpt_msgq_service = msgq.Service(
        configuration['gpt_queue_service_endpoint'])

    email_polling_interval = configuration['email_polling_interval']
    email_poller = mail.Poller(mail_service, interval=email_polling_interval)
    email_enqueuer = mail.Enqueuer(
        email_poller, mail_service, EmailMsgqController(mail_msgq_service))

    async with asyncio.TaskGroup() as task_group:
        task_group.create_task(email_enqueuer.loop())


if __name__ == '__main__':
    configuration = Configuration.read('agent.json')
    configuration.validate()
    asyncio.run(main(configuration))

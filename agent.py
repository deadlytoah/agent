import asyncio
from sys import stderr
from typing import List

import mail
from configuration import Configuration
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
        email_poller, mail_service, mail_msgq_service)

    async with asyncio.TaskGroup() as task_group:
        task_group.create_task(email_enqueuer.loop())


if __name__ == '__main__':
    configuration = Configuration.read('agent.json')
    configuration.validate()
    asyncio.run(main(configuration))

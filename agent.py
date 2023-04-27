import asyncio
from sys import stderr
from typing import List

from configuration import Configuration
from proxy import gpt, mail, msgq

AGENT_EMAIL_ADDRESS = 'thevoicekorea+chat@gmail.com'


async def main(configuration: Configuration) -> None:
    mail_service = mail.Service(
        configuration['email_service_endpoint'], AGENT_EMAIL_ADDRESS)
    mail_msgq_service = msgq.Service(
        configuration['email_queue_service_endpoint'])
    gpt_service = gpt.Service(configuration['gpt_service_endpoint'])
    gpt_msgq_service = msgq.Service(
        configuration['gpt_queue_service_endpoint'])
    thread = await mail_service.next_thread()
    if thread:
        gpt_messages: List[gpt.Message] = [
            gpt.SystemMessage("You are a helpful assistant.")]
        for message in thread.messages:
            try:
                if message.headers['From'] == AGENT_EMAIL_ADDRESS:
                    # assistant message
                    gpt_messages.append(
                        gpt.AssistantMessage(message.get_body_str()))
                elif message.headers['To'] == AGENT_EMAIL_ADDRESS:
                    # user message
                    gpt_messages.append(
                        gpt.UserMessage(message.get_body_str()))
                else:
                    pass
            except KeyError:
                print(
                    f'expected from and to headers.  Message with problem: {message}', file=stderr)
                raise
        response = await gpt_service.complete(gpt_messages)
        await mail_service.reply(thread, response[0].text)
        await mail_service.archive_thread(thread.id)
    else:
        print('No more e-mail threads.', file=stderr)


if __name__ == '__main__':
    try:
        configuration = Configuration.read('agent.json')
    except Exception:
        print('Configuration file [agent.json] missing.', file=stderr)
        exit(1)
    asyncio.run(main(configuration))

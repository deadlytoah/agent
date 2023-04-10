from os import environ
from sys import stderr
from typing import Dict, List

from pyservice import gpt

from gpt import GptService
from mail import MailService

AGENT_EMAIL_ADDRESS = 'thevoicekorea+chat@gmail.com'


def main(endpoints: Dict[str, str]) -> None:
    mail_service = MailService(endpoints['email'], AGENT_EMAIL_ADDRESS)
    gpt_service = GptService(endpoints['gpt'])
    thread = mail_service.next_thread()
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
        response = gpt_service.send(gpt_messages)
        mail_service.reply(thread, response[0].text)
        mail_service.archive_thread(thread.id)
    else:
        print('No more e-mail threads.', file=stderr)


if __name__ == '__main__':
    endpoints = {
        'email': environ['EMAIL_SERVICE_ENDPOINT'],
        'gpt': environ['GPT_SERVICE_ENDPOINT'],
    }
    main(endpoints)

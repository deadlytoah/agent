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
from typing import Dict


class Configuration(dict):
    """
    Configuration for the agent.
    """

    __REQUIRED_KEYS__ = [
        'email_service_endpoint',
        'email_queue_service_endpoint',
        'gpt_service_endpoint',
        'gpt_queue_service_endpoint',
        'email_polling_interval'
    ]

    def __init__(self) -> None:
        super(Configuration, self).__init__()

    def validate(self) -> None:
        """
        Validates the configuration.

        :return: None
        :rtype: None
        :raises ValueError: If the configuration is invalid.
        """
        for key in self.__REQUIRED_KEYS__:
            if key not in self:
                raise ValueError(f'{key} is required')

    @staticmethod
    def read(filename: str) -> 'Configuration':
        """
        Reads the configuration from a JSON file.

        :param filename: The name of the file to read.
        :type filename: str
        :return: The configuration.
        :rtype: Configuration
        :raises FileNotFoundError: If the file is not found.
        :raises json.JSONDecodeError: If the file is not valid JSON.
        """
        with open(filename) as f:
            instance = Configuration()
            instance.update(json.load(f))
            return instance

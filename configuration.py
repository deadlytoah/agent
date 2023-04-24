import json
from typing import Dict


class Configuration(dict):
    """
    Configuration for the agent.
    """

    def __init__(self) -> None:
        super(Configuration, self).__init__()

    @staticmethod
    def read(filename: str) -> 'Configuration':
        """
        Reads the configuration from a JSON file.

        :param filename: The name of the file to read.
        :type filename: str
        :return: The configuration.
        :rtype: Configuration
        """
        with open(filename) as f:
            instance = Configuration()
            instance.update(json.load(f))
            return instance

"""Logs data created during program runtime."""

import os
from pasypy import variables


class Logger:
    """Logs data created during program runtime."""

    def __init__(self):
        pass

    @staticmethod
    def _create_logfile(name, area):
        """Creates a logfile by name and area.

        :param name: The name of the logfile.
        :param area: The area used to write into the logfile.
        """
        logfile = open('logs/{}.log'.format(name), 'w')
        for variable in variables.parameters:
            logfile.write('----- {} -----'.format(str(variable)))
        logfile.write('\n')
        for sub_area in area:
            logfile.write(str(sub_area) + '\n')
        logfile.close()

    def create_logfiles(self):
        """Creates logfiles for both safe and unsafe area."""
        self._create_logfile('safe_area', variables.safe_area)
        self._create_logfile('unsafe_area', variables.unsafe_area)

    @staticmethod
    def _show_area(name):
        """Opens the logfile by name.

        :param name: The name of the logfile. Either 'safe_area' or 'unsafe_area'.
        """
        file_path = os.getcwd() + '/logs/{}.log'.format(name)
        if os.path.exists(file_path) and (os.path.getsize(file_path) > 0):
            os.startfile(file_path)

    def show_safe_area(self):
        """Opens the logfile containing all safe areas."""
        self._show_area('safe_area')

    def show_unsafe_area(self):
        """Opens the logfile containing all unsafe areas."""
        self._show_area('unsafe_area')

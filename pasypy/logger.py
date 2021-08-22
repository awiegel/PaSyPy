import os
from pasypy import variables


class Logger:
    def __init__(self):
        pass

    def _create_logfile(self, name, area):
        logfile = open('logs/{}.log'.format(name), 'w')
        for variable in variables.parameters:
            logfile.write('----- {} -----'.format(str(variable)))
        logfile.write('\n')
        for sub_area in area:
            logfile.write(str(sub_area) + '\n')
        logfile.close()

    def create_logfiles(self):
        self._create_logfile('safe_area', variables.safe_area)
        self._create_logfile('unsafe_area', variables.unsafe_area)

    def _show_area(self, name):
        file_path = os.getcwd() + '/logs/{}.log'.format(name)
        if os.path.exists(file_path) and (os.path.getsize(file_path) > 0):
            os.startfile(file_path)

    def show_safe_area(self):
        self._show_area('safe_area')

    def show_unsafe_area(self):
        self._show_area('unsafe_area')

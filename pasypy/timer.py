import timeit


class Timer:
    def __init__(self):
        self.timestamps = {
            'Computation'  : 0,
            'Visualization': 0
        }

    def _clear_timestamp(self, key):
        self.timestamps[key] = 0

    def create_timestamp(self, key):
        self._clear_timestamp(key)
        self.timestamps[key] = timeit.default_timer()

    def calculate_time(self, key):
        self.timestamps[key] = timeit.default_timer() - self.timestamps[key]

    def get_time(self, key):
        return self.timestamps[key]

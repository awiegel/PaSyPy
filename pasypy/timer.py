"""Tracks the time."""

import timeit


class Timer:
    """Tracks the time."""

    def __init__(self):
        """Creates a dictionary with keys."""
        self.timestamps = {
            'Computation'  : 0,
            'Visualization': 0
        }

    def _clear_timestamp(self, key):
        """Deletes previous values for this timestamp.

        :param key: The selected timestamp.
        """
        self.timestamps[key] = 0

    def create_timestamp(self, key):
        """Creates a timestamp for a given key.
        Deletes previous values for this timestamp.

        :param key: The selected timestamp.
        """
        self._clear_timestamp(key)
        self.timestamps[key] = timeit.default_timer()

    def calculate_time(self, key):
        """Calculates the time for a given key with previous created timestamps.

        :param key: The selected timestamp.
        """
        self.timestamps[key] = timeit.default_timer() - self.timestamps[key]

    def get_time(self, key):
        """Gets the calculated time for a given key.

        :param key: The selected timestamp.
        :return: The calculated time of the selected timestamp.
        """
        return self.timestamps[key]

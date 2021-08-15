import timeit

timestamps = {
    'Computation'  : 0,
    'Visualization': 0
}


def create_timestamp(key):
    _clear_timestamp(key)
    timestamps[key] = timeit.default_timer()


def calculate_time(key):
    timestamps[key] = timeit.default_timer() - timestamps[key]


def get_time(key):
    return timestamps[key]


def _clear_timestamp(key):
    timestamps[key] = 0

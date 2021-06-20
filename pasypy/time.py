import timeit

timestamps = []
total_time = 0


def create_timestamp():
    timestamp = timeit.default_timer()
    for i in timestamps:
        timestamp -= i
    timestamps.append(timestamp)


def calculate_time():
    global total_time
    total_time = 0
    for timestamp in timestamps[1:]:
        total_time += timestamp
    _clear_timestamps()


def _clear_timestamps():
    global timestamps
    timestamps = []

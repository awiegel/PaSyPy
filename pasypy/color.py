"""Contains the used colors reflecting safe and unsafe area."""

from enum import Enum


class Color(Enum):
    """Contains the used colors reflecting safe and unsafe area."""

    def __init__(self, value):
        pass

    GREEN = 'forestgreen'
    RED = 'firebrick'
    BLUE = 'dodgerblue'
    YELLOW = 'goldenrod'

safe_color = Color.GREEN.value # pylint: disable=C0103 # is not a constant
unsafe_color = Color.RED.value # pylint: disable=C0103 # is not a constant

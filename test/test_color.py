"""Tests the color module."""

import unittest

from pasypy.color import Color


class TestColor(unittest.TestCase):
    """Tests the color module."""

    @classmethod
    def setUpClass(cls):
        cls.color = Color('forestgreen')

    def test_valid_color(self):
        """Checks all available colors."""
        self.assertEqual('forestgreen', self.color.GREEN.value)
        self.assertEqual('firebrick', self.color.RED.value)
        self.assertEqual('dodgerblue', self.color.BLUE.value)
        self.assertEqual('goldenrod', self.color.YELLOW.value)

    def test_invalid_color(self):
        """Checks if invalid colors are rejected."""
        with self.assertRaises(ValueError):
            Color('maroon')

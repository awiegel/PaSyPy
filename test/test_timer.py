"""Tests the timer module."""

import unittest
import time

# from pasypy import formula_parser, variables
from pasypy.timer import Timer


class TestTimer(unittest.TestCase):
    """Tests the timer module."""

    @classmethod
    def setUpClass(cls):
        cls.timer = Timer()

    def test_timer(self):
        """Checks if calculation of time is correct and precisely."""
        self.assertEqual(0, self.timer.get_time('Computation'))
        self.timer.create_timestamp('Computation')
        time.sleep(0.02)
        self.timer.calculate_time('Computation')
        self.assertAlmostEqual(0.02, self.timer.get_time('Computation'), places=2)

        self.assertEqual(0, self.timer.get_time('Visualization'))
        self.timer.create_timestamp('Visualization')
        time.sleep(0.01)
        self.timer.calculate_time('Visualization')
        self.assertAlmostEqual(0.01, self.timer.get_time('Visualization'), places=2)

    def test_invalid_key(self):
        """Checks if invalid keys are rejected."""
        with self.assertRaises(KeyError):
            self.assertEqual(0, self.timer.get_time('Invalid Key'))
            self.timer.create_timestamp('Invalid Key')
            time.sleep(0.01)
            self.timer.calculate_time('Invalid Key')
            self.assertAlmostEqual(0.01, self.timer.get_time('Invalid Key'), places=2)

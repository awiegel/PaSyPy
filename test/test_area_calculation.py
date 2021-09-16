"""Tests the area_calculation module."""

import unittest
import z3

from pasypy import variables
from pasypy.area_calculation import AreaCalculation


class TestAreaCalculation(unittest.TestCase):
    """Tests the area_calculation module."""

    @classmethod
    def setUpClass(cls):
        variables.parameters = [z3.Real('x'), z3.Real('y')]
        variables.interval_limit = [variables.DEFAULT_LIMIT.copy(), variables.DEFAULT_LIMIT.copy()]

    def test_calculate_area(self):
        """Checks if calculation of given area is correct."""
        safe_area = [([0.0,0.25], [0.0,0.25]),
                     ([0.25,0.5], [0.0,0.25]),
                     ([0.0,0.25], [0.25,0.5]),
                     ([0.25,0.5], [0.25,0.5])]
        total_safe_area = AreaCalculation().calculate_area(safe_area)
        self.assertEqual(0.25, total_safe_area)

        unsafe_area = [([0.5,0.75], [0.5,0.75]),
                       ([0.75,1.0], [0.75,1.0])]
        total_unsafe_area = AreaCalculation().calculate_area(unsafe_area)
        self.assertEqual(0.125, total_unsafe_area)

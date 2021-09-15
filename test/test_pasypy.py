"""Tests the pasypy module."""

import unittest
import z3

from pasypy import variables
from pasypy.pasypy import PaSyPy


class TestPaSyPy(unittest.TestCase):
    """Tests the pasypy module."""

    @classmethod
    def setUpClass(cls):
        x = z3.Real('x') # pylint: disable=C0103 # parameter name is conform
        y = z3.Real('y') # pylint: disable=C0103 # parameter name is conform
        z = z3.Real('z') # pylint: disable=C0103 # parameter name is conform
        variables.formula = z3.Exists(z, z3.And(x >= 1/2, y >= 1/2, x > z, z > y))
        variables.parameters = [x,y]
        cls.pasypy = PaSyPy()

    def test_empty_queue(self):
        """Checks if empty queue is rejected."""
        variables.queue = []
        with self.assertRaises(IndexError):
            self.pasypy.solveit(([0.0, 1.0], [0.0, 1.0], 1))

    def test_correctly_assigned_regions(self):
        """Checks if found safe and unsafe regions are correctly assigned."""
        variables.queue = [([0.0, 1.0], [0.0, 1.0], 1)]
        for _ in range(100):
            self.pasypy.solveit(variables.queue[0])

        for safe_area in variables.safe_area:
            self.assertTrue((safe_area[0][0] >= 1/2) and (safe_area[1][0] >= 1/2) and (safe_area[0][0] > safe_area[1][0]))
        for unsafe_area in variables.unsafe_area:
            self.assertTrue((unsafe_area[0][0] < 1/2) or (unsafe_area[1][0] < 1/2) or (unsafe_area[0][0] <= unsafe_area[1][0]))

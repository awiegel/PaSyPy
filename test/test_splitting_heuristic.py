"""Tests the splitting_heuristic module."""

import unittest
import z3

from pasypy import variables, splitting_heuristic
from pasypy.splitting_heuristic import SplittingHeuristic
from pasypy.area_calculation import AreaCalculation


class TestSplittingHeuristic(unittest.TestCase):
    """Tests the splitting_heuristic module."""

    @classmethod
    def setUpClass(cls):
        x = z3.Real('x') # pylint: disable=C0103 # parameter name is conform
        y = z3.Real('y') # pylint: disable=C0103 # parameter name is conform
        variables.parameters = [x,y]
        variables.interval_limit = [variables.DEFAULT_LIMIT.copy(), variables.DEFAULT_LIMIT.copy()]
        cls.splitting_heuristic = SplittingHeuristic()

    def test_default_heuristic(self):
        """Checks if default heuristic operates correctly."""
        number_of_new_regions = 3 # 2**len(variables.parameters)
        variables.queue = [([0.0, 1.0], [0.0, 1.0], 1)]
        current_number_of_regions = 0
        for _ in range(1000):
            self.splitting_heuristic.apply_heuristic(variables.queue[0])
            variables.queue.pop(0)
            current_number_of_regions += number_of_new_regions
            self.assertEqual(1.0, AreaCalculation.calculate_area(variables.queue))
            self.assertEqual(current_number_of_regions+1, len(variables.queue))

    def test_simple_heuristic(self):
        """Checks if simple heuristic operates correctly."""
        splitting_heuristic.current_splitting_heuristic = 'Simple'
        number_of_new_regions = 1 # 2**len(variables.parameters)
        variables.queue = [([0.0, 1.0], [0.0, 1.0], 1)]
        current_number_of_regions = 0
        for _ in range(1000):
            self.splitting_heuristic.apply_heuristic(variables.queue[0])
            variables.queue.pop(0)
            current_number_of_regions += number_of_new_regions
            self.assertEqual(1.0, AreaCalculation.calculate_area(variables.queue))
            self.assertEqual(current_number_of_regions+1, len(variables.queue))

    def test_extended_heuristic(self):
        """Checks if extended heuristic operates correctly."""
        splitting_heuristic.current_splitting_heuristic = 'Extended'
        variables.queue = [([0.0, 1.0], [0.0, 1.0], 1)]

    def test_random_heuristic(self):
        """Checks if random heuristic operates correctly."""
        splitting_heuristic.current_splitting_heuristic = 'Random'
        number_of_new_regions = 3 # 2**len(variables.parameters)
        variables.queue = [([0.0, 1.0], [0.0, 1.0], 1)]
        current_number_of_regions = 0
        for _ in range(1000):
            self.splitting_heuristic.apply_heuristic(variables.queue[0])
            variables.queue.pop(0)
            current_number_of_regions += number_of_new_regions
            self.assertAlmostEqual(1.0, AreaCalculation.calculate_area(variables.queue))
            self.assertEqual(current_number_of_regions+1, len(variables.queue))

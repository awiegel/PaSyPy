"""Tests the sampling module."""

import unittest
import z3

from pasypy import variables
from pasypy.sampling import PreSampling

class TestPreSampling(unittest.TestCase):
    """Tests the PreSampling class."""

    @classmethod
    def setUpClass(cls):
        cls.x = z3.Real('x') # pylint: disable=C0103 # parameter name is conform
        cls.y = z3.Real('y') # pylint: disable=C0103 # parameter name is conform
        variables.parameters = [cls.x,cls.y]
        cls.formula = z3.And(cls.x >= 1/2, cls.y >= 1/4, cls.x >= cls.y)
        cls.pre_sampling = PreSampling()

    def setUp(self):
        self.pre_sampling.candidates = []

    def test_empty_queue(self):
        """Checks if empty queue is rejected."""
        variables.queue = []
        self.pre_sampling.get_pre_sampling_candidate(self.formula.children()[0])
        self.assertEqual([self.x >= 1/2], self.pre_sampling.candidates)
        self.pre_sampling.get_pre_sampling_candidate(self.formula.children()[1])
        self.assertEqual([self.x >= 1/2, self.y >= 1/4], self.pre_sampling.candidates)
        self.pre_sampling.pre_sampling()
        self.assertFalse(variables.queue)

    def test_empty_candidates(self):
        """Checks if empty candidates are rejected."""
        variables.queue = [([0.0, 1.0], [0.0, 1.0], 1)]
        self.pre_sampling.pre_sampling()
        self.assertEqual([([0.0, 1.0], [0.0, 1.0], 1)], variables.queue)

    def test_get_pre_sampling_candidate(self):
        """Tests the PreSampling class."""
        variables.queue = [([0.0, 1.0], [0.0, 1.0], 1)]
        self.pre_sampling.get_pre_sampling_candidate(self.formula.children()[0])
        self.assertEqual([self.x >= 1/2], self.pre_sampling.candidates)
        self.pre_sampling.get_pre_sampling_candidate(self.formula.children()[1])
        self.assertEqual([self.x >= 1/2, self.y >= 1/4], self.pre_sampling.candidates)
        self.pre_sampling.pre_sampling()
        # factor for the gap is 0.0001
        expected_regions = [([0.0, 0.4999], [0.0, 0.2499], 4),
                            ([0.0, 0.4999], [0.25, 1.0], 4),
                            ([0.5, 1.0], [0.0, 0.2499], 4),
                            ([0.5, 1.0], [0.25, 1.0], 4),
                            ([0.4999, 0.5], [0.0, 1.0], 4),
                            ([0.0, 0.4999], [0.2499, 0.25], 4),
                            ([0.5, 1.0], [0.2499, 0.25], 4)]
        self.assertEqual(expected_regions, variables.queue)

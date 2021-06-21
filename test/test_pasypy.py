import unittest

import z3
from pasypy import pasypy, variables


class TestPasypy(unittest.TestCase):

    def test_empty_queue(self):
        
        x = z3.Real('x')
        y = z3.Real('y')
        z = z3.Real('z')
        variables.Constraints = z3.Exists(z, z3.And(x >= 1/2, y >= 1/2, z > x, z < y))
        variables.Constraints_neg = z3.Not(variables.Constraints)
        variables.parameters = [x,y]

        pasypy.main()
        
        self.assertEqual(variables.G, [])
        self.assertEqual(variables.R, [])


    def test_queue_with_area_calculation(self):
        
        x = z3.Real('x')
        y = z3.Real('y')
        z = z3.Real('z')
        variables.Constraints = z3.Exists(z, z3.And(x >= 1/2, y >= 1/2, y < z, z < x))
        variables.Constraints_neg = z3.Not(variables.Constraints)
        variables.parameters = [x,y]

        variables.Queue = [([0.0, 1.0], [0.0, 1.0], 1)]

        pasypy.main()
        
        for g in variables.G:
            self.assertTrue((g[0][0] >= 1/2) and (g[1][0] >= 1/2) and (g[0][0] > g[1][0]))
        
        for r in variables.R:
            self.assertTrue((r[0][0] < 1/2) or (r[1][0] < 1/2) or (r[0][0] <= r[1][0]))
        
        self.assertEqual(pasypy.calculate_area(variables.G), 0.046875)
        self.assertEqual(pasypy.calculate_area(variables.R), 0.78125)

import unittest

import z3
from pasypy import pasypy, variables


class TestPasypy(unittest.TestCase):

    def test_empty_queue(self):
        
        x = z3.Real('x')
        y = z3.Real('y')
        z = z3.Real('z')
        variables.constraints = z3.Exists(z, z3.And(x >= 1/2, y >= 1/2, z > x, z < y))
        variables.parameters = [x,y]

        pasypy.main()
        
        self.assertEqual(variables.safe_area, [])
        self.assertEqual(variables.unsafe_area, [])


    def test_queue_with_area_calculation(self):
        
        x = z3.Real('x')
        y = z3.Real('y')
        z = z3.Real('z')
        variables.constraints = z3.Exists(z, z3.And(x >= 1/2, y >= 1/2, y < z, z < x))
        variables.parameters = [x,y]

        variables.queue = [([0.0, 1.0], [0.0, 1.0], 1)]

        pasypy.main()
        
        for g in variables.safe_area:
            self.assertTrue((g[0][0] >= 1/2) and (g[1][0] >= 1/2) and (g[0][0] > g[1][0]))
        
        for r in variables.unsafe_area:
            self.assertTrue((r[0][0] < 1/2) or (r[1][0] < 1/2) or (r[0][0] <= r[1][0]))
        
        self.assertEqual(pasypy.calculate_area(variables.safe_area), 0.046875)
        self.assertEqual(pasypy.calculate_area(variables.unsafe_area), 0.78125)

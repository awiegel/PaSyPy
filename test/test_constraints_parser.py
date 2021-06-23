import unittest

import z3
from pasypy import constraints_parser, variables


class TestConstraintsParser(unittest.TestCase):

    def test_parse_from_textfield_no_quantifier(self):
        text = 'And(x >= 1/2, y >= 1/2, x >= y)'
        constraints_parser.parse_from_textfield(text)

        x = z3.Real('x')
        y = z3.Real('y')
        constraints = z3.And(x >= 1/2, y >= 1/2, x >= y)

        self.assertEqual(variables.Constraints, constraints)
        self.assertEqual(type(variables.Constraints), type(constraints))
        self.assertEqual(variables.parameters, [x,y])


    def test_parse_from_textfield_quantifier(self):
        text = 'Exists(z, Exists([p,q], And(x >= 1/2, y >= 1/2, y <= z, z <= x, p >= 1/4, p <= z, q <= 3/4, q >= z)))'
        constraints_parser.parse_from_textfield(text)

        x = z3.Real('x')
        y = z3.Real('y')
        z = z3.Real('z')
        p = z3.Real('p')
        q = z3.Real('q')
        constraints = z3.Exists(z, z3.Exists([p,q], z3.And(x >= 1/2, y >= 1/2, y <= z, z <= x, p >= 1/4, p <= z, q <= 3/4, q >= z)))

        self.assertEqual(variables.Constraints, constraints)
        self.assertEqual(type(variables.Constraints), type(constraints))
        self.assertEqual(variables.parameters, [x,y])


    def test_parse_from_file(self):
        file_path = 'test/test_benchmarks/basic.smt2'
        constraints_parser.parse_from_file(file_path)

        x = z3.Real('x')
        y = z3.Real('y')
        z = z3.Real('z')
        constraints = z3.Exists(z, z3.And(x >= 1/2, y >= 1/2, z > x, z < y))

        self.assertEqual(variables.Constraints, constraints)
        self.assertEqual(type(variables.Constraints), type(constraints))
        self.assertEqual(variables.parameters, [x,y])
    
    
    def test_parse_from_file_mixed_parameter_and_quantifier(self):
        file_path = 'test/test_benchmarks/mixed_parameter_and_quantifier.smt2'
        constraints_parser.parse_from_file(file_path)

        x = z3.Real('x')
        y = z3.Real('y')
        z = z3.Real('z')
        constraints = z3.Exists(z, z3.And(z + z + x >= 1/2, z + z - y >= 1/2, z > x, z < y))

        self.assertEqual(variables.Constraints, constraints)
        self.assertEqual(type(variables.Constraints), type(constraints))
        self.assertEqual(variables.parameters, [x,y])

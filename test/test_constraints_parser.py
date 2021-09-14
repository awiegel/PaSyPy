"""Tests the constraints_parser module."""

import unittest

import z3
from pasypy import variables
from pasypy.constraints_parser import ConstraintsParser


class TestConstraintsParser(unittest.TestCase):
    """Tests the constraints_parser module."""

    @classmethod
    def setUpClass(cls):
        cls.constraints_parser = ConstraintsParser()

    def test_parse_from_textfield_no_quantifier(self):
        """Checks if parsing from text field without quantifiers is correct."""
        text = 'And(x >= 1/2, y >= 1/2, x >= y)'
        self.constraints_parser.parse_from_textfield(text)

        x = z3.Real('x') # pylint: disable=C0103 # parameter name is conform
        y = z3.Real('y') # pylint: disable=C0103 # parameter name is conform
        constraints = z3.And(x >= 1/2, y >= 1/2, x >= y)

        self.assertEqual(variables.constraints, constraints)
        self.assertEqual(type(variables.constraints), type(constraints))
        self.assertEqual(variables.parameters, [x,y])

    def test_parse_from_textfield_quantifier(self):
        """Checks if parsing from text field with quantifiers is correct."""
        text = 'Exists(z, Exists([p,q], And(x >= 1/2, y >= 1/2, y <= z, z <= x, p >= 1/4, p <= z, q <= 3/4, q >= z)))'
        self.constraints_parser.parse_from_textfield(text)

        x = z3.Real('x') # pylint: disable=C0103 # parameter name is conform
        y = z3.Real('y') # pylint: disable=C0103 # parameter name is conform
        z = z3.Real('z') # pylint: disable=C0103 # parameter name is conform
        p = z3.Real('p') # pylint: disable=C0103 # parameter name is conform
        q = z3.Real('q') # pylint: disable=C0103 # parameter name is conform
        constraints = z3.Exists(z, z3.Exists([p,q], z3.And(x >= 1/2, y >= 1/2, y <= z, z <= x, p >= 1/4, p <= z, q <= 3/4, q >= z)))

        self.assertEqual(variables.constraints, constraints)
        self.assertEqual(type(variables.constraints), type(constraints))
        self.assertEqual(variables.parameters, [x,y])

    def test_parse_from_file(self):
        """Checks if parsing from .smt2 file is correct."""
        file_path = 'benchmarks/2params_greater_restricted_quantifier.smt2'
        self.constraints_parser.parse_from_file(file_path)

        x = z3.Real('x') # pylint: disable=C0103 # parameter name is conform
        y = z3.Real('y') # pylint: disable=C0103 # parameter name is conform
        z = z3.Real('z') # pylint: disable=C0103 # parameter name is conform
        constraints = z3.Exists(z, z3.And(x >= 1/2, y >= 1/2, z > x, z < y))

        self.assertEqual(variables.constraints, constraints)
        self.assertEqual(type(variables.constraints), type(constraints))
        self.assertEqual(variables.parameters, [x,y])

    def test_parse_from_file_mixed_parameter_and_quantifier(self):
        """Checks if parsing from .smt2 file on mixed parameter and quantifier constraints is correct."""
        file_path = 'benchmarks/2params_mixed_params_and_quantifier.smt2'
        self.constraints_parser.parse_from_file(file_path)

        x = z3.Real('x') # pylint: disable=C0103 # parameter name is conform
        y = z3.Real('y') # pylint: disable=C0103 # parameter name is conform
        z = z3.Real('z') # pylint: disable=C0103 # parameter name is conform
        constraints = z3.Exists(z, z3.And(z + z + x >= 1/2, z + z - y >= 1/2, z > x, z < y))

        self.assertEqual(variables.constraints, constraints)
        self.assertEqual(type(variables.constraints), type(constraints))
        self.assertEqual(variables.parameters, [x,y])

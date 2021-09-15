"""Tests the formula_parser module."""

import unittest

import z3
from pasypy import variables
from pasypy.formula_parser import FormulaParser


class TestFormulaParser(unittest.TestCase):
    """Tests the formula_parser module."""

    @classmethod
    def setUpClass(cls):
        cls.formula_parser = FormulaParser()

    def test_parse_from_textfield_no_quantifier(self):
        """Checks if parsing from text field without quantifiers is correct."""
        text = 'And(x >= 1/2, y >= 1/2, x >= y)'
        self.formula_parser.parse_from_textfield(text)

        x = z3.Real('x') # pylint: disable=C0103 # parameter name is conform
        y = z3.Real('y') # pylint: disable=C0103 # parameter name is conform
        formula = z3.And(x >= 1/2, y >= 1/2, x >= y)

        self.assertEqual(variables.formula, formula)
        self.assertEqual(type(variables.formula), type(formula))
        self.assertEqual(variables.parameters, [x,y])

    def test_parse_from_textfield_quantifier(self):
        """Checks if parsing from text field with quantifiers is correct."""
        text = 'Exists(z, Exists([p,q], And(x >= 1/2, y >= 1/2, y <= z, z <= x, p >= 1/4, p <= z, q <= 3/4, q >= z)))'
        self.formula_parser.parse_from_textfield(text)

        x = z3.Real('x') # pylint: disable=C0103 # parameter name is conform
        y = z3.Real('y') # pylint: disable=C0103 # parameter name is conform
        z = z3.Real('z') # pylint: disable=C0103 # parameter name is conform
        p = z3.Real('p') # pylint: disable=C0103 # parameter name is conform
        q = z3.Real('q') # pylint: disable=C0103 # parameter name is conform
        formula = z3.Exists(z, z3.Exists([p,q], z3.And(x >= 1/2, y >= 1/2, y <= z, z <= x, p >= 1/4, p <= z, q <= 3/4, q >= z)))

        self.assertEqual(variables.formula, formula)
        self.assertEqual(type(variables.formula), type(formula))
        self.assertEqual(variables.parameters, [x,y])

    def test_parse_from_file(self):
        """Checks if parsing from .smt2 file is correct."""
        file_path = 'benchmarks/2params_greater_restricted_quantifier.smt2'
        self.formula_parser.parse_from_file(file_path)

        x = z3.Real('x') # pylint: disable=C0103 # parameter name is conform
        y = z3.Real('y') # pylint: disable=C0103 # parameter name is conform
        z = z3.Real('z') # pylint: disable=C0103 # parameter name is conform
        formula = z3.Exists(z, z3.And(x >= 1/2, y >= 1/2, z > x, z < y))

        self.assertEqual(variables.formula, formula)
        self.assertEqual(type(variables.formula), type(formula))
        self.assertEqual(variables.parameters, [x,y])

    def test_parse_from_file_mixed_parameter_and_quantifier(self):
        """Checks if parsing from .smt2 file on mixed parameter and quantifier formulas is correct."""
        file_path = 'benchmarks/2params_mixed_params_and_quantifier.smt2'
        self.formula_parser.parse_from_file(file_path)

        x = z3.Real('x') # pylint: disable=C0103 # parameter name is conform
        y = z3.Real('y') # pylint: disable=C0103 # parameter name is conform
        z = z3.Real('z') # pylint: disable=C0103 # parameter name is conform
        formula = z3.Exists(z, z3.And(z + z + x >= 1/2, z + z - y >= 1/2, z > x, z < y))

        self.assertEqual(variables.formula, formula)
        self.assertEqual(type(variables.formula), type(formula))
        self.assertEqual(variables.parameters, [x,y])

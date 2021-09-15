"""Handles the parsing of the given formula."""

import re
from z3 import * # pylint: disable=W0614,W0401 # wildcard import is necessary to parse the formula dynamically
from pasypy import variables
from pasypy import settings
from pasypy.sampling import PreSampling

del u # z3 wildcard import is necessary and it defines 'u' which cannot be used in formulas -> delete it


class FormulaParser:
    """Handles the parsing of the given formula."""

    def __init__(self):
        if settings.pre_sampling:
            self.pre_sampling = PreSampling()

    def _get_number_of_vars(self, formula):
        """Extracts all parameters from the new formula.

        :param formula: The currently considered part of the formula.
        """
        if isinstance(formula, z3.QuantifierRef):
            self._get_number_of_vars(formula.body())
        elif isinstance(formula, z3.BoolRef):
            if settings.pre_sampling:
                self.pre_sampling.get_pre_sampling_candidate(formula)
            for sub_formula in formula.children():
                self._get_number_of_vars(sub_formula)
        elif type(formula) is z3.ArithRef: # pylint: disable=C0123 # isinstance checks for subclasses which cannot be used here
            if len(formula.children()) > 0:
                for sub_formula in formula.children():
                    self._get_number_of_vars(sub_formula)
            else:
                if 'var' not in formula.sexpr() and formula not in variables.parameters:
                    variables.parameters.append(formula)
        else:
            pass

    def _set_new_formula(self):
        """Sets the new formula after successfully parsing."""
        variables.parameters = []
        self._get_number_of_vars(variables.formula)

    def parse_from_file(self, file_path):
        """Parses the formula from a SMT-LIB file (.smt2).

        :param file_path: The path to the SMT-LIB file (.smt2).
        """
        try:
            variables.formula = parse_smt2_file(file_path, ctx=Context()) # provide own context because parser might be stuck in main context
            variables.formula = parse_smt2_file(file_path) # re-read correct file with main context

            if len(variables.formula) == 0:
                raise z3types.Z3Exception('no formula found')
            if len(variables.formula) == 1:
                variables.formula = variables.formula[0]
            else:
                variables.formula = z3.And(variables.formula)
            self._set_new_formula()
        except z3types.Z3Exception as e:
            variables.formula = None
            print(e)

    def parse_from_textfield(self, text):
        """Parses the formula from the text field.

        :param text: The text from the text field.
        :raises z3.z3types.Z3Exception: Value gets parsed but is not an actual BoolRef value.
        """
        temp_locals = []
        while True:
            try:
                variables.formula = eval(text) # pylint: disable=W0123 # eval is used here to parse the formula dynamically
                break
            except NameError as e:
                var = re.findall(r"name '(\w+)' is not defined",str(e))[0]
                locals()['{}'.format(var)] = Real('{}'.format(var))
                temp_locals.append(var)
            except AttributeError as e:
                bool_var = temp_locals[-1]
                locals()['{}'.format(bool_var)] = Bool('{}'.format(bool_var))
            except (SyntaxError, z3types.Z3Exception) as e:
                variables.formula = None
                print(e)
                break
        if not isinstance(variables.formula, z3.BoolRef):
            try:
                raise z3types.Z3Exception('Value cannot be converted into a Z3 Boolean value')
            except z3types.Z3Exception as e:
                variables.formula = None
                print(e)
        if variables.formula is not None:
            for temp_local in temp_locals:
                locals().pop(temp_local)
            self._set_new_formula()

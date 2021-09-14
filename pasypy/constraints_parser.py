"""Handles the parsing of the given constraints."""

import re
from z3 import * # pylint: disable=W0614,W0401 # wildcard import is necessary to parse the constraints dynamically
from pasypy import variables
from pasypy import settings
from pasypy.sampling import PreSampling

del u # z3 wildcard import is necessary and it defines 'u' which cannot be used in constraints -> delete it


class ConstraintsParser:
    """Handles the parsing of the given constraints."""

    def __init__(self):
        if settings.pre_sampling:
            self.pre_sampling = PreSampling()

    def _get_number_of_vars(self, formula):
        """Extracts all parameters from the new constraints.

        :param formula: The currently considered part of the formula.
        """
        if isinstance(formula, z3.z3.QuantifierRef):
            self._get_number_of_vars(formula.body())
        elif isinstance(formula, z3.z3.BoolRef):
            if settings.pre_sampling:
                self.pre_sampling.get_pre_sampling_candidate(formula)
            for sub_formula in formula.children():
                self._get_number_of_vars(sub_formula)
        elif type(formula) is z3.z3.ArithRef: # pylint: disable=C0123 # isinstance checks for subclasses which cannot be used here
            if len(formula.children()) > 0:
                for sub_formula in formula.children():
                    self._get_number_of_vars(sub_formula)
            else:
                if 'var' not in formula.sexpr() and formula not in variables.parameters:
                    variables.parameters.append(formula)
        else:
            pass

    def _set_new_constraints(self):
        """Sets the new constraints after successfully parsing."""
        variables.parameters = []
        self._get_number_of_vars(variables.constraints)

    def parse_from_file(self, file_path):
        """Parses the constraints from a SMT-LIB file (.smt2).

        :param file_path: The path to the SMT-LIB file (.smt2).
        """
        try:
            variables.constraints = parse_smt2_file(file_path, ctx=Context())[0] # provide own context because parser might be stuck in main context
            variables.constraints = parse_smt2_file(file_path)[0] # re-read correct file with main context
            self._set_new_constraints()
        except z3types.Z3Exception as e:
            variables.constraints = None
            print(e)

    def parse_from_textfield(self, text):
        """Parses the constraints from the text field.

        :param text: The text from the text field.
        :raises z3.z3types.Z3Exception: Value gets parsed but is not an actual BoolRef value.
        """
        temp_locals = []
        while True:
            try:
                variables.constraints = eval(text) # pylint: disable=W0123 # eval is used here to parse the constraints dynamically
                break
            except NameError as e:
                var = re.findall(r"name '(\w+)' is not defined",str(e))[0]
                locals()['{}'.format(var)] = Real('{}'.format(var))
                temp_locals.append(var)
            except AttributeError as e:
                bool_var = temp_locals[-1]
                locals()['{}'.format(bool_var)] = Bool('{}'.format(bool_var))
            except (SyntaxError, z3.z3types.Z3Exception) as e:
                variables.constraints = None
                print(e)
                break
        if not isinstance(variables.constraints, z3.z3.BoolRef):
            try:
                raise z3.z3types.Z3Exception('Value cannot be converted into a Z3 Boolean value')
            except z3.z3types.Z3Exception as e:
                variables.constraints = None
                print(e)
        if variables.constraints is not None:
            for temp_local in temp_locals:
                locals().pop(temp_local)
            self._set_new_constraints()

import re
from z3 import * # pylint: disable=W0614,W0401
from pasypy import variables

del u # z3 wildcard import is necessary and it defines 'u' which cannot be used in constraints -> delete it


class ConstraintsParser:
    def _get_number_of_vars(self, formula):
        if isinstance(formula, z3.z3.QuantifierRef):
            self._get_number_of_vars(formula.body())
        elif isinstance(formula, z3.z3.BoolRef):
            for sub_formula in formula.children():
                self._get_number_of_vars(sub_formula)
        elif type(formula) is z3.z3.ArithRef:
            if len(formula.children()) > 0:
                for sub_formula in formula.children():
                    self._get_number_of_vars(sub_formula)
            else:
                if 'var' not in formula.sexpr() and formula not in variables.parameters:
                    variables.parameters.append(formula)
        else:
            pass

    def _set_new_constraints(self):
        variables.parameters = []
        self._get_number_of_vars(variables.constraints)

    def parse_from_file(self, file_path):
        try:
            variables.constraints = parse_smt2_file(file_path, ctx=Context())[0] # provide own context because parser might be stuck in main context
            variables.constraints = parse_smt2_file(file_path)[0] # re-read correct file with main context
            self._set_new_constraints()
        except z3.z3types.Z3Exception as e:
            variables.constraints = None
            print(e)

    def parse_from_textfield(self, text):
        temp_locals = []
        while True:
            try:
                variables.constraints = eval(text)
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

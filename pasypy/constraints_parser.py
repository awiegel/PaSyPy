import re

from z3 import *

from pasypy import variables

del u # z3 wildcard import is necessary and it defines 'u' which cannot be used in constraints -> delete it

class ConstraintsParser:
    
    def _get_number_of_vars(self, formula):
            if type(formula) == z3.z3.QuantifierRef:
                self._get_number_of_vars(formula.body())
            elif type(formula) == z3.z3.BoolRef:
                # if len(formula.children()) > 0:
                for subFormula in formula.children():
                    self._get_number_of_vars(subFormula)
                # else:
                #     variables.parameters.append(formula)
            elif type(formula) == z3.z3.ArithRef:
                if len(formula.children()) > 0:
                    for subFormula in formula.children():
                        self._get_number_of_vars(subFormula)
                else:
                    if 'var' not in formula.sexpr() and formula not in variables.parameters:
                        variables.parameters.append(formula)
            else:
                pass


    def _set_new_constraints(self):
        variables.parameters = []
        self._get_number_of_vars(variables.Constraints)


    def parse_from_file(self, file_path):
        try:
            variables.Constraints = parse_smt2_file(file_path)[0]
            self._set_new_constraints()
        except z3.z3types.Z3Exception as e:
            variables.Constraints = None
            print(e)


    def parse_from_textfield(self, text):
        temp_locals = []
        while True:
            try:
                variables.Constraints = eval(text)
                break
            except NameError as e:
                var = re.findall(r"name '(\w+)' is not defined",str(e))[0]
                locals()['{}'.format(var)] = Real('{}'.format(var))
                temp_locals.append(var)
            except AttributeError as e:
                bool_var = temp_locals[-1]
                locals()['{}'.format(bool_var)] = Bool('{}'.format(bool_var))
        for temp_local in temp_locals:
            locals().pop(temp_local)

        self._set_new_constraints()

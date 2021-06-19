from z3 import *

import variables
import re


def _get_number_of_vars(formula):
        if type(formula) == z3.z3.QuantifierRef:
            for i in range(formula.num_vars()):
                variables.quantifiers.append(formula.var_name(i))
            _get_number_of_vars(formula.body())
        elif type(formula) == z3.z3.BoolRef:
            # if len(formula.children()) > 0:
            for subFormula in formula.children():
                _get_number_of_vars(subFormula)
            # else:
            #     variables.parameters.append(formula)
        elif type(formula) == z3.z3.ArithRef:
            if 'var' not in formula.sexpr() and formula not in variables.parameters:
                variables.parameters.append(formula)
        else:
            pass


def set_new_constraints():
    variables.parameters = []
    variables.quantifiers = []
    
    _get_number_of_vars(variables.Constraints)
    variables.Constraints_neg = Not(variables.Constraints)


def parse_from_file(file_path):
    variables.Constraints = parse_smt2_file(file_path)[0]
    set_new_constraints()


def parse_from_textfield(text):
    temp_locals = []
    while True:
        try:
            variables.Constraints = eval(text)
            break
        except NameError as e:
            var = re.findall(r"name '(\w+)' is not defined",str(e))[0]
            locals()['{}'.format(var)] = Real('{}'.format(var))
            temp_locals.append(var)
    for temp_local in temp_locals:
        locals().pop(temp_local)

    set_new_constraints()

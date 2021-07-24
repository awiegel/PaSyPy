import z3

from pasypy import variables, splitting_heuristics


def add_boundary(s, B):
    for index, value in enumerate(variables.parameters):
        s.add(value >= B[index][0])
        s.add(value <= B[index][1])


def solveit(B):
    variables.Queue.pop(0)

    variables.solver.push()
    add_boundary(variables.solver, B)

    status = variables.solver.check()
    if status == z3.sat:
        variables.solver_neg.push()
        add_boundary(variables.solver_neg, B)

        status = variables.solver_neg.check()
        if status == z3.sat:
            splitting_heuristics.dispatcher[splitting_heuristics.current_splitting_heuristic](B)

        elif status == z3.unsat:
            variables.G.append(B)
        else:
            print('TIMEOUT NEG', variables.solver_neg.reason_unknown()) # pragma: no cover

        variables.solver.pop()
        variables.solver_neg.pop()

    elif status == z3.unsat:
        variables.solver.pop()
        variables.R.append(B)
    else:
        print('TIMEOUT', variables.solver.reason_unknown()) # pragma: no cover





def calculate_area(boxes):
    area = 0
    for i in boxes:
        mult = 1
        for j in range(len(variables.parameters)):
            mult *= (i[j][1]-i[j][0]) / (variables.x_axe_limit[1] - variables.x_axe_limit[0])
        area += mult
    return area


def check_zoom():
    inside_zoom = ((variables.Queue[0][variables.x_axe_position][0] >= variables.x_axe_limit_temp[0]) and \
                   (variables.Queue[0][variables.x_axe_position][1] <= variables.x_axe_limit_temp[1]))
    if inside_zoom and (len(variables.parameters) > 1):
        inside_zoom = ((variables.Queue[0][variables.y_axe_position][0] >= variables.y_axe_limit_temp[0]) and \
                       (variables.Queue[0][variables.y_axe_position][1] <= variables.y_axe_limit_temp[1]))
    return inside_zoom


def init_solvers():
    variables.solver.reset()
    variables.solver_neg.reset()
    variables.solver.add(variables.Constraints)
    variables.solver_neg.add(z3.Not(variables.Constraints))


def main():
    init_solvers()

    while variables.Queue:
        if check_zoom() and (variables.Queue[0][len(variables.parameters)] <= (2**variables.depth_limit)):
            solveit(variables.Queue[0])
        else:
            variables.Sub_Queue.append(variables.Queue[0])
            variables.Queue.pop(0)

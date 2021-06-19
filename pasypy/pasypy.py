import z3

import timeit
import itertools

import variables
import visualize
import gui


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
        variables.solver.pop()

        variables.solver_neg.push()
        add_boundary(variables.solver_neg, B)

        status = variables.solver_neg.check()
        if status == z3.sat:
            split_box(B)
        elif status == z3.unsat:
            variables.G.append(B[:-1])
        else:
            print('TIMEOUT NEG', variables.solver_neg.reason_unknown())

        variables.solver_neg.pop()
    elif status == z3.unsat:
        variables.solver.pop()
        variables.R.append(B[:-1])
    else:
        print('TIMEOUT', variables.solver.reason_unknown())


def split_box(area):
    depth = area[len(variables.parameters)]*2
    d = 1 / (depth / (variables.x_axe_limit[1] - variables.x_axe_limit[0]))

    borders = []
    for i in range(len(variables.parameters)):
        borders.append([[(area[i][0] + d), area[i][1]], [area[i][0], (area[i][1] - d)]])
    cross = itertools.product(*borders, repeat=1)
    for i in cross:
        i = i[:len(variables.parameters)] + (depth,)
        if depth < 2**variables.depth_limit:
            variables.Queue.append(i)
        else:
            variables.Sub_Queue.append(i)


def calculate_area(boxes):
    area = 0
    for i in boxes:
        mult = 1
        for j in range(len(variables.parameters)):
            mult *= (i[j][1]-i[j][0]) / (variables.x_axe_limit[1] - variables.x_axe_limit[0])
        area += mult
    return area


def check_zoom():
    if len(variables.parameters) > 1:
        inside_zoom = ((variables.Queue[0][0][0] >= gui.app.global_xlim[0]) and \
                       (variables.Queue[0][0][1] <= gui.app.global_xlim[1]) and \
                       (variables.Queue[0][1][0] >= gui.app.global_ylim[0]) and \
                       (variables.Queue[0][1][1] <= gui.app.global_ylim[1]))
    else:
        inside_zoom = ((variables.Queue[0][0][0] >= gui.app.global_xlim[0]) and \
                       (variables.Queue[0][0][1] <= gui.app.global_xlim[1]))
    return inside_zoom


def init_solvers():
    variables.solver.reset()
    variables.solver_neg.reset()
    variables.solver.add(variables.Constraints)
    variables.solver_neg.add(variables.Constraints_neg)


def main():
    try:
        timestamps = {'Start Time': timeit.default_timer()}

        init_solvers()

        while variables.Queue:
            if check_zoom() and (variables.Queue[0][len(variables.parameters)] < ((2**variables.depth_limit)/2)):
                solveit(variables.Queue[0])
            else:
                variables.Sub_Queue.append(variables.Queue[0])
                variables.Queue.pop(0)

        
    except KeyboardInterrupt:
        None

    finally:
        visualize.create_timestamp('Computation Time', timestamps)

        visualize.generate_graph()

        visualize.create_timestamp('Visualization Time', timestamps)

        visualize.show_time(timestamps)


if __name__ == "__main__":
    gui.root.mainloop()

from z3 import *
import timeit

import variables
import visualize
import gui


def add_boundary(s, B):
    for index, value in zip(range(len(variables.parameters)), variables.parameters):
        s.add(value >= B[index][0])
        s.add(value <= B[index][1])


def solveit(B):
    variables.Queue.pop(0)

    variables.solver.push()
    add_boundary(variables.solver, B)

    if variables.solver.check() == sat:
        variables.solver.pop()

        variables.solver_neg.push()
        add_boundary(variables.solver_neg, B)

        if variables.solver_neg.check() == sat:
            split_box(B)
        else:
            variables.G.append(B[:-1])
        variables.solver_neg.pop()
    else:
        variables.solver.pop()
        variables.R.append(B[:-1])


def split_box(area):
    depth = area[2]*2
    d = 1 / depth
    X1 = area[0][0]
    X1M = X1+d
    X2 = area[0][1]
    X2M = X2-d
    Y1 = area[1][0]
    Y1M = Y1+d
    Y2 = area[1][1]
    Y2M = Y2-d

    if depth < 2**variables.depth_limit:
        variables.Queue.append(([X1M, X2], [Y1M, Y2], depth))
        variables.Queue.append(([X1, X2M], [Y1, Y2M], depth))
        variables.Queue.append(([X1M, X2], [Y1, Y2M], depth))
        variables.Queue.append(([X1, X2M], [Y1M, Y2], depth))
    else:
        variables.Sub_Queue.append(([X1M, X2], [Y1M, Y2], depth))
        variables.Sub_Queue.append(([X1, X2M], [Y1, Y2M], depth))
        variables.Sub_Queue.append(([X1M, X2], [Y1, Y2M], depth))
        variables.Sub_Queue.append(([X1, X2M], [Y1M, Y2], depth))


def calculate_area(boxes):
    area = 0
    for i in boxes:
        area += (i[0][1]-i[0][0]) * (i[1][1]-i[1][0])
    return area

def check_zoom():
    return ((variables.Queue[0][0][0] >= gui.app.global_xlim[0]) and \
            (variables.Queue[0][0][1] <= gui.app.global_xlim[1]) and \
            (variables.Queue[0][1][0] >= gui.app.global_ylim[0]) and \
            (variables.Queue[0][1][1] <= gui.app.global_ylim[1]))


def main():
    try:
        timestamps = {'Start Time': timeit.default_timer()}


        variables.solver.reset()
        variables.solver_neg.reset()
        
        variables.solver.add(variables.Constraints)
        variables.solver_neg.add(Not(variables.Constraints))


        while variables.Queue:
            if check_zoom() and (variables.Queue[0][len(variables.parameters)] < ((2**variables.depth_limit)/2)):

                solveit(variables.Queue[0])
                visualize.show_progress()
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

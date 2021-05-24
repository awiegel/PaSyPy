from z3 import *

from variables import *
from visualize import *


def add_boundary(s, B):
    s.add(x >= B[0][0], x <= B[0][1], y >= B[1][0], y <= B[1][1])


def solveit(B):
    Queue.pop(0)

    solver.push()
    add_boundary(solver, B)

    if solver.check() == sat:
        solver.pop()

        solver_neg.push()
        add_boundary(solver_neg, B)

        if solver_neg.check() == sat:
            split_box(B)
        else:
            G.append(B[:-1])
        solver_neg.pop()
    else:
        solver.pop()
        R.append(B[:-1])


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

    if depth < 2**depth_limit:
        Queue.append(([X1M, X2], [Y1M, Y2], depth))
        Queue.append(([X1, X2M], [Y1, Y2M], depth))
        Queue.append(([X1M, X2], [Y1, Y2M], depth))
        Queue.append(([X1, X2M], [Y1M, Y2], depth))


def calculate_area(boxes):
    area = 0
    for i in boxes:
        area += (i[0][1]-i[0][0]) * (i[1][1]-i[1][0])
    return area


def main():
    try:
        timestamps = {'Start Time': timeit.default_timer()}

        solver.add(f)
        solver_neg.add(Not(f))

        while Queue:
            solveit(Queue[0])
            show_progress()

    except KeyboardInterrupt:
        None

    finally:
        create_timestamp('Computation Time', timestamps)

        generate_graph()

        create_timestamp('Visualization Time', timestamps)

        show_time(timestamps)

        show_graph()


if __name__ == "__main__":
    main()

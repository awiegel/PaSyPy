from z3 import *

s = Solver()

x = Real('x')
y = Real('y')

f = x + y <= 1

# starting box with intervalls [0,1] € R and depth 1
Queue = [([0, 1], [0, 1], 1)]

G = []
R = []

# stops at the limit (1/(2**depth_limit)). Can also be stopped before by pressing Ctrl+C. Amount of splits where 1 is initial box and 2 is the initial box split into 2**dimensions boxes.
depth_limit = 6


def add_boundary(B):
    s.add(x >= B[0][0], x <= B[0][1], y >= B[1][0], y <= B[1][1])


def solveit(B):
    if Queue:
        Queue.pop(0)

    s.push()
    s.add(f)
    add_boundary(B)

    if s.check() == sat:
        s.pop()

        s.push()
        s.add(Not(f))
        add_boundary(B)

        if s.check() == sat:
            split_box(B)
            s.pop()
        else:
            s.pop()
            G.append(B[:-1])
    else:
        s.pop()
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


def main():
    while Queue:
        solveit(Queue[0])


if __name__ == "__main__":
    main()

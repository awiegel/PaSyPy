from z3 import *

s = Solver()

x = Real('x')
y = Real('y')

f = x + y <= 1

# starting box with intervalls [0,1] € R and depth 1
Queue = [([0, 1], [0, 1], 1)]

G = []
R = []


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

        s.add(Not(f))
        s.push()
        add_boundary(B)

        if s.check() == sat:
            # split_box(B)
            s.pop()
        else:
            s.pop()
            G.append(B[:-1])
    else:
        s.pop()
        R.append(B[:-1])


def main():
    while Queue:
        solveit(Queue[0])


if __name__ == "__main__":
    main()

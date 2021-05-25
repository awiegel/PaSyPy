from z3 import Solver, Real

solver = Solver()
solver_neg = Solver()

x = Real('x')
y = Real('y')

Constraints = []
Constraints.append(x + y <= 1.5)

parameters = [x, y]

# starting box with intervalls [0,1] € R and depth 1
Queue = [([0, 1], [0, 1], 1)]
Sub_Queue = []

G = []
R = []

# stops at the limit (1/(2**depth_limit)). Can also be stopped before by pressing Ctrl+C. Amount of splits where 1 is initial box and 2 is the initial box split into 2**dimensions boxes.
depth_limit = 6


def main():
    None


if __name__ == "__main__":
    main()

import z3


solver = z3.ParOr('smt', 'default').solver(logFile='logs/logfile.log')
solver_neg = z3.ParOr('smt', 'default').solver(logFile='logs/logfile.log')

Constraints = None
Constraints_neg = None

parameters = []
quantifiers = []

# starting box with intervalls [0,1] € R and depth 1
Queue = []
Sub_Queue = []

G = []
R = []

# stops at the limit (1/(2**depth_limit)). Can also be stopped before by pressing Ctrl+C. Amount of splits where 1 is initial box and 2 is the initial box split into 2**dimensions boxes.
depth_limit = 5

previous_depth_limit = 0
previous_Constraints = []

x_axe_position = 0
y_axe_position = 0

x_axe_limit = [0.0, 1.0]
y_axe_limit = [0.0, 1.0]

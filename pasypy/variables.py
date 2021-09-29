"""Contains global variables needed for this tool."""

import z3


solver = z3.ParOr('smt', 'default').solver(logFile='logs/logfile.log')
solver_neg = z3.ParOr('smt', 'default').solver(logFile='logs/logfile_neg.log')

formula = None # pylint: disable=C0103 # is not a constant

parameters = []

# starting box with intervalls [0,1] € R and depth 1
queue = []
sub_queue = []

safe_area = []
unsafe_area = []

models = []
models_neg = []

# stops at the limit (1/(2**depth_limit)). Can also be stopped before by pressing Ctrl+C.
# Amount of splits where 1 is initial box and 2 is the initial box split into 2**dimensions boxes.
depth_limit = 8 # pylint: disable=C0103 # is not a constant

x_axe_position = 0 # pylint: disable=C0103 # is not a constant
y_axe_position = 0 # pylint: disable=C0103 # is not a constant

DEFAULT_LIMIT = [0.0, 1.0]
x_axe_limit = DEFAULT_LIMIT.copy()
y_axe_limit = DEFAULT_LIMIT.copy()
interval_limit = []

x_axe_limit_temp = x_axe_limit
y_axe_limit_temp = y_axe_limit

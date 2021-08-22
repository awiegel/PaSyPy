import z3

from pasypy import variables
from pasypy.splitting_heuristic import SplittingHeuristic
from pasypy.logger import Logger


class PaSyPy:
    def __init__(self):
        self.init_solvers()

    def add_boundary(self, solver, area):
        for index, value in enumerate(variables.parameters):
            solver.add(value >= area[index][0])
            solver.add(value <= area[index][1])

    def solveit(self, area):
        variables.queue.pop(0)
        variables.solver.push()
        self.add_boundary(variables.solver, area)
        status = variables.solver.check()
        if status == z3.sat:
            variables.solver_neg.push()
            self.add_boundary(variables.solver_neg, area)
            status = variables.solver_neg.check()
            if status == z3.sat:
                SplittingHeuristic().apply_heuristic(area)
            elif status == z3.unsat:
                variables.safe_area.append(area)
            else:
                print('TIMEOUT NEG', variables.solver_neg.reason_unknown()) # pragma: no cover
            variables.solver.pop()
            variables.solver_neg.pop()
        elif status == z3.unsat:
            variables.solver.pop()
            variables.unsafe_area.append(area)
        else:
            print('TIMEOUT', variables.solver.reason_unknown()) # pragma: no cover

    def check_zoom(self):
        inside_zoom = ((variables.queue[0][variables.x_axe_position][0] >= variables.x_axe_limit_temp[0]) and \
                       (variables.queue[0][variables.x_axe_position][1] <= variables.x_axe_limit_temp[1]))
        if inside_zoom and (len(variables.parameters) > 1):
            inside_zoom = ((variables.queue[0][variables.y_axe_position][0] >= variables.y_axe_limit_temp[0]) and \
                           (variables.queue[0][variables.y_axe_position][1] <= variables.y_axe_limit_temp[1]))
        return inside_zoom

    def init_solvers(self):
        variables.solver.reset()
        variables.solver_neg.reset()
        variables.solver.add(variables.constraints)
        variables.solver_neg.add(z3.Not(variables.constraints))

    def main(self):
        while variables.queue:
            if self.check_zoom() and (variables.queue[0][len(variables.parameters)] <= (2**variables.depth_limit)):
                self.solveit(variables.queue[0])
            else:
                variables.sub_queue.append(variables.queue[0])
                variables.queue.pop(0)
        Logger().create_logfiles()

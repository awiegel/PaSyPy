"""Tries to find safe and unsafe regions of the parameter space."""

import z3

from pasypy import variables
from pasypy.splitting_heuristic import SplittingHeuristic
from pasypy.logger import Logger


class PaSyPy:
    """Tries to find safe and unsafe regions of the parameter space."""

    def __init__(self):
        """Initializes the solvers used by this class."""
        self.init_solvers()

    @staticmethod
    def init_solvers():
        """Initializes the solvers by resetting them and adding the formula."""
        variables.solver.reset()
        variables.solver_neg.reset()
        variables.solver.add(variables.formula)
        variables.solver_neg.add(z3.Not(variables.formula))

    @staticmethod
    def add_boundary(solver, area):
        """Adds the boundaries of given area to the formula.

        :param solver: The used solver. There are two solvers available, one for the original formula and the other for the negated formula.
        :param area: The considered area.
        """
        for index, value in enumerate(variables.parameters):
            solver.add(value >= area[index][0])
            solver.add(value <= area[index][1])

    @staticmethod
    def check_zoom():
        """Compares the first element in the queue with the currently applied zoom area.

        :return: True if element is inside the currently applied zoom area.
        """
        inside_zoom = ((variables.queue[0][variables.x_axe_position][0] >= variables.x_axe_limit_temp[0]) and \
                       (variables.queue[0][variables.x_axe_position][1] <= variables.x_axe_limit_temp[1]))
        if inside_zoom and (len(variables.parameters) > 1):
            inside_zoom = ((variables.queue[0][variables.y_axe_position][0] >= variables.y_axe_limit_temp[0]) and \
                           (variables.queue[0][variables.y_axe_position][1] <= variables.y_axe_limit_temp[1]))
        return inside_zoom

    def solveit(self, area):
        """Checks if the given area is safe, unsafe or unknown and requires splitting.
        For this the solver first checks if the original formula on given area are satisfiable (sat).
        If not, the area is unsafe (red by default).
        Otherwise the solver checks the negated formula on given area for satisfiability (sat).
        If it is unsatifiable (unsat), the area is safe (green by default).
        If it is satisfiable (sat), meaning the original formula and the negated formula are both satisfiable (sat),
        the area contains both safe and unsafe candidates and has to be split further into smaller sub areas.

        :param area: The considered area.
        """
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

    def main(self, application):
        """The main function of this tool which tries to find safe and unsafe regions of the parameter space."""
        while variables.queue and application.running:
            if self.check_zoom() and (variables.queue[0][len(variables.parameters)] <= (2**variables.depth_limit)):
                self.solveit(variables.queue[0])
            else:
                variables.sub_queue.append(variables.queue[0])
                variables.queue.pop(0)
            application.update() # prevents the GUI to get stuck in this loop
        Logger().create_logfiles()

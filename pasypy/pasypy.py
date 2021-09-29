"""Tries to find safe and unsafe regions of the parameter space."""

import z3

from pasypy import variables
from pasypy.splitting_heuristic import SplittingHeuristic
from pasypy.logger import Logger


class PaSyPy:
    """Tries to find safe and unsafe regions of the parameter space."""

    FACTOR = 0.0001

    def __init__(self):
        """Initializes the solvers used by this class."""
        self.init_solvers()
        self.splitting_heuristic = SplittingHeuristic()
        self.model_index = 0

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

    def check_factor(self):
        """Checks if the queue contains scientific notation (<0.0001) because solver crashes on this.

        :return: If the factor is acceptable by the solver.
        """
        correct_factor = True
        for parameter in range(len(variables.parameters)):
            left_number = variables.queue[0][parameter][0]
            right_number = variables.queue[0][parameter][1]
            if left_number < 0:
                left_number = -left_number
            if right_number < 0:
                right_number = -right_number
            if ((left_number < self.FACTOR) and (left_number != 0)) or ((right_number < self.FACTOR)  and (right_number != 0)):
                correct_factor = False
                break
        return correct_factor

    def check_if_point_is_already_known(self, area, models, remove_index=True):
        """Checks if point inside the area is already known.

        :param area: The considered area.
        :param models: The models list either for green or red points.
        :param remove_index: The index to remove from the models list, defaults to True
        :return: True if a known point is inside the area.
        """
        found = False
        for model_index, model in enumerate(models):
            if found:
                break
            for index in range(len(variables.parameters)):
                if (model[index] >= area[index][0]) and (model[index] <= area[index][1]):
                    if index == len(variables.parameters)-1:
                        found = True
                        if remove_index:
                            self.model_index = model_index
                else:
                    break
        return found

    @staticmethod
    def remember_current_model(solver, models):
        """Remembers the found point for later to reduce solving calls.

        :param solver: The used solver. There are two solvers available, one for the original formula and the other for the negated formula.
        :param models: The models list either for green or red points.
        """
        temp = []
        break_algebraic = False
        for parameter in variables.parameters:
            model = solver.model()[parameter]
            if isinstance(model, z3.z3.AlgebraicNumRef):
                break_algebraic = True
                break
            model = (model.numerator().as_long() / model.denominator().as_long())
            temp.append(model)
        if not break_algebraic:
            models.append(temp)

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
        if not self.check_if_point_is_already_known(area, variables.models):
            variables.solver.push()
            self.add_boundary(variables.solver, area)
            status = variables.solver.check()
            if status == z3.sat:
                self.remember_current_model(variables.solver, variables.models)
                if not self.check_if_point_is_already_known(area, variables.models_neg, remove_index=False):
                    variables.solver_neg.push()
                    self.add_boundary(variables.solver_neg, area)
                    status = variables.solver_neg.check()
                    if status == z3.sat:
                        self.remember_current_model(variables.solver_neg, variables.models_neg)
                        self.splitting_heuristic.apply_heuristic(area)
                    elif status == z3.unsat:
                        variables.safe_area.append(area)
                    else:
                        print('TIMEOUT NEG', variables.solver_neg.reason_unknown()) # pragma: no cover
                    variables.solver_neg.pop()
                else:
                    self.splitting_heuristic.apply_heuristic(area)
            elif status == z3.unsat:
                variables.unsafe_area.append(area)
            else:
                print('TIMEOUT', variables.solver.reason_unknown()) # pragma: no cover
            variables.solver.pop()
        else:
            if not self.check_if_point_is_already_known(area, variables.models_neg, remove_index=False):
                variables.solver_neg.push()
                self.add_boundary(variables.solver_neg, area)
                status = variables.solver_neg.check()
                if status == z3.sat:
                    self.remember_current_model(variables.solver_neg, variables.models_neg)
                    self.splitting_heuristic.apply_heuristic(area)
                elif status == z3.unsat:
                    variables.safe_area.append(area)
                    variables.models.pop(self.model_index)
                else:
                    print('TIMEOUT NEG', variables.solver_neg.reason_unknown()) # pragma: no cover
                variables.solver_neg.pop()
            else:
                self.splitting_heuristic.apply_heuristic(area)

    def main(self, application):
        """The main function of this tool which tries to find safe and unsafe regions of the parameter space."""
        while variables.queue and application.running:
            if self.check_zoom() and (variables.queue[0][len(variables.parameters)] <= (2**variables.depth_limit)) and self.check_factor():
                self.solveit(variables.queue[0])
            else:
                variables.sub_queue.append(variables.queue[0])
                variables.queue.pop(0)
            application.update() # prevents the GUI to get stuck in this loop
        Logger().create_logfiles()

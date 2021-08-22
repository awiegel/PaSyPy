import z3

from pasypy import variables, splitting_heuristic
from pasypy.splitting_heuristic import SplittingHeuristic

class PaSyPy:

    def __init__(self):
        self.init_solvers()


    def add_boundary(self, s, B):
        for index, value in enumerate(variables.parameters):
            s.add(value >= B[index][0])
            s.add(value <= B[index][1])


    def solveit(self, B):
        variables.Queue.pop(0)

        variables.solver.push()
        self.add_boundary(variables.solver, B)

        status = variables.solver.check()
        if status == z3.sat:

            variables.solver_neg.push()
            self.add_boundary(variables.solver_neg, B)

            status = variables.solver_neg.check()
            if status == z3.sat:
                SplittingHeuristic().apply_heuristic(B)
            elif status == z3.unsat:
                variables.G.append(B)
            else:
                print('TIMEOUT NEG', variables.solver_neg.reason_unknown()) # pragma: no cover

            variables.solver.pop()
            variables.solver_neg.pop()
        elif status == z3.unsat:
            variables.solver.pop()
            variables.R.append(B)
            
        else:
            print('TIMEOUT', variables.solver.reason_unknown()) # pragma: no cover


    def check_zoom(self):
        inside_zoom = ((variables.Queue[0][variables.x_axe_position][0] >= variables.x_axe_limit_temp[0]) and \
                    (variables.Queue[0][variables.x_axe_position][1] <= variables.x_axe_limit_temp[1]))
        if inside_zoom and (len(variables.parameters) > 1):
            inside_zoom = ((variables.Queue[0][variables.y_axe_position][0] >= variables.y_axe_limit_temp[0]) and \
                        (variables.Queue[0][variables.y_axe_position][1] <= variables.y_axe_limit_temp[1]))
        return inside_zoom


    def init_solvers(self):
        variables.solver.reset()
        variables.solver_neg.reset()
        variables.solver.add(variables.Constraints)
        variables.solver_neg.add(z3.Not(variables.Constraints))


    def main(self):
        while variables.Queue:
            if self.check_zoom() and (variables.Queue[0][len(variables.parameters)] <= (2**variables.depth_limit)):
                self.solveit(variables.Queue[0])
            else:
                variables.Sub_Queue.append(variables.Queue[0])
                variables.Queue.pop(0)

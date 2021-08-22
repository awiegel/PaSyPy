import itertools
import random
import z3

from pasypy import variables


SPLITTING_HEURISTIC = ['Default','Simple','Extended','Random']
current_splitting_heuristic = SPLITTING_HEURISTIC[0]


class SplittingHeuristic:
    def __init__(self):
        self.dispatcher = { 'Default' : self.default_heuristic,
                            'Simple'  : self.simple_heuristic,
                            'Extended': self.extended_heuristic,
                            'Random'  : self.random_heuristic
        }

    def default_heuristic(self, area):
        depth = area[len(variables.parameters)]*(2**len(variables.parameters))
        borders = []
        for i in range(len(variables.parameters)):
            half_area = (area[i][1] - area[i][0]) / 2
            borders.append([[(area[i][0] + half_area), area[i][1]], [area[i][0], (area[i][1] - half_area)]])
        cross = itertools.product(*borders, repeat=1)
        for i in cross:
            i = i[:len(variables.parameters)] + (depth,)
            variables.queue.append(i)

    def simple_heuristic(self, area):
        depth = area[len(variables.parameters)]*2
        counter = 0
        temp_depth = (depth/2)/2
        while temp_depth >= 1:
            temp_depth /= 2
            counter += 1
        counter %= len(variables.parameters)
        half_area = (area[counter][1] - area[counter][0]) / 2
        new_interval1 = [area[counter][0], (area[counter][1] - half_area)]
        new_interval2 = [(area[counter][0] + half_area), area[counter][1]]
        area1 = area
        area1 = list(area1)
        area1[counter] = new_interval1
        area1[len(variables.parameters)] = depth
        area1 = tuple(area1)
        variables.queue.append(area1)
        area2 = area
        area2 = list(area2)
        area2[counter] = new_interval2
        area2[len(variables.parameters)] = depth
        area2 = tuple(area2)
        variables.queue.append(area2)

    def extended_heuristic(self, area):
        models = []
        for value in variables.parameters:
            model = variables.solver.model()[value]
            if type(model) is z3.z3.AlgebraicNumRef:
                model = model.approx(area[len(variables.parameters)])
            model = (model.numerator().as_long() / model.denominator().as_long())
            models.append(model)

        done_flag = False
        for index, value in enumerate(variables.parameters):
            if (not done_flag) and (model in (area[index][0], area[index][1])):
                variables.solver.push()
                variables.solver.add(value != models[index])
                status = variables.solver.check()
                if status == z3.sat:
                    variables.solver_neg.push()
                    variables.solver_neg.add(value != models[index])
                    status = variables.solver_neg.check()
                    if status == z3.unsat:
                        variables.safe_area.append(area)
                        done_flag = True
                    else:
                        pass
                    variables.solver_neg.pop()
                elif status == z3.unsat:
                    variables.unsafe_area.append(area)
                    done_flag = True
                else:
                    pass
                variables.solver.pop()

        if not done_flag:
            depth = area[len(variables.parameters)]*(2**len(variables.parameters))
            borders = []
            for i,model in zip(range(len(variables.parameters)),models):
                if model in (area[i][0], area[i][1]):
                    half_area = (area[i][1] - area[i][0]) / 2
                    borders.append([[(area[i][0] + half_area), area[i][1]], [area[i][0], (area[i][1] - half_area)]])
                else:
                    borders.append([[model, area[i][1]], [area[i][0], model]])

            cross = itertools.product(*borders, repeat=1)
            for i in cross:
                i = i[:len(variables.parameters)] + (depth,)
                variables.queue.append(i)

    def random_heuristic(self, area):
        depth = area[len(variables.parameters)]*(2**len(variables.parameters))
        borders = []
        for i in range(len(variables.parameters)):
            half_area = random.uniform(area[i][0], area[i][1])
            borders.append([[half_area, area[i][1]], [area[i][0], half_area]])
        cross = itertools.product(*borders, repeat=1)
        for i in cross:
            i = i[:len(variables.parameters)] + (depth,)
            variables.queue.append(i)

    def apply_heuristic(self, area):
        self.dispatcher[current_splitting_heuristic](area)

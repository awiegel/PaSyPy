"""Contains all different splitting heuristics."""

import itertools
import random
import z3

from pasypy import variables
from pasypy import settings
from pasypy.sampling import Sampling


SPLITTING_HEURISTIC = ['Default','Simple','Extended','Random']
current_splitting_heuristic = SPLITTING_HEURISTIC[0] # pylint: disable=C0103 # is not a constant


class SplittingHeuristic:
    """Contains all different splitting heuristics."""

    def __init__(self):
        """Creates a dispatcher for all available splitting heuristics."""
        self.dispatcher = { 'Default' : self.default_heuristic,
                            'Simple'  : self.simple_heuristic,
                            'Extended': self.extended_heuristic,
                            'Random'  : self.random_heuristic
        }

    @staticmethod
    def default_heuristic(area):
        """The Default heuristic.
        It splits every area in exactly 2^dimensions areas.

        :param area: The currently considered area across all dimensions.
        """
        depth = area[len(variables.parameters)]*(2**len(variables.parameters))
        borders = []

        if settings.sampling:
            Sampling().sampling_default(area, borders)
        else:
            for i in range(len(variables.parameters)):
                half_area = (area[i][1] - area[i][0]) / 2
                borders.append([[(area[i][0] + half_area), area[i][1]], [area[i][0], (area[i][1] - half_area)]])
        cross = itertools.product(*borders, repeat=1)
        for i in cross:
            i = i[:len(variables.parameters)] + (depth,)
            variables.queue.append(i)

    @staticmethod
    def simple_heuristic(area):
        """The Simple heuristic.
        It splits every area into two areas, starting with the first dimension and iterating through all.

        :param area: The currently considered area across all dimensions.
        """
        depth = area[len(variables.parameters)]*2
        borders = []
        index = 0
        temp_depth = (depth/2)/2
        while temp_depth >= 1:
            temp_depth /= 2
            index += 1
        index %= len(variables.parameters)

        if settings.sampling:
            Sampling().sampling_simple(area, borders, index)
        else:
            half_area = (area[index][1] - area[index][0]) / 2
            borders.append([area[index][0], (area[index][1] - half_area)])
            borders.append([(area[index][0] + half_area), area[index][1]])
        area1 = list(area)
        area1[index] = borders[0]
        area1[len(variables.parameters)] = depth
        area1 = tuple(area1)
        variables.queue.append(area1)
        area2 = list(area)
        area2[index] = borders[1]
        area2[len(variables.parameters)] = depth
        area2 = tuple(area2)
        variables.queue.append(area2)

    @staticmethod
    def extended_heuristic(area):
        """The Extended heuristic.
        First it gets the model for an unknown area. This is usually the first matching point found by the underlying solver.
        Then this heuristic checks, if splitting on the found point is possible, i.e., the point must not lie on the border.
        Otherwise the Default heuristic has to be used. In general, this heuristic operates similar to the Default heuristic with the difference,
        that no fixed point is used but the underlying solver is exploited to find an appropriate point.

        :param area: The currently considered area across all dimensions.
        """
        models = []
        for value in variables.parameters:
            model = variables.solver.model()[value]
            if isinstance(model, z3.z3.AlgebraicNumRef):
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

    @staticmethod
    def random_heuristic(area):
        """The Random heuristic.
        It operates like the Default heuristic but chooses a random point between the interval on every dimension.

        :param area: The currently considered area across all dimensions.
        """
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
        """Applies the currently selected splitting heuristic on the given area.

        :param area: The currently considered area across all dimensions.
        """
        self.dispatcher[current_splitting_heuristic](area)

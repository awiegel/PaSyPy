"""Optimizes performance by sampling."""

from z3.z3 import RatNumRef
from pasypy import variables


class PreSampling:
    """Optimizes performance by pre-sampling constraints on input."""

    EQUIVALENCE_CLASSES = [['>=','<'],['<=','>'],['==','!=']]
    FACTOR =  0.00000001

    def __init__(self):
        """Initializes the pre-sampling class."""
        self.candidates = []
        self.instructions = []
        self.pre_sampling_length = 0

    def get_pre_sampling_candidate(self, formula):
        """Extracts all pre-sampling candidates.
        A pre-sampling candidate is a single parameter restricted by a number.

        :param formula: The currently considered part of the formula.
        """
        if (formula.num_args() == 2) and (isinstance(formula.children()[0], RatNumRef) != isinstance(formula.children()[1], RatNumRef)):
            self.candidates.append(formula)

    def _create_instructions(self):
        """Creates the instruction list."""
        for i in variables.parameters:
            self.instructions.append([i, []])

    def _add_candidates(self):
        """Adds candidates to the instruction list."""
        for candidate in self.candidates:
            temp = [candidate.decl().name(), (candidate.children()[1].numerator_as_long()/candidate.children()[1].denominator_as_long())]
            for index, value in enumerate(variables.parameters):
                if candidate.children()[0] == value:
                    self.instructions[index][1].append(temp)

    def _sort_values(self):
        """Sorts values on the instruction list."""
        for index, value in enumerate(self.instructions):
            self.instructions[index][1] = sorted(value[1], key=lambda x:x[1])

    def _filter_duplicates(self):
        """Filters duplicates on the instruction list."""
        for parameter in self.instructions:
            last = []
            delete_index = 0
            for index, value in enumerate(parameter[1][:]):
                if last and (value[1] == last[1]):
                    value_index = 0xFF
                    last_index = 0xFF
                    for class_index, equivalence_class in enumerate(self.EQUIVALENCE_CLASSES):
                        if value[0] in equivalence_class:
                            value_index = class_index
                        if last[0] in equivalence_class:
                            last_index = class_index
                    if value_index == last_index:
                        parameter[1].pop(index-delete_index)
                        delete_index += 1
                    else:
                        parameter[1].pop(index-delete_index)
                        parameter[1][index-delete_index-1] = ['==', value[1]]
                        delete_index += 1
                else:
                    last = value

    def _set_depth(self):
        """Sets the depth based on the separated regions."""
        for index, value in enumerate(variables.queue):
            variables.queue[index] = value[:len(variables.parameters)] + (self.pre_sampling_length,)

    def pre_sampling(self):
        """Pre-samples the initial queue on input."""
        self._create_instructions()
        self._add_candidates()
        self._sort_values()
        self._filter_duplicates()
        temp_list = []
        for index, parameter in enumerate(self.instructions):
            for candidate in parameter[1]:
                delete = 0
                for queue_index, element in enumerate(variables.queue[:]):
                    if (candidate[1] >= element[index][0]) and (candidate[1] <= element[index][1]):
                        if candidate[0] in self.EQUIVALENCE_CLASSES[0]:
                            variables.queue.append(element[:index] + ([element[index][0], candidate[1]-self.FACTOR],) + element[index+1:])
                            temp_list.append(element[:index] + ([candidate[1]-self.FACTOR, candidate[1]],) + element[index+1:])
                            variables.queue.append(element[:index] + ([candidate[1], element[index][1]],) + element[index+1:])
                        elif candidate[0] in self.EQUIVALENCE_CLASSES[1]:
                            variables.queue.append(element[:index] + ([element[index][0], candidate[1]],) + element[index+1:])
                            temp_list.append(element[:index] + ([candidate[1], candidate[1]+self.FACTOR],) + element[index+1:])
                            variables.queue.append(element[:index] + ([candidate[1]+self.FACTOR, element[index][1]],) + element[index+1:])
                        else:
                            variables.queue.append(element[:index] + ([element[index][0], candidate[1]-self.FACTOR],) + element[index+1:])
                            temp_list.append(element[:index] + ([candidate[1]-self.FACTOR, candidate[1]+self.FACTOR],) + element[index+1:])
                            variables.queue.append(element[:index] + ([candidate[1]+self.FACTOR, element[index][1]],) + element[index+1:])
                        variables.queue.pop(queue_index-delete)
                        delete += 1
        self.pre_sampling_length = len(variables.queue)
        variables.queue = variables.queue + temp_list
        self._set_depth()


class Sampling:
    """Optimizes performance by sampling before every split."""

    def __init__(self):
        pass

    def sampling_default(self, area, borders):
        """Tries to find a more suitable candidate for splitting on each axis.

        :param area: The currently considered area across all dimensions.
        :param borders: The array where new borders are appended.
        """
        for index, value in enumerate(variables.parameters):
            factor = (area[index][1] - area[index][0]) / 1000
            self.add_mid_points(area, index)
            first_point = (area[index][0] + area[index][1]) / 2
            first_point_status = self.check_point(first_point, index)

            found = False
            test_point_status = self.check_bounds(area[index][0], first_point, value)
            if test_point_status != first_point_status:
                counter = 0
                test_point = first_point
                while counter < 499:
                    test_point -= factor
                    test_point_status = self.check_point(test_point, index)
                    if test_point_status != first_point_status:
                        found = True
                        break
                    counter += 1

            if not found:
                test_point_status = self.check_bounds(first_point, area[index][1], value)
                if test_point_status != first_point_status:
                    counter = 0
                    test_point = first_point
                    while counter < 499:
                        test_point += factor
                        test_point_status = self.check_point(test_point, index)
                        if test_point_status != first_point_status:
                            found = True
                            break
                        counter += 1
            if found:
                borders.append([[area[index][0], test_point], [test_point, area[index][1]]])
            else:
                borders.append([[area[index][0], first_point], [first_point, area[index][1]]])
            self.remove_mid_points()


    def sampling_simple(self, area, borders, index):
        """Tries to find a more suitable candidate for splitting on a single axis.

        :param area: The currently considered area across all dimensions.
        :param borders: The array where new borders are appended.
        :param index: The index of the currently considered parameter.
        """
        factor = (area[index][1] - area[index][0]) / 1000
        self.add_mid_points(area, index)
        first_point = (area[index][0] + area[index][1]) / 2
        first_point_status = self.check_point(first_point, index)

        found = False
        test_point_status = self.check_bounds(area[index][0], first_point, variables.parameters[index])
        if test_point_status != first_point_status:
            counter = 0
            test_point = first_point
            while counter < 499:
                test_point -= factor
                test_point_status = self.check_point(test_point, index)
                if test_point_status != first_point_status:
                    found = True
                    break
                counter += 1

        if not found:
            test_point_status = self.check_bounds(first_point, area[index][1], variables.parameters[index])
            if test_point_status != first_point_status:
                counter = 0
                test_point = first_point
                while counter < 499:
                    test_point += factor
                    test_point_status = self.check_point(test_point, index)
                    if test_point_status != first_point_status:
                        found = True
                        break
                    counter += 1

        self.remove_mid_points()
        if found:
            borders.append([area[index][0], test_point])
            borders.append([test_point, area[index][1]])
        else:
            borders.append([area[index][0], first_point])
            borders.append([first_point, area[index][1]])

    @staticmethod
    def check_bounds(left, right, parameter):
        """Checks a specific interval for satisfiability.

        :param left: The left boundary of the interval.
        :param right: The right boundary of the interval.
        :param parameter: The currently considered parameter.
        :return: The status of the solver check.
        """
        variables.solver.push()
        variables.solver.add(parameter > left)
        variables.solver.add(parameter < right)
        status = variables.solver.check()
        variables.solver.pop()
        return status

    @staticmethod
    def check_point(point, current_index):
        """Checks a specific point for satisfiability.

        :param point: The exact point to check.
        :param current_index: The index of the currently considered parameter.
        :return: The status of the solver check.
        """
        variables.solver.push()
        variables.solver.add(variables.parameters[current_index] == point)
        status = variables.solver.check()
        variables.solver.pop()
        return status

    @staticmethod
    def add_mid_points(area, current_index):
        """Adds the exact middle point on each axis different to the currently considered axis.

        :param area: The currently considered area across all dimensions.
        :param current_index: The index of the currently considered parameter.
        """
        variables.solver.push()
        for index, value in enumerate(variables.parameters):
            if index != current_index:
                variables.solver.add(value == (area[current_index][0] + area[current_index][1])/2)

    @staticmethod
    def remove_mid_points():
        """Removes all middle points."""
        variables.solver.pop()

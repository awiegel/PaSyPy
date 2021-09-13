"""Optimize performance by sampling."""

from z3.z3 import RatNumRef
from pasypy import variables


class PreSampling:
    """Optimize performance by pre-sampling constraints on input."""

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

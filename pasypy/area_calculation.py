"""Calculates the total percentage area."""

from pasypy import variables


class AreaCalculation:
    """Calculates the total percentage area."""

    def __init__(self):
        pass

    @staticmethod
    def calculate_area(area):
        """Calculates the total percentage area.
        Usually given the safe and unsafe area which is both used to calculate the remaining unknown area.

        :param area: The considered area to calculate from. Usually either the total safe area or total unsafe area.
        :return: The total percentage area.
        """
        total_area = 0
        for i in area:
            mult = 1
            for j in range(len(variables.parameters)):
                mult *= (i[j][1]-i[j][0]) / (variables.x_axe_limit[1] - variables.x_axe_limit[0])
            total_area += mult
        return total_area

from pasypy import variables


class AreaCalculation:

    def __init__(self):
        pass

    @staticmethod
    def calculate_area(boxes):
        area = 0
        for i in boxes:
            mult = 1
            for j in range(len(variables.parameters)):
                mult *= (i[j][1]-i[j][0]) / (variables.x_axe_limit[1] - variables.x_axe_limit[0])
            area += mult
        return area

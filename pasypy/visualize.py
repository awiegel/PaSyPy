"""Visualizes all areas."""

import matplotlib.pyplot as plt
import numpy as np
from sklearn import svm

from pasypy import variables, settings, color


class Visualize:
    """Visualizes all areas."""

    def __init__(self):
        """Creates the arrays for the different types of areas and closes all other opened plots."""
        self.safe_area = []
        self.unsafe_area = []
        self.unknown_area = []
        plt.close('all')

    @staticmethod
    def init_graph():
        """Initializes the graph."""
        plt.xlim(variables.x_axe_limit)
        if len(variables.parameters) > 1:
            plt.ylim(variables.y_axe_limit)
        else:
            plt.ylim([0, 1])
            plt.yticks([])

    def filter_depth(self, unfiltered, filtered):
        """Filters already found safe and unsafe areas on decreasing accuracy.

        :param unfiltered: The original unfiltered area.
        :param filtered: The final filtered area.
        """
        for i in unfiltered:
            if i[len(variables.parameters)] <= (2**variables.depth_limit):
                filtered.append(i)
            else:
                self.unknown_area.append(i)

    @staticmethod
    def filter_multiple_axes(temp_boxes, area):
        """Filters duplicate areas on more than two dimensions.

        :param temp_boxes: The original unfiltered area.
        :param area: The final filtered area.
        """
        new_boxes = area
        unique_boxes = []
        unique_boxes_indices = []
        for index, value in enumerate(temp_boxes):
            box = (value[variables.x_axe_position], value[variables.y_axe_position])
            if box not in unique_boxes:
                unique_boxes.append(box)
                unique_boxes_indices.append(index)
        for unique_boxes_index in unique_boxes_indices:
            for index, value in enumerate(temp_boxes):
                if unique_boxes_index == index:
                    new_boxes.append(value)
                    break

    @staticmethod
    def get_hatch_pattern(area_color):
        """Gets the hatch pattern by color of the area.

        :param area_color: The color of the area.
        :return: The corresponding hatch pattern.
        """
        if not settings.hatch_pattern:
            hatch_pattern = ''
        else:
            if area_color == color.safe_color:
                hatch_pattern = 'o'
            elif area_color == color.unsafe_color:
                hatch_pattern = 'x'
            else:
                hatch_pattern = ''
        return hatch_pattern

    def plot_one_dimensional(self, area, area_color):
        """Plots constraints with only one dimension.
        The x-axis represents the only parameter and the y-axis is fixed around the center point.
        If active applies a hatch pattern for better distinction between safe and unsafe area.

        :param area: The area to plot.
        :param area_color: The color of the area.
        """
        hatch_pattern = self.get_hatch_pattern(area_color)
        for i in area:
            plt.plot([i[0][0],i[0][1],i[0][1],i[0][0],i[0][0]], [0.4, 0.4, 0.6, 0.6, 0.4], color='black')
            plt.fill([i[0][0],i[0][1],i[0][1],i[0][0],i[0][0]], [0.4, 0.4, 0.6, 0.6, 0.4], color=area_color, edgecolor='black', linewidth=0, hatch=hatch_pattern)

    def plot_multi_dimensional(self, area, area_color):
        """Plots constraints with only one dimension.
        The x-axis represents the first selected parameter and the y-axis the second selected parameter.
        If active applies a hatch pattern for better distinction between safe and unsafe area.

        :param area: The area to plot.
        :param area_color: The color of the area.
        """
        hatch_pattern = self.get_hatch_pattern(area_color)
        for i in area:
            plt.plot([i[variables.x_axe_position][0],i[variables.x_axe_position][1],i[variables.x_axe_position][1],i[variables.x_axe_position][0],i[variables.x_axe_position][0]],
                    [i[variables.y_axe_position][0],i[variables.y_axe_position][0],i[variables.y_axe_position][1],i[variables.y_axe_position][1],i[variables.y_axe_position][0]],
                    color='black')
            plt.fill([i[variables.x_axe_position][0],i[variables.x_axe_position][1],i[variables.x_axe_position][1],i[variables.x_axe_position][0],i[variables.x_axe_position][0]],
                    [i[variables.y_axe_position][0],i[variables.y_axe_position][0],i[variables.y_axe_position][1],i[variables.y_axe_position][1],i[variables.y_axe_position][0]],
                    color=area_color, edgecolor='black', linewidth=0, hatch=hatch_pattern)

    @staticmethod
    def plot_multi_dimensional_without_fill(area):
        """Plots unknown area on multiple dimensions.

        :param area: The area to plot.
        """
        for i in area:
            plt.plot([i[variables.x_axe_position][0],i[variables.x_axe_position][1],i[variables.x_axe_position][1],i[variables.x_axe_position][0],i[variables.x_axe_position][0]],
                    [i[variables.y_axe_position][0],i[variables.y_axe_position][0],i[variables.y_axe_position][1],i[variables.y_axe_position][1],i[variables.y_axe_position][0]],
                    color='black')

    def draw_green_area(self):
        """Draws the safe (green by default) area. Filters on more than two parameters with the order: safe > unknown > unsafe."""
        safe_area_depth_filtered = []
        self.filter_depth(variables.safe_area, safe_area_depth_filtered)
        if len(variables.parameters) == 1:
            self.safe_area = safe_area_depth_filtered.copy()
            self.plot_one_dimensional(safe_area_depth_filtered, color.safe_color)
        else:
            if len(variables.parameters) == 2:
                self.safe_area = safe_area_depth_filtered.copy()
                self.plot_multi_dimensional(self.safe_area, color.safe_color)
            else:
                self.safe_area = []
                temp = safe_area_depth_filtered.copy()
                for sub_area in safe_area_depth_filtered[:]:
                    for sub_area2 in safe_area_depth_filtered[:]:
                        if (((sub_area2[variables.x_axe_position][0] >= sub_area[variables.x_axe_position][0]) and (sub_area2[variables.x_axe_position][1] <= sub_area[variables.x_axe_position][1])) and \
                            ((sub_area2[variables.y_axe_position][0] >= sub_area[variables.y_axe_position][0]) and (sub_area2[variables.y_axe_position][1] <= sub_area[variables.y_axe_position][1]))) and \
                            (((sub_area2[variables.x_axe_position][0] != sub_area[variables.x_axe_position][0]) or (sub_area2[variables.x_axe_position][1] != sub_area[variables.x_axe_position][1])) or \
                            ((sub_area2[variables.y_axe_position][0] != sub_area[variables.y_axe_position][0]) or (sub_area2[variables.y_axe_position][1] != sub_area[variables.y_axe_position][1]))):
                            temp.remove(sub_area)
                            break
                self.filter_multiple_axes(temp, self.safe_area)
                self.plot_multi_dimensional(self.safe_area, color.safe_color)

    def draw_red_area(self):
        """Draws the unsafe (red by default) area. Filters on more than two parameters with the order: safe > unknown > unsafe."""
        unsafe_area_depth_filtered = []
        self.filter_depth(variables.unsafe_area, unsafe_area_depth_filtered)
        if len(variables.parameters) == 1:
            self.unsafe_area = unsafe_area_depth_filtered.copy()
            self.plot_one_dimensional(unsafe_area_depth_filtered, color.unsafe_color)
        else:
            if len(variables.parameters) == 2:
                self.unsafe_area = unsafe_area_depth_filtered.copy()
                self.plot_multi_dimensional(self.unsafe_area, color.unsafe_color)
            else:
                self.unsafe_area = []
                temp = unsafe_area_depth_filtered.copy()
                for sub_area in unsafe_area_depth_filtered[:]:
                    for sub_area_sub_queue in variables.sub_queue:
                        if ((sub_area_sub_queue[variables.x_axe_position][0] >= sub_area[variables.x_axe_position][0]) and (sub_area_sub_queue[variables.x_axe_position][1] <= sub_area[variables.x_axe_position][1])) and \
                            ((sub_area_sub_queue[variables.y_axe_position][0] >= sub_area[variables.y_axe_position][0]) and (sub_area_sub_queue[variables.y_axe_position][1] <= sub_area[variables.y_axe_position][1])):
                            temp.remove(sub_area)
                            break
                self.filter_multiple_axes(temp, self.unsafe_area)
                self.plot_multi_dimensional(self.unsafe_area, color.unsafe_color)

    def draw_white_area(self):
        """Draws the unknown (white) area. Filters on more than two parameters with the order: safe > unknown > unsafe."""
        if len(variables.parameters) == 1:
            white_boxes = variables.sub_queue.copy() + self.unknown_area.copy()
            self.plot_one_dimensional(white_boxes, 'white')
        else:
            if len(variables.parameters) == 2:
                white_boxes = variables.sub_queue.copy() + self.unknown_area.copy()
                self.plot_multi_dimensional(white_boxes, 'white')
            else:
                white_boxes = variables.sub_queue.copy() + variables.safe_area.copy() + variables.unsafe_area.copy()
                for unknown_area in white_boxes[:]:
                    for safe_area in variables.safe_area:
                        if ((unknown_area[variables.x_axe_position][0] >= safe_area[variables.x_axe_position][0]) and (unknown_area[variables.x_axe_position][1] <= safe_area[variables.x_axe_position][1])) and \
                            ((unknown_area[variables.y_axe_position][0] >= safe_area[variables.y_axe_position][0]) and (unknown_area[variables.y_axe_position][1] <= safe_area[variables.y_axe_position][1])) and safe_area != unknown_area:
                            white_boxes.remove(unknown_area)
                            break
                temp = []
                for unknown_area in white_boxes:
                    for index, _ in enumerate(unknown_area):
                        if index == (len(unknown_area) - 1):
                            unknown_area = list(unknown_area)
                            unknown_area[index] = 0
                            unknown_area = tuple(unknown_area)
                        elif index not in (variables.x_axe_position, variables.y_axe_position):
                            unknown_area = list(unknown_area)
                            unknown_area[index] = []
                            unknown_area = tuple(unknown_area)
                        else:
                            pass
                    temp.append(unknown_area)
                temp_unique = ()
                for unknown_area in temp:
                    if unknown_area not in temp_unique:
                        temp_unique += (unknown_area,)
                self.plot_multi_dimensional_without_fill(temp_unique)

    def draw_hyperplane(self, ax):
        """Draws the (fake) hyperplane.
        This is actually a support vector machine created based on the safe and unsafe area as training data sets.
        Only works for constraints with more than one parameter.

        :param ax: The fundamental of the graph.
        """
        X = []
        Y = []
        for i in self.safe_area:
            for x_pos in range(2):
                for y_pos in range(2):
                    X.append([i[variables.x_axe_position][x_pos],i[variables.y_axe_position][y_pos]])
                    Y.append(0)
        for i in self.unsafe_area:
            for x_pos in range(2):
                for y_pos in range(2):
                    X.append([i[variables.x_axe_position][x_pos],i[variables.y_axe_position][y_pos]])
                    Y.append(1)
        if 0 in Y and 1 in Y:
            clf = svm.SVC(kernel='rbf', C=1000)
            clf.fit(X, Y)
            xlim = ax.get_xlim()
            ylim = ax.get_ylim()
            xx = np.linspace(xlim[0], xlim[1], 30)
            yy = np.linspace(ylim[0], ylim[1], 30)
            YY, XX = np.meshgrid(yy, xx)
            xy = np.vstack([XX.ravel(), YY.ravel()]).T
            Z = clf.decision_function(xy).reshape(XX.shape)
            # plot decision boundary and margins
            # plot support vectors
            ax.contour(XX, YY, Z, colors='b', levels=[-1, 0, 1], alpha=0.5, linestyles=['--', '-', '--'])

    @staticmethod
    def on_xlims_change(event_ax):
        """Reports changes of the considered x-axis, f.e., by zooming or moving.

        :param event_ax: Event listener for the watched axis.
        """
        variables.x_axe_limit_temp = event_ax.get_xlim()

    @staticmethod
    def on_ylims_change(event_ax):
        """Reports changes of the considered y-axis, f.e., by zooming or moving.

        :param event_ax: Event listener for the watched axis.
        """
        variables.y_axe_limit_temp = event_ax.get_ylim()

    def generate_graph(self):
        """Generates the complete graph by calling every relevant function in appropriate order.

        :return: The created graph.
        """
        figure = plt.figure()
        self.init_graph()
        self.draw_red_area()
        self.draw_green_area()
        if settings.white_boxes:
            self.draw_white_area()
        ax = plt.gca()
        ax.callbacks.connect('xlim_changed', self.on_xlims_change)
        ax.callbacks.connect('ylim_changed', self.on_ylims_change)
        variables.x_axe_limit_temp = variables.x_axe_limit
        variables.y_axe_limit_temp = variables.y_axe_limit
        if (len(variables.parameters) > 1) and settings.hyperplane:
            self.draw_hyperplane(ax)
        return figure

import os

import matplotlib.pyplot as plt
import numpy as np
from sklearn import svm

from pasypy import variables
from pasypy import settings


class Visualize:
    
    def __init__(self):
        self.GS = []
        self.RS = []
        self.WS = []
        
        
    def init_graph(self):
        plt.xlim(variables.x_axe_limit)
        if len(variables.parameters) > 1:
            plt.ylim(variables.y_axe_limit)
        else:
            plt.ylim([0, 1])
            plt.yticks([])


    def create_logfile(self, name, B):
        logfile = open('logs/{}.log'.format(name), 'w')
        for variable in variables.parameters:
            logfile.write('----- {} -----'.format(str(variable)))
        logfile.write('\n')

        for b in B:
            logfile.write(str(b) + '\n')

        logfile.close()


    def create_logfiles(self):
        self.create_logfile('safe_area', variables.G)
        self.create_logfile('unsafe_area', variables.R)


    def filter_depth(self, unfiltered, filtered):
        for i in unfiltered:
            if (i[len(variables.parameters)] <= ((2**variables.depth_limit))):
                filtered.append(i)
            else:
                self.WS.append(i)


    def filter_multiple_axes(self, temp_boxes, color):
        new_boxes = color

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


    def get_hatch_pattern(self, area_color):
        if not settings.hatch_pattern:
            hatch_pattern = ''
        else:
            if area_color == settings.safe_color:
                hatch_pattern = 'o'
            elif area_color == settings.unsafe_color:
                hatch_pattern = 'x'
            else:
                hatch_pattern = ''
        return hatch_pattern


    def plot_one_dimensional(self, area, area_color):
        hatch_pattern = self.get_hatch_pattern(area_color)
        for i in area:
            plt.plot([i[0][0],i[0][1],i[0][1],i[0][0],i[0][0]], [0.4, 0.4, 0.6, 0.6, 0.4], color='black')
            plt.fill([i[0][0],i[0][1],i[0][1],i[0][0],i[0][0]], [0.4, 0.4, 0.6, 0.6, 0.4], color=area_color, edgecolor='black', linewidth=0, hatch=hatch_pattern)


    def plot_multi_dimensional(self, area, area_color):
        hatch_pattern = self.get_hatch_pattern(area_color)
        for i in area:
            plt.plot([i[variables.x_axe_position][0],i[variables.x_axe_position][1],i[variables.x_axe_position][1],i[variables.x_axe_position][0],i[variables.x_axe_position][0]],
                    [i[variables.y_axe_position][0],i[variables.y_axe_position][0],i[variables.y_axe_position][1],i[variables.y_axe_position][1],i[variables.y_axe_position][0]],
                    color='black')
            plt.fill([i[variables.x_axe_position][0],i[variables.x_axe_position][1],i[variables.x_axe_position][1],i[variables.x_axe_position][0],i[variables.x_axe_position][0]],
                    [i[variables.y_axe_position][0],i[variables.y_axe_position][0],i[variables.y_axe_position][1],i[variables.y_axe_position][1],i[variables.y_axe_position][0]],
                    color=area_color, edgecolor='black', linewidth=0, hatch=hatch_pattern)

    def plot_multi_dimensional2(self, area):
        for i in area:
            plt.plot([i[variables.x_axe_position][0],i[variables.x_axe_position][1],i[variables.x_axe_position][1],i[variables.x_axe_position][0],i[variables.x_axe_position][0]],
                    [i[variables.y_axe_position][0],i[variables.y_axe_position][0],i[variables.y_axe_position][1],i[variables.y_axe_position][1],i[variables.y_axe_position][0]],
                    color='black')


    def draw_green_area(self):
        G_depth_filtered = []
        self.filter_depth(variables.G, G_depth_filtered)

        if len(variables.parameters) == 1:
            self.GS = G_depth_filtered.copy()
            self.plot_one_dimensional(G_depth_filtered, settings.safe_color)
        else:
            if len(variables.parameters) == 2:
                self.GS = G_depth_filtered.copy()
                self.plot_multi_dimensional(self.GS, settings.safe_color)
            else:
                self.GS = []
                temp = G_depth_filtered.copy()
                for g in G_depth_filtered[:]:
                    for gg in G_depth_filtered[:]:
                        if (((gg[variables.x_axe_position][0] >= g[variables.x_axe_position][0]) and (gg[variables.x_axe_position][1] <= g[variables.x_axe_position][1])) and \
                            ((gg[variables.y_axe_position][0] >= g[variables.y_axe_position][0]) and (gg[variables.y_axe_position][1] <= g[variables.y_axe_position][1]))) and \
                            (((gg[variables.x_axe_position][0] != g[variables.x_axe_position][0]) or (gg[variables.x_axe_position][1] != g[variables.x_axe_position][1])) or \
                            ((gg[variables.y_axe_position][0] != g[variables.y_axe_position][0]) or (gg[variables.y_axe_position][1] != g[variables.y_axe_position][1]))):
                            try:
                                temp.remove(gg)
                            except:
                                pass
                
                self.filter_multiple_axes(temp, self.GS)
                self.plot_multi_dimensional(self.GS, settings.safe_color)


        self.create_logfile('safe_area', variables.G)


    def draw_red_area(self):
        R_depth_filtered = []
        self.filter_depth(variables.R, R_depth_filtered)

        if len(variables.parameters) == 1:
            self.RS = R_depth_filtered.copy()
            self.plot_one_dimensional(R_depth_filtered, settings.unsafe_color)
        else:
            if len(variables.parameters) == 2:
                self.RS = R_depth_filtered.copy()
                self.plot_multi_dimensional(self.RS, settings.unsafe_color)

            else:
                self.RS = []
                temp = R_depth_filtered.copy()
                for r in R_depth_filtered[:]:
                    for w in variables.Sub_Queue:
                        if ((w[variables.x_axe_position][0] >= r[variables.x_axe_position][0]) and (w[variables.x_axe_position][1] <= r[variables.x_axe_position][1])) and \
                            ((w[variables.y_axe_position][0] >= r[variables.y_axe_position][0]) and (w[variables.y_axe_position][1] <= r[variables.y_axe_position][1])):
                            try:
                                temp.remove(r)
                            except:
                                pass

                self.filter_multiple_axes(temp, self.RS)
                self.plot_multi_dimensional(self.RS, settings.unsafe_color)


        self.create_logfile('unsafe_area', variables.R)


    def draw_white_area(self):
        if len(variables.parameters) == 1:
            white_boxes = variables.Sub_Queue + self.WS
            self.plot_one_dimensional(white_boxes, 'white')
        else:
            if len(variables.parameters) == 2:
                white_boxes = variables.Sub_Queue + self.WS
                self.plot_multi_dimensional(white_boxes, 'white')
            else:
                white_boxes = variables.Sub_Queue
                for w in white_boxes[:]:
                    for g in self.GS:
                        if ((w[variables.x_axe_position][0] >= g[variables.x_axe_position][0]) and (w[variables.x_axe_position][1] <= g[variables.x_axe_position][1])) and \
                            ((w[variables.y_axe_position][0] >= g[variables.y_axe_position][0]) and (w[variables.y_axe_position][1] <= g[variables.y_axe_position][1])):
                            white_boxes.remove(w)
                    for g in self.RS:
                        if ((w[variables.x_axe_position][0] >= g[variables.x_axe_position][0]) and (w[variables.x_axe_position][1] <= g[variables.x_axe_position][1])) and \
                            ((w[variables.y_axe_position][0] >= g[variables.y_axe_position][0]) and (w[variables.y_axe_position][1] <= g[variables.y_axe_position][1])):
                            white_boxes.remove(w)
                
                test = []
                for i in white_boxes:
                    for x in range(len(i)):
                        if x == (len(i) - 1):
                            i = list(i)
                            i[x] = 0
                            i = tuple(i)
                        elif x != variables.x_axe_position and x != variables.y_axe_position:
                            i = list(i)
                            i[x] = []
                            i = tuple(i)
                        else:
                            pass
                    test.append(i)
                b = ()
                for sublist in test:
                    if sublist not in b:
                        b += (sublist,)
                self.plot_multi_dimensional2(b)
                

    def draw_hyperplane(self, ax):
        X = []
        Y = []

        for i in self.GS:
            for x_pos in range(2):
                for y_pos in range(2):
                    X.append([i[variables.x_axe_position][x_pos],i[variables.y_axe_position][y_pos]])
                    Y.append(0)
        
        for i in self.RS:
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
            # plt instead of ax
            ax.contour(XX, YY, Z, colors='b', levels=[-1, 0, 1], alpha=0.5, linestyles=['--', '-', '--'])
            # plot support vectors
            # ax.scatter(clf.support_vectors_[:, 0], clf.support_vectors_[:, 1], s=100, linewidth=1, facecolors='none', edgecolors='k')


    def on_xlims_change(self, event_ax):
        variables.x_axe_limit_temp = event_ax.get_xlim()

    def on_ylims_change(self, event_ax):
        variables.y_axe_limit_temp = event_ax.get_ylim()


    # Complete visualization part
    def generate_graph(self):
        self.WS.clear()

        plt.close('all')
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
        if (len(variables.parameters) > 1) and settings.show_hyperplane:
            self.draw_hyperplane(ax)
        return figure


    def show_graph(self):
        plt.show()

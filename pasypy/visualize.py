import os

import matplotlib.pyplot as plt
import numpy as np
from sklearn import svm

from pasypy import variables


GS = []
RS = []


def init_graph():
    plt.xlim(variables.x_axe_limit)
    if len(variables.parameters) > 1:
        plt.ylim(variables.y_axe_limit)
    else:
        plt.ylim([0, 1])
        plt.yticks([])


def create_logfile(name, B):
    if not os.path.exists('logs'):
        os.makedirs('logs')
    logfile = open('logs/{}.log'.format(name), 'w')
    for variable in variables.parameters:
        logfile.write('----- {} -----'.format(str(variable)))
    logfile.write('\n')

    for b in B:
        logfile.write(str(b) + '\n')

    logfile.close()


def filter_depth(unfiltered, filtered):
    for i in unfiltered:
        if (i[len(variables.parameters)] < ((2**variables.depth_limit)/2)):
            filtered.append(i) 


def filter_multiple_axes(temp_boxes, color):
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


def plot_one_dimensional(area, area_color):
    for i in area:
        plt.plot([i[0][0],i[0][1],i[0][1],i[0][0],i[0][0]], [0.4, 0.4, 0.6, 0.6, 0.4], color='black')
        plt.fill([i[0][0],i[0][1],i[0][1],i[0][0],i[0][0]], [0.4, 0.4, 0.6, 0.6, 0.4], color=area_color)

def plot_multi_dimensional(area, area_color):
    for i in area:
        plt.plot([i[variables.x_axe_position][0],i[variables.x_axe_position][1],i[variables.x_axe_position][1],i[variables.x_axe_position][0],i[variables.x_axe_position][0]],
                 [i[variables.y_axe_position][0],i[variables.y_axe_position][0],i[variables.y_axe_position][1],i[variables.y_axe_position][1],i[variables.y_axe_position][0]],
                 color='black')
        plt.fill([i[variables.x_axe_position][0],i[variables.x_axe_position][1],i[variables.x_axe_position][1],i[variables.x_axe_position][0],i[variables.x_axe_position][0]],
                 [i[variables.y_axe_position][0],i[variables.y_axe_position][0],i[variables.y_axe_position][1],i[variables.y_axe_position][1],i[variables.y_axe_position][0]],
                 color=area_color)

def draw_green_area():
    global GS

    G_depth_filtered = []
    filter_depth(variables.G, G_depth_filtered)

    if len(variables.parameters) == 1:
        GS = G_depth_filtered.copy()
        plot_one_dimensional(G_depth_filtered, 'forestgreen')
    else:
        if len(variables.parameters) == 2:
            GS = G_depth_filtered.copy()
            plot_multi_dimensional(GS, 'forestgreen')
        else:
            GS = []
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
            
            filter_multiple_axes(temp, GS)
            plot_multi_dimensional(GS, 'forestgreen')


    create_logfile('safe_area', variables.G)


def draw_red_area():
    global RS

    R_depth_filtered = []
    filter_depth(variables.R, R_depth_filtered)

    if len(variables.parameters) == 1:
        RS = R_depth_filtered.copy()
        plot_one_dimensional(R_depth_filtered, 'firebrick')
    else:
        if len(variables.parameters) == 2:
            RS = R_depth_filtered.copy()
            plot_multi_dimensional(RS, 'firebrick')

        else:
            RS = []
            temp = R_depth_filtered.copy()
            for r in R_depth_filtered[:]:
                for w in variables.Sub_Queue:
                    if ((w[variables.x_axe_position][0] >= r[variables.x_axe_position][0]) and (w[variables.x_axe_position][1] <= r[variables.x_axe_position][1])) and \
                        ((w[variables.y_axe_position][0] >= r[variables.y_axe_position][0]) and (w[variables.y_axe_position][1] <= r[variables.y_axe_position][1])):
                        try:
                            temp.remove(r)
                        except:
                            pass

            filter_multiple_axes(temp, RS)
            plot_multi_dimensional(RS, 'firebrick')


    create_logfile('unsafe_area', variables.R)


def draw_hyperplane():
    X = []
    Y = []

    for i in GS:
        for x_pos in range(2):
            for y_pos in range(2):
                X.append([i[variables.x_axe_position][x_pos],i[variables.y_axe_position][y_pos]])
                Y.append(0)
    
    for i in RS:
        for x_pos in range(2):
            for y_pos in range(2):
                X.append([i[variables.x_axe_position][x_pos],i[variables.y_axe_position][y_pos]])
                Y.append(1)

    if 0 in Y and 1 in Y:
        clf = svm.SVC(kernel='rbf', C=1000)
        clf.fit(X, Y)
        ax = plt.gca()
        ax.callbacks.connect('xlim_changed', on_xlims_change)
        ax.callbacks.connect('ylim_changed', on_ylims_change)
        xlim = ax.get_xlim()
        ylim = ax.get_ylim()
        variables.x_axe_limit_temp = variables.x_axe_limit
        variables.y_axe_limit_temp = variables.y_axe_limit
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


def on_xlims_change(event_ax):
    print("updated xlims: ", event_ax.get_xlim())
    variables.x_axe_limit_temp = event_ax.get_xlim()

def on_ylims_change(event_ax):
    print("updated ylims: ", event_ax.get_ylim())
    variables.y_axe_limit_temp = event_ax.get_ylim()


# Complete visualization part
def generate_graph():
    plt.close('all')
    figure = plt.figure()
    init_graph()
    draw_green_area()
    draw_red_area()
    if len(variables.parameters) > 1:
        draw_hyperplane()
    return figure


def show_graph():
    plt.show()

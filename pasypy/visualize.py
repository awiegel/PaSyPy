import matplotlib.pyplot as plt
import numpy as np
from sklearn import svm
from colorama import Fore, Style
import timeit
import os

import variables

from gui import *
from pasypy import calculate_area


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


def draw_green_area():
    global GS

    GS = variables.G.copy()
    if len(variables.parameters) == 1:
        for g in variables.G[:]:
            for gg in variables.G[:]:
                if ((gg[variables.x_axe_position][0] >= g[variables.x_axe_position][0]) and (gg[variables.x_axe_position][1] <= g[variables.x_axe_position][1])) and \
                    ((gg[variables.x_axe_position][0] != g[variables.x_axe_position][0]) or (gg[variables.x_axe_position][1] != g[variables.x_axe_position][1])):
                    try:
                        GS.remove(gg)
                    except:
                        pass
        for g in GS:
            plt.plot([g[variables.x_axe_position][0],g[variables.x_axe_position][1],g[variables.x_axe_position][1],g[variables.x_axe_position][0],g[variables.x_axe_position][0]], [0.4, 0.4, 0.6, 0.6, 0.4], color='black')
            plt.fill([g[variables.x_axe_position][0],g[variables.x_axe_position][1],g[variables.x_axe_position][1],g[variables.x_axe_position][0],g[variables.x_axe_position][0]], [0.4, 0.4, 0.6, 0.6, 0.4], color='forestgreen')
    else:
        for g in variables.G[:]:
            for gg in variables.G[:]:
                if (((gg[variables.x_axe_position][0] >= g[variables.x_axe_position][0]) and (gg[variables.x_axe_position][1] <= g[variables.x_axe_position][1])) and \
                    ((gg[variables.y_axe_position][0] >= g[variables.y_axe_position][0]) and (gg[variables.y_axe_position][1] <= g[variables.y_axe_position][1]))) and \
                    (((gg[variables.x_axe_position][0] != g[variables.x_axe_position][0]) or (gg[variables.x_axe_position][1] != g[variables.x_axe_position][1])) or \
                    ((gg[variables.y_axe_position][0] != g[variables.y_axe_position][0]) or (gg[variables.y_axe_position][1] != g[variables.y_axe_position][1]))):
                    try:
                        GS.remove(gg)
                    except:
                        pass
        for g in GS:
            plt.plot([g[variables.x_axe_position][0],g[variables.x_axe_position][1],g[variables.x_axe_position][1],g[variables.x_axe_position][0],g[variables.x_axe_position][0]],
                    [g[variables.y_axe_position][0],g[variables.y_axe_position][0],g[variables.y_axe_position][1],g[variables.y_axe_position][1],g[variables.y_axe_position][0]], color='black')
            plt.fill([g[variables.x_axe_position][0],g[variables.x_axe_position][1],g[variables.x_axe_position][1],g[variables.x_axe_position][0],g[variables.x_axe_position][0]],
                    [g[variables.y_axe_position][0],g[variables.y_axe_position][0],g[variables.y_axe_position][1],g[variables.y_axe_position][1],g[variables.y_axe_position][0]], color='forestgreen')

    create_logfile('safe_area', variables.G)

    print(Fore.GREEN + 'G: ', variables.G)
    print('Number of green boxes: ', len(variables.G))
    print(Style.RESET_ALL)


def draw_red_area():
    global RS

    RS = variables.R.copy()
    if len(variables.parameters) == 1:
        for r in variables.R[:]:
            for w in variables.Sub_Queue:
                if ((w[variables.x_axe_position][0] >= r[variables.x_axe_position][0]) and (w[variables.x_axe_position][1] <= r[variables.x_axe_position][1])):
                    try:
                        RS.remove(r)
                    except:
                        pass

        for r in RS:
            plt.plot([r[variables.x_axe_position][0],r[variables.x_axe_position][1],r[variables.x_axe_position][1],r[variables.x_axe_position][0],r[variables.x_axe_position][0]], [0.4, 0.4, 0.6, 0.6, 0.4], color='black')
            plt.fill([r[variables.x_axe_position][0],r[variables.x_axe_position][1],r[variables.x_axe_position][1],r[variables.x_axe_position][0],r[variables.x_axe_position][0]], [0.4, 0.4, 0.6, 0.6, 0.4], color='firebrick')
    else:
        for r in variables.R[:]:
            for w in variables.Sub_Queue:
                if ((w[variables.x_axe_position][0] >= r[variables.x_axe_position][0]) and (w[variables.x_axe_position][1] <= r[variables.x_axe_position][1])) and \
                    ((w[variables.y_axe_position][0] >= r[variables.y_axe_position][0]) and (w[variables.y_axe_position][1] <= r[variables.y_axe_position][1])):
                    try:
                        RS.remove(r)
                    except:
                        pass

        for r in RS:
            plt.plot([r[variables.x_axe_position][0],r[variables.x_axe_position][1],r[variables.x_axe_position][1],r[variables.x_axe_position][0],r[variables.x_axe_position][0]],
                    [r[variables.y_axe_position][0],r[variables.y_axe_position][0],r[variables.y_axe_position][1],r[variables.y_axe_position][1],r[variables.y_axe_position][0]], color='black')
            plt.fill([r[variables.x_axe_position][0],r[variables.x_axe_position][1],r[variables.x_axe_position][1],r[variables.x_axe_position][0],r[variables.x_axe_position][0]],
                    [r[variables.y_axe_position][0],r[variables.y_axe_position][0],r[variables.y_axe_position][1],r[variables.y_axe_position][1],r[variables.y_axe_position][0]], color='firebrick')

    create_logfile('unsafe_area', variables.R)

    print(Fore.RED + 'R: ', variables.R)
    print('Number of red boxes: ', len(variables.R))
    print(Style.RESET_ALL)


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
        app.ax = plt.gca()
        app.ax.callbacks.connect('xlim_changed', on_xlims_change)
        app.ax.callbacks.connect('ylim_changed', on_ylims_change)
        xlim = app.ax.get_xlim()
        ylim = app.ax.get_ylim()
        app.global_xlim = variables.x_axe_limit
        app.global_ylim = variables.y_axe_limit
        xx = np.linspace(xlim[0], xlim[1], 30)
        yy = np.linspace(ylim[0], ylim[1], 30)
        YY, XX = np.meshgrid(yy, xx)
        xy = np.vstack([XX.ravel(), YY.ravel()]).T
        Z = clf.decision_function(xy).reshape(XX.shape)
        # plot decision boundary and margins
        # plt instead of ax
        app.ax.contour(XX, YY, Z, colors='b', levels=[-1, 0, 1], alpha=0.5,
                   linestyles=['--', '-', '--'])
        # plot support vectors
        # ax.scatter(clf.support_vectors_[:, 0], clf.support_vectors_[:, 1], s=100,
        # linewidth=1, facecolors='none', edgecolors='k')


def on_xlims_change(event_ax):
    print("updated xlims: ", event_ax.get_xlim())
    app.global_xlim = event_ax.get_xlim()

def on_ylims_change(event_ax):
    print("updated ylims: ", event_ax.get_ylim())
    app.global_ylim = event_ax.get_ylim()


# Complete visualization part
def generate_graph():
    figure = plt.figure()
    init_graph()
    draw_green_area()
    draw_red_area()
    if len(variables.parameters) > 1:
        draw_hyperplane()
    app.add_plot(figure)


def show_graph():
    plt.show()


def show_progress():
    green_area = calculate_area(variables.G)
    red_area = calculate_area(variables.R)
    print(Fore.GREEN + 'Green area:', '{:.2%}'.format(green_area), Fore.RED + '    Red area:', '{:.2%}'.format(red_area),
          Fore.WHITE + '    White area left:', '{:.2%}'.format(1 - (green_area + red_area)))


def create_timestamp(name, timestamps):
    timestamp = timeit.default_timer()
    for i in timestamps.values():
        timestamp -= i
    timestamps.update({name: timestamp})


def show_time(timestamps):
    total_time = 0
    max_name_len = len(max(timestamps, key=len))
    for i in timestamps:
        if i != 'Start Time':
            print('{}{} :'.format(i, (' ' * (max_name_len-len(i)))), round(timestamps[i], 3), 'sec.')
            total_time += round(timestamps[i], 3)
        if i == 'Computation Time':
            app.time1.config(text='{}{} : {} sec.'.format(i, (' ' * (max_name_len-len(i))), round(timestamps[i], 3)))
        elif i == 'Visualization Time':
            app.time2.config(text='{}{} : {} sec.'.format(i, (2 * ' ' * (max_name_len-len(i))), round(timestamps[i], 3)))
    print('Total Time{} :'.format(' ' * (max_name_len-len('Total Time'))), round(total_time, 3), 'sec.')
    app.time3.config(text='Total Time{} : {} sec.'.format((2 * ' ' * (max_name_len-len('Total Time'))), round(total_time, 3)))

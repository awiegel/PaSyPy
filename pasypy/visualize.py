import matplotlib.pyplot as plt
import numpy as np
from sklearn import svm
from colorama import Fore, Style
import timeit
import os

import variables

from gui import *
from pasypy import calculate_area


def init_graph():
    plt.xlim([0, 1.0])
    plt.ylim([0, 1.0])


def create_logfile(name):
    if not os.path.exists('logs'):
        os.makedirs('logs')
    logfile = open('logs/{}.log'.format(name), 'w')
    for variable in variables.parameters:
        logfile.write('----- {} -----'.format(str(variable)))
    logfile.write('\n')
    return logfile


def draw_green_area():
    logfile = create_logfile('safe_area')

    for g in variables.G:
        plt.plot([g[0][0], g[0][1], g[0][1], g[0][0], g[0][0]],
                 [g[1][0], g[1][0], g[1][1], g[1][1], g[1][0]], color='black')
        plt.fill([g[0][0], g[0][1], g[0][1], g[0][0], g[0][0]],
                 [g[1][0], g[1][0], g[1][1], g[1][1], g[1][0]], color='limegreen')
        logfile.write(str(g) + '\n')
    logfile.close()

    print(Fore.GREEN + 'G: ', variables.G)
    print('Number of green boxes: ', len(variables.G))
    print(Style.RESET_ALL)


def draw_red_area():
    logfile = create_logfile('unsafe_area')

    for r in variables.R:
        plt.plot([r[0][0], r[0][1], r[0][1], r[0][0], r[0][0]],
                 [r[1][0], r[1][0], r[1][1], r[1][1], r[1][0]], color='black')
        plt.fill([r[0][0], r[0][1], r[0][1], r[0][0], r[0][0]],
                 [r[1][0], r[1][0], r[1][1], r[1][1], r[1][0]], color='red')
        logfile.write(str(r) + '\n')
    logfile.close()

    print(Fore.RED + 'R: ', variables.R)
    print('Number of red boxes: ', len(variables.R))
    print(Style.RESET_ALL)


def draw_hyperplane():
    X = []
    Y = []
    for i in variables.G:
        X.append([i[0][0], i[1][0]])
        X.append([i[0][1], i[1][1]])
        Y.append(0)
        Y.append(0)

    for i in variables.R:
        X.append([i[0][0], i[1][0]])
        X.append([i[0][1], i[1][1]])
        Y.append(1)
        Y.append(1)

    if 0 in Y and 1 in Y:
        clf = svm.SVC(kernel='rbf', C=1000)
        clf.fit(X, Y)
        app.ax = plt.gca()
        app.ax.callbacks.connect('xlim_changed', on_xlims_change)
        app.ax.callbacks.connect('ylim_changed', on_ylims_change)
        xlim = app.ax.get_xlim()
        ylim = app.ax.get_ylim()
        app.global_xlim = (0.0, 1.0)
        app.global_ylim = (0.0, 1.0)
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



def main():
    None


if __name__ == "__main__":
    main()

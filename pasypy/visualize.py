import matplotlib.pyplot as plt
import numpy as np
from sklearn import svm
from colorama import Fore, Style
import timeit
import os

from variables import *
from pasypy import calculate_area


def init_graph():
    plt.xlim([0, 1.0])
    plt.ylim([0, 1.0])


def create_logfile(name):
    if not os.path.exists('logs'):
        os.makedirs('logs')
    logfile = open('logs/{}.txt'.format(name), 'w')
    for variable in variables:
        logfile.write('----- {} -----'.format(str(variable)))
    logfile.write('\n')
    return logfile


def draw_green_area():
    logfile = create_logfile('safe_area')

    for g in G:
        plt.plot([g[0][0], g[0][1], g[0][1], g[0][0], g[0][0]],
                 [g[1][0], g[1][0], g[1][1], g[1][1], g[1][0]], color='black')
        plt.fill([g[0][0], g[0][1], g[0][1], g[0][0], g[0][0]],
                 [g[1][0], g[1][0], g[1][1], g[1][1], g[1][0]], color='limegreen')
        logfile.write(str(g) + '\n')
    logfile.close()

    print(Fore.GREEN + 'G: ', G)
    print('Number of green boxes: ', len(G))
    print(Style.RESET_ALL)


def draw_red_area():
    logfile = create_logfile('unsafe_area')

    for r in R:
        plt.plot([r[0][0], r[0][1], r[0][1], r[0][0], r[0][0]],
                 [r[1][0], r[1][0], r[1][1], r[1][1], r[1][0]], color='black')
        plt.fill([r[0][0], r[0][1], r[0][1], r[0][0], r[0][0]],
                 [r[1][0], r[1][0], r[1][1], r[1][1], r[1][0]], color='red')
        logfile.write(str(r) + '\n')
    logfile.close()

    print(Fore.RED + 'R: ', R)
    print('Number of red boxes: ', len(R))
    print(Style.RESET_ALL)


def draw_hyperplane():
    X = []
    Y = []
    for i in G:
        X.append([i[0][0], i[1][0]])
        X.append([i[0][1], i[1][1]])
        Y.append(0)
        Y.append(0)

    for i in R:
        X.append([i[0][0], i[1][0]])
        X.append([i[0][1], i[1][1]])
        Y.append(1)
        Y.append(1)

    if 0 in Y and 1 in Y:
        clf = svm.SVC(kernel='rbf', C=1000)
        clf.fit(X, Y)
        ax = plt.gca()
        xlim = ax.get_xlim()
        ylim = ax.get_ylim()
        xx = np.linspace(xlim[0], xlim[1], 30)
        yy = np.linspace(ylim[0], ylim[1], 30)
        YY, XX = np.meshgrid(yy, xx)
        xy = np.vstack([XX.ravel(), YY.ravel()]).T
        Z = clf.decision_function(xy).reshape(XX.shape)
        # plot decision boundary and margins
        # plt instead of ax
        ax.contour(XX, YY, Z, colors='b', levels=[-1, 0, 1], alpha=0.5,
                   linestyles=['--', '-', '--'])
        # plot support vectors
        # ax.scatter(clf.support_vectors_[:, 0], clf.support_vectors_[:, 1], s=100,
        # linewidth=1, facecolors='none', edgecolors='k')


# Complete visualization part
def generate_graph():
    init_graph()
    draw_green_area()
    draw_red_area()
    draw_hyperplane()


def show_graph():
    plt.show()


def show_progress():
    green_area = calculate_area(G)
    red_area = calculate_area(R)
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
    print('Total Time{} :'.format(' ' * (max_name_len-len('Total Time'))), round(total_time, 3), 'sec.')


def main():
    None


if __name__ == "__main__":
    main()

import matplotlib.pyplot as plt

from variables import *


def init_graph():
    plt.xlim([0, 1.0])
    plt.ylim([0, 1.0])


def draw_green_area():
    for g in G:
        plt.plot([g[0][0], g[0][1], g[0][1], g[0][0], g[0][0]], [
                 g[1][0], g[1][0], g[1][1], g[1][1], g[1][0]], color='black')
        plt.fill([g[0][0], g[0][1], g[0][1], g[0][0], g[0][0]], [
                 g[1][0], g[1][0], g[1][1], g[1][1], g[1][0]], color='limegreen')


def draw_red_area():
    for r in R:
        plt.plot([r[0][0], r[0][1], r[0][1], r[0][0], r[0][0]], [
                 r[1][0], r[1][0], r[1][1], r[1][1], r[1][0]], color='black')
        plt.fill([r[0][0], r[0][1], r[0][1], r[0][0], r[0][0]], [
                 r[1][0], r[1][0], r[1][1], r[1][1], r[1][0]], color='red')


# Complete visualization part
def generate_graph():
    init_graph()
    draw_green_area()
    draw_red_area()


def show_graph():
    plt.show()


def main():
    None


if __name__ == "__main__":
    main()

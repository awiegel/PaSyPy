import os
import tkinter as tk
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.backends.backend_tkagg import NavigationToolbar2Tk
import matplotlib.pyplot as plt

import variables
import pasypy


class MainApplication(tk.Frame):
    def __init__(self, parent, *args, **kwargs):
        tk.Frame.__init__(self, parent, *args, **kwargs)
        self.parent = parent

        self.parent.title('Parameter Synthesis with Python')
        self.parent.geometry('1280x1080')
        self.greeting = tk.Label(text='Parameter Synthesis with Python')

        self.exit_button = tk.Button(root, text="Exit", command=root.quit, width=10, height=2, bg='black', fg='white')
        self.exit_button.grid(row=0, column=1, sticky=tk.NE, padx=5, pady=5)

        self.update_button = tk.Button(text="UPDATE", command=self.update_window, width=25, height=5, bg="blue", fg="yellow",)
        self.update_button.grid(row=0, column=0, sticky=tk.NW, padx=5, pady=5)

        self.show_safe_area_button = tk.Button(text="Show safe area", command=self.show_safe_area, width=15, height=2, bg='limegreen')
        self.show_safe_area_button.grid(row=0, column=0, sticky=tk.NW, padx=200, pady=5)

        self.show_unsafe_area_button = tk.Button(text="Show unsafe area", command=self.show_unsafe_area, width=15, height=2, bg='red')
        self.show_unsafe_area_button.grid(row=0, column=0, sticky=tk.NW, padx=200, pady=50)

        self.increase_accuracy_button = tk.Button(root, text="Increase accuracy", command=self.increase_accuracy, width=15, height=1, bg='white', fg='black')
        self.increase_accuracy_button.grid(row=1, column=2, sticky=tk.NW, padx=5, pady=245)

        self.decrease_accuracy_button = tk.Button(root, text="Decrease accuracy", command=self.decrease_accuracy, width=15, height=1, bg='white', fg='black')
        self.decrease_accuracy_button.grid(row=1, column=2, sticky=tk.NW, padx=5, pady=270)

        self.accuracy = 0
        self.ax = None
        self.line = 0

        figure = plt.figure()
        self.add_plot(figure)

    @classmethod
    def show_safe_area(self):
        os.startfile(os.getcwd() + '/logs/safe_area.log')


    @classmethod
    def show_unsafe_area(self):
        os.startfile(os.getcwd() + '/logs/unsafe_area.log')


    def increase_accuracy(self):
        variables.depth_limit += 1
        self.accuracy.destroy()
        self.accuracy = tk.Label(text='Accuracy: 2^{} or {} or {}'.format(variables.depth_limit, 2**variables.depth_limit, 1/(2**variables.depth_limit)), width=30, bg='black', fg='white', anchor=tk.W)
        self.accuracy.grid(row=1, column=1, sticky=tk.NW, pady=260)


    def decrease_accuracy(self):
        if variables.depth_limit > 1:
            variables.depth_limit -= 1
            self.accuracy.destroy()
            self.accuracy = tk.Label(text='Accuracy: 2^{} or {} or {}'.format(variables.depth_limit, 2**variables.depth_limit, 1/(2**variables.depth_limit)), width=30, bg='black', fg='white', anchor=tk.W)
            self.accuracy.grid(row=1, column=1, sticky=tk.NW, pady=260)


    def add_plot(self, figure):
        figure_frame = tk.Frame(root, highlightbackground='black', highlightcolor='black', highlightthickness=5)
        figure_frame.grid(row=1, column=0, sticky=tk.NW, padx=5, pady=5)
        self.line = FigureCanvasTkAgg(figure, master=figure_frame)
        
        toolbar_frame = tk.Frame(root, highlightbackground='black', highlightcolor='black', highlightthickness=5)
        toolbar_frame.grid(row=1, column=0, sticky=tk.NW, padx=5, pady=5)
        NavigationToolbar2Tk(self.line, toolbar_frame)
        self.line = self.line.get_tk_widget()
        self.line.grid(row=1, column=0, sticky=tk.NW, padx=5, pady=5)


    def update_window(self):
        self.line.destroy()
        print(variables.Queue)
        print(variables.Sub_Queue)
        if variables.Sub_Queue:
            variables.Queue = variables.Sub_Queue
            variables.Sub_Queue = []
        pasypy.main()


def main():
    None


if __name__ == "__main__":
    main()
else:
    root = tk.Tk()
    app = MainApplication(root)

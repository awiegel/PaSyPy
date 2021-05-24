import os
import tkinter as tk
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.backends.backend_tkagg import NavigationToolbar2Tk

from variables import *


class MainApplication(tk.Frame):
    def __init__(self, parent, *args, **kwargs):
        tk.Frame.__init__(self, parent, *args, **kwargs)
        self.parent = parent

        self.parent.title('Parameter Synthesis with Python')
        self.parent.geometry('1280x1080')
        self.greeting = tk.Label(text='Parameter Synthesis with Python')

        self.exit_button = tk.Button(root, text="Exit", command=root.quit, width=10, height=2, bg='black', fg='white')
        self.exit_button.grid(row=0, column=1, sticky=tk.NE, padx=5, pady=5)


    def add_plot(self, figure):
        figure_frame = tk.Frame(root, highlightbackground='black', highlightcolor='black', highlightthickness=5)
        figure_frame.grid(row=1, column=0, sticky=tk.NW, padx=5, pady=5)
        self.line = FigureCanvasTkAgg(figure, master=figure_frame).get_tk_widget()
        self.line.grid(row=1, column=0, sticky=tk.NW, padx=5, pady=5)


root = tk.Tk()
app = MainApplication(root)

def main():
    None


if __name__ == "__main__":
    main()

import os
import re
import tkinter as tk
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.backends.backend_tkagg import NavigationToolbar2Tk
import matplotlib.pyplot as plt
from z3 import *

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

        self.update_button = tk.Button(text="UPDATE", command=self.update, width=25, height=5, bg="blue", fg="yellow",)
        self.update_button.grid(row=0, column=0, sticky=tk.NW, padx=5, pady=5)

        self.reset_button = tk.Button(text="RESET", command=self.reset, width=10, height=5, bg="gray", fg="white",)
        self.reset_button.grid(row=0, column=0, sticky=tk.NW, padx=325, pady=5)

        self.show_safe_area_button = tk.Button(text="Show safe area", command=self.show_safe_area, width=15, height=2, bg='limegreen')
        self.show_safe_area_button.grid(row=0, column=0, sticky=tk.NW, padx=200, pady=5)

        self.show_unsafe_area_button = tk.Button(text="Show unsafe area", command=self.show_unsafe_area, width=15, height=2, bg='red')
        self.show_unsafe_area_button.grid(row=0, column=0, sticky=tk.NW, padx=200, pady=50)

        self.increase_accuracy_button = tk.Button(root, text="Increase accuracy", command=self.increase_accuracy, width=15, height=1, bg='white', fg='black')
        self.increase_accuracy_button.grid(row=1, column=2, sticky=tk.NW, padx=5, pady=245)

        self.decrease_accuracy_button = tk.Button(root, text="Decrease accuracy", command=self.decrease_accuracy, width=15, height=1, bg='white', fg='black')
        self.decrease_accuracy_button.grid(row=1, column=2, sticky=tk.NW, padx=5, pady=270)

        self.summary = tk.Label(text='SUMMARY:', width=30, bg='black', fg='white')
        self.summary.grid(row=1, column=1, sticky=tk.NW, pady=20)
        self.summary1 = tk.Label(text='------------------------------', width=30, bg='black', fg='white') # relief='raised'
        self.summary1.grid(row=1, column=1, sticky=tk.NW)
        self.summary2 = tk.Label(text='------------------------------', width=30, bg='black', fg='white')
        self.summary2.grid(row=1, column=1, sticky=tk.NW, pady=40)
        self.summary3 = tk.Label(text='------------------------------', width=30, bg='black', fg='white')
        self.summary3.grid(row=1, column=1, sticky=tk.NW, pady=160)
        self.summary4 = tk.Label(text='------------------------------', width=30, bg='black', fg='white',)
        self.summary4.grid(row=1, column=1, sticky=tk.NW, pady=240)
        self.summary5 = tk.Label(text='------------------------------', width=30, bg='black', fg='white')
        self.summary5.grid(row=1, column=1, sticky=tk.NW, pady=280)

        self.time1 = tk.Label(text='Computation Time   :', width=30, bg='black', fg='white', anchor=tk.W)
        self.time1.grid(row=1, column=1, sticky=tk.NW, pady=180)
        self.time2 = tk.Label(text='Visualization Time    :', width=30, bg='black', fg='white', anchor=tk.W)
        self.time2.grid(row=1, column=1, sticky=tk.NW, pady=200)
        self.time3 = tk.Label(text='Total Time                 :', width=30, bg='black', fg='white', anchor=tk.W)
        self.time3.grid(row=1, column=1, sticky=tk.NW, pady=220)
        
        self.constraints = 0
        self.accuracy = tk.Label(text='Accuracy: 2^{} or {} or {}'.format(variables.depth_limit, 2**variables.depth_limit, 1/(2**variables.depth_limit)), width=30, bg='black', fg='white', anchor=tk.W)
        self.accuracy.grid(row=1, column=1, sticky=tk.NW, pady=260)
        self.number_of_green_boxes = tk.Label(text='Number of green boxes : ', width=30, bg='limegreen', fg='black', anchor=tk.W)
        self.number_of_green_boxes.grid(row=1, column=1, sticky=tk.NW, pady=60)
        
        self.green_area = tk.Label(text='Green area                        : ', width=30, bg='limegreen', fg='black', anchor=tk.W)
        self.green_area.grid(row=1, column=1, sticky=tk.NW, pady=80)

        self.number_of_red_boxes = tk.Label(text='Number of red boxes     : ', width=30, bg='red', fg='black', anchor=tk.W)
        self.number_of_red_boxes.grid(row=1, column=1, sticky=tk.NW, pady=100)

        self.red_area = tk.Label(text='Red area                           : ', width=30, bg='red', fg='black', anchor=tk.W)
        self.red_area.grid(row=1, column=1, sticky=tk.NW, pady=120)

        self.white_area_left = tk.Label(text='White area left                 : ', width=30, bg='white', fg='black', anchor=tk.W)
        self.white_area_left.grid(row=1, column=1, sticky=tk.NW, pady=140)

        self.constraints_title = tk.Label(text='Constraints:', width=30, bg='black', fg='white')
        self.constraints_title.grid(row=1, column=1, sticky=tk.NW, pady=300)

        self.constraints_label = tk.Label(text="", width=30, height=10, bg='black', fg='white')
        self.constraints_label.grid(row=1, column=1, sticky=tk.NW, pady=320)

        self.ax = None
        self.line = 0

        figure = plt.figure()
        self.add_plot(figure)

        self.text = tk.Text(root, width=22, height=10)
        self.text.grid(row=1, column=2, sticky=tk.NW, padx=5, pady=350)

        self.text_button = tk.Button(root, text="EDIT", command=self.edit, width=5, height=1, bg='green', fg='white')
        self.text_button.grid(row=1, column=2, sticky=tk.NW, padx=190, pady=490)

        self.reload_file_button = tk.Button(root, text="RELOAD FILE", command=self.reload_file, width=10, height=1, bg='brown', fg='white')
        self.reload_file_button.grid(row=1, column=2, sticky=tk.NW, padx=190, pady=335)

        self.global_xlim = (0.0, 1.0)
        self.global_ylim = (0.0, 1.0)

        self.file_path_label = tk.Label(root, text="", width=25, height=2, bg='black', fg='white')
        self.file_path_label.grid(row=1, column=2, sticky=tk.NW, padx=5, pady=310)

        self.get_file_path_button = tk.Button(root, text="Open .smt2 file", command=self.browseFiles, width=15, height=1, bg='gray', fg='white')
        self.get_file_path_button.grid(row=1, column=2, sticky=tk.NW, padx=190, pady=310)

        self.file_path = None


    def reload_file(self):
        self.constraints = parse_smt2_file(self.file_path)
        self.constraints_label.configure(text=self.constraints[0])
        variables.Constraints = self.constraints[0]
        self.text.delete('1.0', 'end-1c')
        self.text.insert('1.0', self.constraints[0])
        variables.parameters = []

        while True:
            try:
                print(eval(str(self.constraints)))
                break
            except NameError as e:
                var = re.findall("name '(\w+)' is not defined",str(e))[0]
                locals()['{}'.format(var)] = Real('{}'.format(var))
                variables.parameters.append(locals()['{}'.format(var)])

        pasypy.main()


    def browseFiles(self):
        if self.file_path:
            reload = True
        else:
            reload = False
        
        file_path = tk.filedialog.askopenfilename()
        if file_path:
            self.file_path = file_path
            self.file_path_label.configure(text=os.path.basename(self.file_path))

            self.constraints = parse_smt2_file(self.file_path)
            self.constraints_label.configure(text=self.constraints[0])

            variables.Constraints = self.constraints[0]
            self.text.delete('1.0', 'end-1c')
            self.text.insert('1.0', self.constraints[0])

            variables.parameters = []

            while True:
                try:
                    print(eval(str(self.constraints)))
                    break
                except NameError as e:
                    var = re.findall("name '(\w+)' is not defined",str(e))[0]
                    locals()['{}'.format(var)] = Real('{}'.format(var))
                    variables.parameters.append(locals()['{}'.format(var)])

            if reload:
                self.reset()
            else:
                pasypy.main()
                self.update_window()



    def edit(self):
        f = self.text.get('1.0', 'end-1c')
        if self.text.compare('1.0', '!=', 'end-1c') and f != str(self.constraints[0]):

            for i in variables.parameters:
                locals()['{}'.format(i)] = i
            
            self.constraints_label.configure(text=f)
            variables.Constraints = eval(f)

            self.reset()


    @classmethod
    def show_safe_area(self):
        os.startfile(os.getcwd() + '/logs/safe_area.log')


    @classmethod
    def show_unsafe_area(self):
        os.startfile(os.getcwd() + '/logs/unsafe_area.log')


    def increase_accuracy(self):
        variables.depth_limit += 1
        self.accuracy.config(text='Accuracy: 2^{} or {} or {}'.format(variables.depth_limit, 2**variables.depth_limit, 1/(2**variables.depth_limit)))


    def decrease_accuracy(self):
        if variables.depth_limit > 1:
            variables.depth_limit -= 1
            self.accuracy.config(text='Accuracy: 2^{} or {} or {}'.format(variables.depth_limit, 2**variables.depth_limit, 1/(2**variables.depth_limit)))


    def add_plot(self, figure):
        figure_frame = tk.Frame(root, highlightbackground='black', highlightcolor='black', highlightthickness=5)
        figure_frame.grid(row=1, column=0, sticky=tk.NW, padx=5, pady=5)
        self.line = FigureCanvasTkAgg(figure, master=figure_frame)
        
        toolbar_frame = tk.Frame(root, highlightbackground='black', highlightcolor='black', highlightthickness=5)
        toolbar_frame.grid(row=1, column=0, sticky=tk.NW, padx=5, pady=5)
        NavigationToolbar2Tk(self.line, toolbar_frame)
        self.line = self.line.get_tk_widget()
        self.line.grid(row=1, column=0, sticky=tk.NW, padx=5, pady=5)


    def update(self):
        self.line.destroy()
        if variables.Sub_Queue:
            variables.Queue = variables.Sub_Queue
            variables.Sub_Queue = []
        pasypy.main()
        self.update_window()


    def reset(self):
        variables.Queue = [([0, 1], [0, 1], 1)]
        variables.Sub_Queue = []
        variables.G = []
        variables.R = []

        self.line.destroy()
        self.ax.clear()

        pasypy.main()
        self.update_window()


    def update_window(self):
        green_area = pasypy.calculate_area(variables.G)
        self.number_of_green_boxes.config(text='Number of green boxes : {}'.format(len(variables.G)))
        self.green_area.config(text='Green area                        : {:.2%}'.format(green_area))

        red_area = pasypy.calculate_area(variables.R)
        self.number_of_red_boxes.config(text='Number of red boxes     : {}'.format(len(variables.R)))
        self.red_area.config(text='Red area                           : {:.2%}'.format(red_area))

        self.white_area_left.config(text='White area left                 : {:.2%}'.format(1 - (green_area + red_area)))


def main():
    None


if __name__ == "__main__":
    main()
else:
    root = tk.Tk()
    app = MainApplication(root)

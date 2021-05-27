import os
import re
import tkinter as tk
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.backends.backend_tkagg import NavigationToolbar2Tk
import matplotlib.pyplot as plt
from z3 import *

import variables
import visualize
import pasypy


class MainApplication(tk.Frame):
    def __init__(self, parent, *args, **kwargs):
        tk.Frame.__init__(self, parent, *args, **kwargs)
        self.parent = parent

        self.parent.title('PaSyPy - Parameter Synthesis with Python')
        self.parent.geometry('1020x740')
        # self.greeting = tk.Label(text='Parameter Synthesis with Python')
        self.parent.configure(background='white')

        self.frame_color = 'black'

        self.frame5 = tk.Frame(width=100, height=140, background=self.frame_color)       
        self.frame5.grid(row=0, column=0, sticky=tk.NW, padx=925, pady=5)

        self.exit_button = tk.Button(self.frame5, text="Exit", command=root.quit, width=10, height=2, bg='black', fg='white')
        self.exit_button.grid(row=0, column=0, sticky=tk.NW, padx=5, pady=5)

        self.left_frame = tk.Frame(width=100, height=140, background=self.frame_color)       
        self.left_frame.grid(row=0, column=0, sticky=tk.NW, padx=475, pady=62)

        self.update_graph_button = tk.Button(self.left_frame, text="Update\nGraph", command=self.update, width=11, height=3, bg="steel blue", fg="white")
        self.update_graph_button.grid(row=0, column=0, sticky=tk.NW, padx=(5,3), pady=5)

        self.compute_button = tk.Button(self.left_frame, text="Compute", command=self.update, width=11, height=3, bg="steel blue", fg="white",)
        self.compute_button.grid(row=0, column=1, sticky=tk.NW, padx=(3,5), pady=5)

        self.frame2 = tk.Frame(width=100, height=100, background=self.frame_color)       
        self.frame2.grid(row=1, column=0, sticky=tk.NW, padx=890, pady=70)

        self.show_safe_area_button = tk.Button(self.frame2, text="Show safe area", command=self.show_safe_area, width=15, height=2, bg='forest green')
        self.show_safe_area_button.grid(row=0, column=0, sticky=tk.NW, padx=5, pady=(5,0))

        self.show_unsafe_area_button = tk.Button(self.frame2, text="Show unsafe area", command=self.show_unsafe_area, width=15, height=2, bg='firebrick')
        self.show_unsafe_area_button.grid(row=1, column=0, sticky=tk.NW, padx=5, pady=(0,5))

        self.frame1 = tk.Frame(width=1000, height=1400, background=self.frame_color)       
        self.frame1.grid(row=1, column=0, sticky=tk.NW, padx=670, pady=5)



        self.summary = tk.Label(self.frame1, text='SUMMARY:', width=30, bg='black', fg='white')
        self.summary.grid(row=1, column=0, sticky=tk.NW, padx=5)
        self.summary1 = tk.Label(self.frame1, text='---------------------------------------------', width=30, bg='black', fg='white') # relief='raised'
        self.summary1.grid(row=0, column=0, sticky=tk.NW, padx=5, pady=(5,0))
        self.summary2 = tk.Label(self.frame1,text='---------------------------------------------', width=30, bg='black', fg='white')
        self.summary2.grid(row=2, column=0, sticky=tk.NW, padx=5)
        self.summary3 = tk.Label(self.frame1, text='---------------------------------------------', width=30, bg='black', fg='white')
        self.summary3.grid(row=8, column=0, sticky=tk.NW, padx=5)
        self.summary4 = tk.Label(self.frame1, text='---------------------------------------------', width=30, bg='black', fg='white',)
        self.summary4.grid(row=12, column=0, sticky=tk.NW, padx=5)
        self.summary5 = tk.Label(self.frame1, text='---------------------------------------------', width=30, bg='black', fg='white')
        self.summary5.grid(row=14, column=0, sticky=tk.NW, padx=5)
        self.summary6 = tk.Label(self.frame1, text='---------------------------------------------', width=30, bg='black', fg='white')
        self.summary6.grid(row=17, column=0, sticky=tk.NW, padx=5, pady=(0,5))

        self.time1 = tk.Label(self.frame1, text='Computation Time   :', width=30, bg='black', fg='white', anchor=tk.W)
        self.time1.grid(row=9, column=0, sticky=tk.NW, padx=5)
        self.time2 = tk.Label(self.frame1, text='Visualization Time    :', width=30, bg='black', fg='white', anchor=tk.W)
        self.time2.grid(row=10, column=0, sticky=tk.NW, padx=5)
        self.time3 = tk.Label(self.frame1, text='Total Time                 :', width=30, bg='black', fg='white', anchor=tk.W)
        self.time3.grid(row=11, column=0, sticky=tk.NW, padx=5)
        
        self.constraints = 0
        self.accuracy = tk.Label(self.frame1, text='Accuracy: 2^{}'.format(variables.depth_limit), width=30, bg='black', fg='white', anchor=tk.W)
        self.accuracy.grid(row=13, column=0, sticky=tk.NW, padx=5)

        self.increase_accuracy_button = tk.Button(self.frame1, text="+", command=self.increase_accuracy, width=2, height=1, bg='white', fg='black')
        self.increase_accuracy_button.grid(row=13, column=0, sticky=tk.NE, padx=35)

        self.decrease_accuracy_button = tk.Button(self.frame1, text="-", command=self.decrease_accuracy, width=2, height=1, bg='white', fg='black')
        self.decrease_accuracy_button.grid(row=13, column=0, sticky=tk.NE, padx=5)

        self.number_of_green_boxes = tk.Label(self.frame1, text='Number of green boxes : ', width=30, bg='forestgreen', fg='black', anchor=tk.W)
        self.number_of_green_boxes.grid(row=3, column=0, sticky=tk.NW, padx=5)
        
        self.green_area = tk.Label(self.frame1, text='Green area                        : ', width=30, bg='forestgreen', fg='black', anchor=tk.W)
        self.green_area.grid(row=4, column=0, sticky=tk.NW, padx=5)

        self.number_of_red_boxes = tk.Label(self.frame1, text='Number of red boxes     : ', width=30, bg='firebrick', fg='black', anchor=tk.W)
        self.number_of_red_boxes.grid(row=5, column=0, sticky=tk.NW, padx=5)

        self.red_area = tk.Label(self.frame1, text='Red area                           : ', width=30, bg='firebrick', fg='black', anchor=tk.W)
        self.red_area.grid(row=6, column=0, sticky=tk.NW, padx=5)

        self.white_area_left = tk.Label(self.frame1, text='White area left                 : ', width=30, bg='white', fg='black', anchor=tk.W)
        self.white_area_left.grid(row=7, column=0, sticky=tk.NW, padx=5)

        self.constraints_title = tk.Label(self.frame1, text='Constraints:', width=30, bg='black', fg='white')
        self.constraints_title.grid(row=15, column=0, sticky=tk.NW, padx=5)

        self.constraints_label = tk.Label(self.frame1, text="", width=30, height=8, bg='black', fg='white')
        self.constraints_label.grid(row=16, column=0, sticky=tk.NW, padx=5, pady=(0,5))

                # self.frame3 = tk.Frame(width=100, height=100, background=self.frame_color)       
        # self.frame3.grid(row=1, column=0, sticky=tk.NW, padx=890, pady=275)

        self.ax = None
        self.line = 0

        figure = plt.figure()
        self.add_plot(figure)

        self.global_xlim = (0.0, 1.0)
        self.global_ylim = (0.0, 1.0)

        self.frame4 = tk.Frame(width=100, height=140, background=self.frame_color)       
        self.frame4.grid(row=0, column=0, sticky=tk.NW, padx=670, pady=(5,0))

        self.text = tk.Text(self.frame4, width=19, height=10)
        self.text.grid(row=1, column=0, sticky=tk.NW, padx=5, pady=(0,5))

        self.text_button = tk.Button(self.frame4, text="EDIT", command=self.edit, width=6, height=4, bg='gray', fg='white')
        self.text_button.grid(row=1, column=0, sticky=tk.NW, padx=(170,5), pady=(95,5))

        self.get_file_path_button = tk.Button(self.frame4, text="OPEN\nFILE", command=self.open_file, width=6, height=2, bg='gray', fg='white')
        self.get_file_path_button.grid(row=1, column=0, sticky=tk.NW, padx=(170,5), pady=0)

        self.reload_file_button = tk.Button(self.frame4, text="RELOAD\nFILE", command=self.reload_file, width=6, height=2, bg='gray', fg='white')
        self.reload_file_button.grid(row=1, column=0, sticky=tk.NW, padx=(170,5), pady=45)


        self.file_path_label = tk.Label(self.frame4, text="no file loaded", width=30, height=2, bg='black', fg='white')
        self.file_path_label.grid(row=0, column=0, sticky=tk.NW, padx=5, pady=4)


        self.file_path = None

        self.frame5 = tk.Frame(width=100, height=140, background=self.frame_color)       
        self.frame5.grid(row=0, column=0, sticky=tk.NW, padx=475, pady=5)

        self.ready_label1 = tk.Label(self.frame5, text=">> STATUS <<", width=25, height=1, bg='black', fg='white')
        self.ready_label1.grid(row=0, column=0, sticky=tk.NW, padx=5, pady=(5,0))

        self.ready_label = tk.Label(self.frame5, text="WAITING", width=25, height=1, bg='black', fg='white')
        self.ready_label.grid(row=1, column=0, sticky=tk.NW, padx=5, pady=(0,5))


        self.frame6 = tk.Frame(width=100, height=140, background=self.frame_color)       
        self.frame6.grid(row=0, column=0, sticky=tk.NW, padx=5, pady=5)

        self.background_image=tk.PhotoImage(file='PaSyPy/rwth_logo.png')
        self.background_label = tk.Label(self.frame6, image=self.background_image)
        self.background_label.grid(row=0, column=0, sticky=tk.NW, padx=5, pady=5)


    def add_axes_field(self, x_axe, y_axe):
        self.text_x_axe = tk.Entry(root, width=3, bg='black', fg='white', justify='center')
        self.text_x_axe.insert(string=x_axe, index=0)
        self.text_x_axe.grid(row=1, column=0, sticky=tk.NW, padx=325, pady=465)

        self.text_y_axe = tk.Entry(root, width=3, bg='black', fg='white', justify='center')
        self.text_y_axe.insert(string=y_axe, index=0)
        self.text_y_axe.grid(row=1, column=0, sticky=tk.NW, padx=35, pady=250)

    def add_empty_graph(self):
        self.add_plot(plt.figure())
        visualize.init_graph()

        self.add_axes_field(variables.parameters[0], variables.parameters[1])


    def get_graph_axes(self):
        x_axe = Real('{}'.format(self.text_x_axe.get()))
        variables.x_axe_position = 0
        for index, value in zip(range(len(variables.parameters)), variables.parameters):
            if x_axe == value:
                variables.x_axe_position = index
                break

        y_axe = Real('{}'.format(self.text_y_axe.get()))
        variables.y_axe_position = 0       
        for index, value in zip(range(len(variables.parameters)), variables.parameters):
            if y_axe == value:
                variables.y_axe_position = index
                break


    def reload_file(self):
        if self.file_path:
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

            Bounds = ()
            for _ in range(len(variables.parameters)):
                Bounds += ([0,1],)
            Bounds += (1,)
            variables.Queue = [Bounds]
            variables.Sub_Queue = []
            variables.G = []
            variables.R = []

            pasypy.main()


    def open_file(self):
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

            Bounds = ()
            for _ in range(len(variables.parameters)):
                Bounds += ([0,1],)
            Bounds += (1,)
            variables.Queue = [Bounds]
            variables.Sub_Queue = []
            variables.G = []
            variables.R = []


            self.add_empty_graph()


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
        self.accuracy.config(text='Accuracy: 2^{}'.format(variables.depth_limit))


    def decrease_accuracy(self):
        if variables.depth_limit > 1:
            variables.depth_limit -= 1
            self.accuracy.config(text='Accuracy: 2^{}'.format(variables.depth_limit))


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
        if variables.Constraints is not None:
            self.ready_label.configure(text='COMPUTING...')
            if variables.depth_limit >= variables.previous_depth_limit:
                self.get_graph_axes()

                self.line.destroy()
                if variables.Sub_Queue:
                    variables.Queue = variables.Sub_Queue
                    variables.Sub_Queue = []
                pasypy.main()
                self.update_window()
            else:
                self.reset()
            
            self.add_axes_field(variables.parameters[variables.x_axe_position], variables.parameters[variables.y_axe_position])

            self.ready_label.configure(text='FINISHED')
            variables.previous_depth_limit = variables.depth_limit


    def reset(self):
        Bounds = ()
        for _ in range(len(variables.parameters)):
            Bounds += ([0,1],)
        Bounds += (1,)
        variables.Queue = [Bounds]
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

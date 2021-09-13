"""The graphical user interface (GUI) of this tool."""

import os
import webbrowser
import tkinter as tk
import matplotlib
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.backends.backend_tkagg import NavigationToolbar2Tk

from pasypy import variables, settings, color, splitting_heuristic
from pasypy.pasypy import PaSyPy
from pasypy.visualize import Visualize
from pasypy.logger import Logger
from pasypy.timer import Timer
from pasypy.constraints_parser import ConstraintsParser
from pasypy.area_calculation import AreaCalculation


class MainApplication(tk.Frame):
    """The graphical user interface (GUI) of this tool."""

    def __init__(self, parent, *args, **kwargs):
        """Creates the complete graphical user interface (GUI) with all its functionality sorted by frames."""
        matplotlib.use('Agg')
        tk.Frame.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        self.parent.title('PaSyPy - Parameter Synthesis with Python')
        self.parent.geometry('1200x770')
        self.parent.minsize(1200, 770)
        self.parent.configure(background='white')
        self.frame_color = 'black'
        tk.Grid.rowconfigure(self.parent, index=0, weight=1)
        tk.Grid.columnconfigure(self.parent, index=0, weight=0)
        tk.Grid.columnconfigure(self.parent, index=1, weight=1)
        self.tk.call('wm', 'iconphoto', self.parent._w, tk.PhotoImage(file='images/PaSyPy_logo.png'))

        self.line = 0
        self.file_path = None
        self.computation_timer = Timer()
        self.area_calculation = AreaCalculation()

        self.parent.bind('+', lambda _: self.increase_accuracy())
        self.parent.bind('-', lambda _: self.decrease_accuracy())
        self.parent.bind('<Escape>', lambda _: self.parent.quit())
        self.parent.bind('o', lambda _: self.open_file())
        self.parent.bind('r', lambda _: self.reload_file())
        self.parent.bind('<space>', lambda _: self.update())

        self.changed = True
        self.current_depth_limit = 0
        self.window = None
        self.parent.protocol('WM_DELETE_WINDOW', self._top_closes)

        # START - FRAME 1 #
        self.frame1 = tk.Frame(background='white')
        self.frame1.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)

        ## START - FRAME 1.1 #
        self.frame11 = tk.Frame(master=self.frame1, background='white')
        self.frame11.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)

        ### START - FRAME 1.1.1 #
        self.frame111 = tk.Frame(master=self.frame11, background='black')
        self.frame111.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=(0,5))

        #### START - FRAME 1.1.1.1 #
        self.frame1111 = tk.Frame(master=self.frame111, background='white')
        self.frame1111.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1, pady=(1,0))
        self.ready_label1 = tk.Label(self.frame1111, text='>> STATUS <<', height=1, bg='black', fg='white', font=('',16))
        self.ready_label1.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=(5,0))
        self.ready_label = tk.Label(self.frame1111, text='WAITING', height=1, bg='black', fg='white', font=('',16))
        self.ready_label.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=(0,5))

        tk.Grid.rowconfigure(self.frame1111, index=0, weight=1)
        tk.Grid.rowconfigure(self.frame1111, index=1, weight=1)
        tk.Grid.columnconfigure(self.frame1111, index=0, weight=1)
        #### END - FRAME 1.1.1.1 #

        #### START - FRAME 1.1.1.2 #
        self.frame1112 = tk.Frame(master=self.frame111, background='white')
        self.frame1112.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1, pady=(0,1))
        self.compute_button = tk.Button(self.frame1112, text='Compute', command=self.start_calculation, bg='steel blue', fg='white', font=('',25))
        self.compute_button.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)

        tk.Grid.rowconfigure(self.frame1112, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame1112, index=0, weight=1)
        #### END - FRAME 1.1.1.2 #

        tk.Grid.rowconfigure(self.frame111, index=0, weight=1)
        tk.Grid.rowconfigure(self.frame111, index=1, weight=1)
        tk.Grid.columnconfigure(self.frame111, index=0, weight=1)
        ### END - FRAME 1.1.1 #

        #### START - FRAME 1.1.2 #
        self.frame112 = tk.Frame(master=self.frame11, background='black')
        self.frame112.grid(row=0, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5)

        #### START - FRAME 1.1.2.1 #
        self.frame1121 = tk.Frame(master=self.frame112, background='white')
        self.frame1121.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1, pady=(1,0))
        self.accuracy = tk.Label(self.frame1121, text='Accuracy: 2^{}'.format(variables.depth_limit), bg='white', fg='black', anchor=tk.W, width=12, font=('',10))
        self.accuracy.grid(row=0, column=0, columnspan=2, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5)
        self.decrease_accuracy_button = tk.Button(self.frame1121, text='-', command=self.decrease_accuracy, bg='black', fg='white')
        self.decrease_accuracy_button.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=(5,2.5))
        self.increase_accuracy_button = tk.Button(self.frame1121, text='+', command=self.increase_accuracy, bg='black', fg='white')
        self.increase_accuracy_button.grid(row=1, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=(2.5,5))

        tk.Grid.rowconfigure(self.frame1121, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame1121, index=0, weight=1)
        tk.Grid.rowconfigure(self.frame1121, index=1, weight=1)
        tk.Grid.columnconfigure(self.frame1121, index=1, weight=1)
        #### END - FRAME 1.1.2.1 #

        #### START - FRAME 1.1.2.2 #
        self.frame1122 = tk.Frame(master=self.frame112, background='white')
        self.frame1122.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1)
        self.hyphen = tk.Label(self.frame1122, text='------------------', bg='white', fg='black', font=('',13))
        self.hyphen.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))

        tk.Grid.rowconfigure(self.frame1122, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame1122, index=0, weight=1)
        #### END - FRAME 1.1.2.2 #

        #### START - FRAME 1.1.2.3 #
        self.frame1123 = tk.Frame(master=self.frame112, background='white')
        self.frame1123.grid(row=2, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1)
        self.interval = tk.Label(self.frame1123, text='Interval:', bg='white', fg='black', anchor=tk.W, font=('',10))
        self.interval.grid(row=0, column=0, columnspan=2, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5)
        self.minimum = tk.Entry(self.frame1123, width=5, relief='solid')
        self.minimum.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=(5,0))
        self.maximum = tk.Entry(self.frame1123, width=5, relief='solid')
        self.maximum.grid(row=1, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=(5,0))
        self.border_button = tk.Button(self.frame1123, text='SAVE', command=self.border, bg='gray', fg='white')
        self.border_button.grid(row=0, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5)

        tk.Grid.rowconfigure(self.frame1123, index=0, weight=1)
        tk.Grid.rowconfigure(self.frame1123, index=1, weight=1)
        tk.Grid.columnconfigure(self.frame1123, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame1123, index=1, weight=1)
        #### END - FRAME 1.1.2.3 #

        #### START - FRAME 1.1.2.4 #
        self.frame1124 = tk.Frame(master=self.frame112, background='white')
        self.frame1124.grid(row=3, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1)
        self.hyphen = tk.Label(self.frame1124, text='------------------', bg='white', fg='black', font=('',13))
        self.hyphen.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))

        tk.Grid.rowconfigure(self.frame1124, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame1124, index=0, weight=1)
        #### END - FRAME 1.1.2.4 #

        #### START - FRAME 1.1.2.5 #
        self.frame1125 = tk.Frame(master=self.frame112, background='white')
        self.frame1125.grid(row=4, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1, pady=(0,1))
        self.current_splitting_heuristic = tk.StringVar(self)
        self.current_splitting_heuristic.set(splitting_heuristic.current_splitting_heuristic)

        self.splitting_option = tk.OptionMenu(self.frame1125, self.current_splitting_heuristic, *splitting_heuristic.SPLITTING_HEURISTIC, command=self.set_splitting_heuristic)
        self.splitting_option.configure(state='normal', font=('',10), width=8, relief='solid')
        self.splitting_option.grid(row=0, column=0, sticky=tk.NW, padx=5, pady=(0,1))

        tk.Grid.rowconfigure(self.frame1125, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame1125, index=0, weight=1)
        #### END - FRAME 1.1.2.5 #

        tk.Grid.rowconfigure(self.frame112, index=0, weight=1)
        tk.Grid.rowconfigure(self.frame112, index=1, weight=1)
        tk.Grid.rowconfigure(self.frame112, index=2, weight=1)
        tk.Grid.rowconfigure(self.frame112, index=3, weight=1)
        tk.Grid.rowconfigure(self.frame112, index=4, weight=1)
        tk.Grid.columnconfigure(self.frame112, index=0, weight=1)
        ### END - FRAME 1.1.2 #

        ### START - FRAME 1.1.3 #
        self.frame113 = tk.Frame(master=self.frame11, background='black')
        self.frame113.grid(row=0, column=2, sticky=(tk.N+tk.E+tk.S+tk.W), padx=(5,0))
        self.number_of_green_boxes = tk.Label(self.frame113, text='Number of green boxes : 0', bg=color.safe_color, fg='black', anchor=tk.W, width=18, font=('',10))
        self.number_of_green_boxes.grid(row=3, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1, pady=(1,0))
        self.green_area = tk.Label(self.frame113, text='Green area                   : 0.00%', bg=color.safe_color, fg='black', anchor=tk.W, width=18, font=('',10))
        self.green_area.grid(row=4, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1, pady=(0,1))
        self.show_safe_area_button = tk.Button(self.frame113, text='X', command=Logger().show_safe_area, width=2, height=1, bg=color.safe_color)
        self.show_safe_area_button.grid(row=3, column=0, rowspan=2, sticky=tk.E, padx=10)
        self.number_of_red_boxes = tk.Label(self.frame113, text='Number of red boxes     : 0', bg=color.unsafe_color, fg='black', anchor=tk.W, width=18, font=('',10))
        self.number_of_red_boxes.grid(row=5, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1)
        self.red_area = tk.Label(self.frame113, text='Red area                      : 0.00%', bg=color.unsafe_color, fg='black', anchor=tk.W, width=18, font=('',10))
        self.red_area.grid(row=6, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1, pady=(0,1))
        self.show_unsafe_area_button = tk.Button(self.frame113, text='X', command=Logger().show_unsafe_area, width=2, height=1, bg=color.unsafe_color)
        self.show_unsafe_area_button.grid(row=5, column=0, rowspan=2, sticky=tk.E, padx=10)
        self.white_area_left = tk.Label(self.frame113, text='White area left              : 100%', bg='white', fg='black', anchor=tk.W, width=18, font=('',10))
        self.white_area_left.grid(row=7, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1)

        self.computation_time = tk.Label(self.frame113, text='Computation Time         :', bg='black', fg='white', anchor=tk.W, width=18, font=('',10))
        self.computation_time.grid(row=8, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1)
        self.visualization_time = tk.Label(self.frame113, text='Visualization Time         :', bg='black', fg='white', anchor=tk.W, width=18, font=('',10))
        self.visualization_time.grid(row=9, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1)
        self.computed_accuracy = tk.Label(self.frame113, text='Computed Accuracy      :', bg='black', fg='white', anchor=tk.W, width=18, font=('',10))
        self.computed_accuracy.grid(row=10, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1, pady=(0,1))

        tk.Grid.rowconfigure(self.frame113, index=0, weight=1)
        tk.Grid.rowconfigure(self.frame113, index=1, weight=1)
        tk.Grid.rowconfigure(self.frame113, index=2, weight=1)
        tk.Grid.rowconfigure(self.frame113, index=3, weight=1)
        tk.Grid.rowconfigure(self.frame113, index=4, weight=1)
        tk.Grid.rowconfigure(self.frame113, index=5, weight=1)
        tk.Grid.rowconfigure(self.frame113, index=6, weight=1)
        tk.Grid.rowconfigure(self.frame113, index=7, weight=1)
        tk.Grid.rowconfigure(self.frame113, index=8, weight=1)
        tk.Grid.rowconfigure(self.frame113, index=9, weight=1)
        tk.Grid.columnconfigure(self.frame113, index=0, weight=1)
        ### END - FRAME 1.1.3 #

        tk.Grid.rowconfigure(self.frame11, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame11, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame11, index=2, weight=1)
        ## END - FRAME 1.1 #

        ## START - FRAME 1.2 #
        self.frame12 = tk.Frame(master=self.frame1, background='black')
        self.frame12.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)

        tk.Grid.rowconfigure(self.frame12, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame12, index=0, weight=1)
        ## END - FRAME 1.2 #

        ## START - FRAME 1.3 #
        self.frame13 = tk.Frame(master=self.frame1, background='black')
        self.frame13.grid(row=2, column=0, sticky=tk.SW, padx=5, pady=5)

        self.background_image = tk.PhotoImage(file='images/logo_ths.png')
        self.background_label = tk.Label(self.frame13, image=self.background_image)
        self.background_label.grid(row=0, column=0, sticky=tk.SW, padx=1, pady=1)
        self.background_label.bind('<Button-1>', self.on_click)
        ## END - FRAME 1.3 #

        tk.Grid.rowconfigure(self.frame1, index=0, weight=0)
        tk.Grid.rowconfigure(self.frame1, index=1, weight=0)
        tk.Grid.rowconfigure(self.frame1, index=2, weight=1)
        tk.Grid.columnconfigure(self.frame1, index=0, weight=0)
        # END - FRAME 1 #

        # START - FRAME 2 #
        self.frame2 = tk.Frame(background='black')
        self.frame2.grid(row=0, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=(0,5), pady=(10,5))

        ## START - FRAME 2.1 #
        self.frame21 = tk.Frame(master=self.frame2, background='black')
        self.frame21.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
        self.get_file_path_button = tk.Button(self.frame21, text='OPEN\nFILE', command=self.open_file, width=6, height=2, bg='gray', fg='white')
        self.get_file_path_button.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
        self.reload_file_button = tk.Button(self.frame21, text='RELOAD\nFILE', command=self.reload_file, width=6, height=2, bg='gray', fg='white')
        self.reload_file_button.grid(row=0, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
        self.text_button = tk.Button(self.frame21, text='EDIT', command=self.edit, width=6, height=2, bg='gray', fg='white')
        self.text_button.grid(row=0, column=2, sticky=tk.NW, padx=5, pady=5)
        self.save_button = tk.Button(self.frame21, text='SAVE', command=self.save, width=6, height=2, bg='gray', fg='white')
        self.save_button.grid(row=0, column=3, sticky=tk.NW, padx=5, pady=5)
        self.file_path_label = tk.Label(self.frame21, text='no file loaded', height=2, bg='black', fg='white', anchor=tk.W, font=('',10))
        self.file_path_label.grid(row=0, column=4, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)

        self.settings_image = tk.PhotoImage(file='images/gear.png')
        self.settings_label = tk.Label(self.frame12, image=self.settings_image, bg='black', fg='black')
        self.settings_label.grid(row=0, column=0, sticky=tk.NE, padx=1, pady=1)
        self.settings_label.bind('<Button-1>', self.on_click)
        ## END - FRAME 2.1 #

        ## START - FRAME 2.2 #
        self.frame22 = tk.Frame(master=self.frame2, background='black', width=100, height=100)
        self.frame22.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
        self.text = tk.Text(self.frame22, width=19, height=10)
        self.text.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)

        tk.Grid.rowconfigure(self.frame22, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame22, index=0, weight=1)
        ## END - FRAME 2.2 #

        tk.Grid.rowconfigure(self.frame2, index=0, weight=0)
        tk.Grid.rowconfigure(self.frame2, index=1, weight=1)
        tk.Grid.columnconfigure(self.frame2, index=0, weight=1)
        # END - FRAME 2 #

        self.add_empty_graph()
        self.add_empty_axes()

    def _top_closes(self, event=None): # pylint: disable=W0613 # argument is required
        """Called when main window is closed.
        Approach to increase closing speed.

        :param event: Event listener, defaults to None
        """
        self.parent.quit()

    @staticmethod
    def on_click(event=None): # pylint: disable=W0613 # argument is required
        """Opens the link to the official Theory of Hybrid Systems research group (RWTH i2), headed by Prof. Dr. Erika Ábrahám.

        :param event: Event listener, defaults to None
        """
        webbrowser.open('https://ths.rwth-aachen.de/')

    def add_empty_graph(self):
        """Adds the empty graph on initialization or resetting to default."""
        plt.close('all')
        self.add_plot(plt.figure())
        plt.xlim(variables.x_axe_limit)
        plt.ylim(variables.y_axe_limit)

    def add_empty_axes(self):
        """Adds the empty fields for the parameters on the graph and the settings wheel."""
        self.variable_x_axe = tk.StringVar(self)
        self.opt_x_axe = tk.OptionMenu(self.frame12, self.variable_x_axe, *[''])
        self.opt_x_axe.configure(state='disabled', font=('',10), width=1, relief='solid')
        self.opt_x_axe.grid(row=0, column=0, sticky=tk.S, pady=1)
        self.variable_y_axe = tk.StringVar(self)
        self.opt_y_axe = tk.OptionMenu(self.frame12, self.variable_y_axe, *[''])
        self.opt_y_axe.configure(state='disabled', font=('',10), width=1, relief='solid')
        self.opt_y_axe.grid(row=0, column=0, sticky=tk.W, padx=1)
        self.settings_image = tk.PhotoImage(file='images/gear.png')
        self.settings_label = tk.Label(self.frame12, image=self.settings_image, bg='white', fg='black')
        self.settings_label.grid(row=0, column=0, sticky=tk.NE, padx=(0,1), pady=(1,0))
        self.settings_label.bind('<Button-1>', settings.Settings(self).on_click)

    def add_axes_field(self, update=False):
        """Adds the axes fields with actual parameters.

        :param update: If true sets the currently selected parameters and else the first two parameters from the constraint, defaults to False
        """
        self.opt_x_axe.children['menu'].delete(0, 'end')
        self.opt_y_axe.children['menu'].delete(0, 'end')

        if len(variables.parameters) == 1:
            self.opt_x_axe.children['menu'].add_command(label=variables.parameters[0], command=self.variable_x_axe.set(variables.parameters[0]))
        elif len(variables.parameters) > 1:
            for parameter in variables.parameters:
                self.opt_x_axe.children['menu'].add_command(label=parameter, command=lambda x=parameter: self.variable_x_axe.set(x))
                self.opt_y_axe.children['menu'].add_command(label=parameter, command=lambda x=parameter: self.variable_y_axe.set(x))
            if update:
                self.variable_x_axe.set(self.variable_x_axe.get())
                if self.variable_y_axe.get() != self.variable_x_axe.get():
                    self.variable_y_axe.set(self.variable_y_axe.get())
                else:
                    for parameter in variables.parameters:
                        if self.variable_x_axe.get() != str(parameter):
                            self.variable_y_axe.set(str(parameter))
            else:
                self.variable_x_axe.set(variables.parameters[0])
                self.variable_y_axe.set(variables.parameters[1])
            self.opt_x_axe.configure(state='normal')
            self.opt_y_axe.configure(state='normal')
        else:
            pass
        self.opt_x_axe.lift()
        self.opt_y_axe.lift()
        self.settings_label.lift()

    def get_graph_axes(self):
        """Sets the position of the currently active parameters inside the array to know which axes have to be visualized."""
        if len(variables.parameters) == 1:
            variables.x_axe_position = 0
        else:
            for index, value in enumerate(variables.parameters):
                if self.variable_x_axe.get() == str(value):
                    variables.x_axe_position = index
                    break
            if self.variable_y_axe.get() != self.variable_x_axe.get():
                for index, value in enumerate(variables.parameters):
                    if self.variable_y_axe.get() == str(value):
                        variables.y_axe_position = index
                        break
            else:
                for index, value in enumerate(variables.parameters):
                    if self.variable_x_axe.get() != str(value):
                        variables.y_axe_position = index

    def border(self):
        """Sets the complete considered interval."""
        lim_inf = self.minimum.get()
        if lim_inf:
            lim_inf = float(lim_inf.replace(',','.'))
        else:
            lim_inf = variables.x_axe_limit[0]
        lim_sup = self.maximum.get()
        if lim_sup:
            lim_sup = float(lim_sup.replace(',','.'))
        else:
            lim_sup = variables.x_axe_limit[1]
        variables.x_axe_limit = [lim_inf, lim_sup]
        variables.x_axe_limit_temp = variables.x_axe_limit
        if len(variables.parameters) > 1:
            variables.y_axe_limit = [lim_inf, lim_sup]
        variables.y_axe_limit_temp = variables.y_axe_limit
        self.restore_default()

    def _check_correct_parsing(self, constraints_parser, insert=False):
        if variables.constraints is not None:
            if insert:
                self.text.insert('1.0', variables.constraints)
            if settings.pre_sampling:
                constraints_parser.pre_sampling.pre_sampling()
        else:
            self.ready_label.configure(text='ERROR')

    def read_file(self):
        """Reads the constraints from the selected file and tries to parse them."""
        if self.file_path:
            self.file_path_label.configure(text=os.path.basename(self.file_path), anchor=tk.W)
            constraints_parser = ConstraintsParser()
            constraints_parser.parse_from_file(self.file_path)
            self.restore_default()
            self.text.delete('1.0', 'end-1c')
            self._check_correct_parsing(constraints_parser, True)

    def open_file(self):
        """Opens a SMT-LIB file (.smt2)."""
        self.file_path = tk.filedialog.askopenfilename(filetypes=[('SMT-LIB', '.smt2')])
        self.read_file()

    def reload_file(self):
        """Reloads the last opened SMT-LIB file (.smt2)."""
        self.read_file()

    def edit(self):
        """Sets the constraints from the text field as the new constraints."""
        text = self.text.get('1.0', 'end-1c')
        if self.text.compare('1.0', '!=', 'end-1c'):
            constraints_parser = ConstraintsParser()
            constraints_parser.parse_from_textfield(text)
            self.restore_default()
            self._check_correct_parsing(constraints_parser)

    @staticmethod
    def save():
        """Saves the constraints from the text field to a file (.smt2 by default)."""
        if variables.constraints is not None:
            path = tk.filedialog.asksaveasfilename(filetypes=[('SMT-LIB', '.smt2')], defaultextension='.smt2')
            if path:
                variables.solver.reset()
                variables.solver.add(variables.constraints)
                smt2_file = open(path, 'w')
                smt2_file.write(variables.solver.to_smt2())
                smt2_file.close()

    def increase_accuracy(self):
        """Increases the current accuracy."""
        variables.depth_limit += 1
        self.accuracy.config(text='Accuracy: 2^{}'.format(variables.depth_limit))

    def decrease_accuracy(self):
        """Decreases the current accuracy."""
        if variables.depth_limit > 1:
            variables.depth_limit -= 1
            self.accuracy.config(text='Accuracy: 2^{}'.format(variables.depth_limit))

    def set_splitting_heuristic(self, args=None): # pylint: disable=W0613 # argument is required
        """Sets the 'current splitting heuristic' option from the option menu.

        :param args: Event listener, defaults to None
        """
        splitting_heuristic.current_splitting_heuristic = self.current_splitting_heuristic.get()
        self.restore_default()

    def add_plot(self, figure):
        """Adds the navigation toolbar to the plot.

        :param figure: The plot as a root for the navigation toolbar.
        """
        self.line = FigureCanvasTkAgg(figure, master=self.frame12)

        toolbar_frame = tk.Frame(self.frame12, highlightbackground='black', highlightcolor='black', highlightthickness=1)
        toolbar_frame.grid(row=0, column=0, sticky=tk.NW, padx=(0,1), pady=(0,1))
        toolbar = NavigationToolbar2Tk(self.line, toolbar_frame)
        toolbar.config(background='white')
        toolbar._message_label.config(background='white') # pylint: disable=W0212 # only way to modify navigationtoolbar
        self.line = self.line.get_tk_widget()
        self.line.grid(row=0, column=0, sticky=tk.NW, padx=1,pady=1)

    def compute(self):
        """Computes the constraints, particularly tries to find safe and unsafe areas."""
        self.ready_label.configure(text='COMPUTING...')
        self.ready_label.update()
        self.computation_timer.create_timestamp('Computation')
        PaSyPy().main()
        self.computation_timer.calculate_time('Computation')
        self.computation_time.config(text='Computation Time         : {} sec.'.format(round(self.computation_timer.get_time('Computation'), 3)))

    def visualize(self):
        """Visualizes all safe, unsafe and unknown areas."""
        if not settings.skip_visualization:
            self.ready_label.configure(text='VISUALIZING...')
            self.ready_label.update()
            self.computation_timer.create_timestamp('Visualization')
            figure = Visualize().generate_graph()
            self.add_plot(figure)
            self.computation_timer.calculate_time('Visualization')
            self.visualization_time.config(text='Visualization Time         : {} sec.'.format(round(self.computation_timer.get_time('Visualization'), 3)))

    def start_calculation(self):
        """After checking pre-conditions, starts the calculation consisting of computation and visualization."""
        if variables.constraints is not None:
            self.get_graph_axes()
            if (self.changed or (variables.depth_limit > self.current_depth_limit)):
                if variables.sub_queue:
                    variables.queue.extend(variables.sub_queue)
                    variables.sub_queue = []
                if (variables.x_axe_limit_temp != variables.x_axe_limit) or (variables.y_axe_limit_temp != variables.y_axe_limit):
                    self.changed = True
                else:
                    self.changed = False
                self.compute()
                self.visualize()
                self.current_depth_limit = variables.depth_limit
                self.computed_accuracy.configure(text='Computed Accuracy      : 2^{}'.format(self.current_depth_limit))
            else:
                self.visualize()
            self.update_window()
            self.add_axes_field(update=True)
            self.ready_label.configure(text='FINISHED')

    def update_window(self):
        """Updates the information window."""
        green_area = self.area_calculation.calculate_area(variables.safe_area)
        self.number_of_green_boxes.config(text='Number of green boxes : {}'.format(len(variables.safe_area)))
        self.green_area.config(text='Green area                   : {:.2%}'.format(green_area))
        red_area = self.area_calculation.calculate_area(variables.unsafe_area)
        self.number_of_red_boxes.config(text='Number of red boxes     : {}'.format(len(variables.unsafe_area)))
        self.red_area.config(text='Red area                      : {:.2%}'.format(red_area))
        self.white_area_left.config(text='White area left              : {:.2%}'.format(1 - (green_area + red_area)))

    def restore_default(self):
        """Restores all relevant variables to default as they were at the beginning of the program."""
        boundaries = ()
        for _ in range(len(variables.parameters)):
            boundaries += (variables.x_axe_limit,)
        boundaries += (1,)
        variables.queue = [boundaries]
        variables.sub_queue = []
        variables.safe_area = []
        variables.unsafe_area = []
        self.add_empty_graph()
        self.add_axes_field()
        self.changed = True
        if variables.constraints is not None:
            self.ready_label.configure(text='READY')


if __name__ != '__main__':
    root = tk.Tk()
    app = MainApplication(root)

import os
import tkinter as tk
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.backends.backend_tkagg import NavigationToolbar2Tk
import matplotlib.pyplot as plt
import matplotlib
matplotlib.use('Agg')

from pasypy import variables, pasypy, constraints_parser, visualize, time



class MainApplication(tk.Frame):
    def __init__(self, parent, *args, **kwargs):
        tk.Frame.__init__(self, parent, *args, **kwargs)
        self.parent = parent

        self.parent.title('PaSyPy - Parameter Synthesis with Python')
        self.parent.geometry('1200x750')
        self.parent.minsize(1200, 750)
        # self.greeting = tk.Label(text='Parameter Synthesis with Python')
        self.parent.configure(background='white')

        self.frame_color = 'black'


        tk.Grid.rowconfigure(self.parent, index=0, weight=1)
        tk.Grid.columnconfigure(self.parent, index=0, weight=0)
        tk.Grid.columnconfigure(self.parent, index=1, weight=1)

        # START - FRAME 1 #
        self.frame1 = tk.Frame(background='white')     
        self.frame1.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)

        ## START - FRAME 1.1 #
        self.frame11 = tk.Frame(master=self.frame1, background='white')       
        self.frame11.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)

        ### START - FRAME 1.1.1 #
        self.frame111 = tk.Frame(master=self.frame11, background='black')       
        self.frame111.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))
        self.background_image = tk.PhotoImage(file='rwth_logo.png')
        self.background_label = tk.Label(self.frame111, image=self.background_image)
        self.background_label.grid(row=0, column=0, sticky=tk.NW, padx=1, pady=1)
        self.exit_button = tk.Button(self.frame111, text="Exit", command=self.parent.quit, width=10, height=2, bg='black', fg='white')
        self.exit_button.grid(row=0, column=0, sticky=tk.SW, padx=10, pady=10)
        
        tk.Grid.rowconfigure(self.frame111, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame111, index=0, weight=1)
        ### END - FRAME 1.1.1 #

        ### START - FRAME 1.1.2 #
        self.frame112 = tk.Frame(master=self.frame11, background='black')       
        self.frame112.grid(row=0, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=(10,0))

        #### START - FRAME 1.1.2.1 #
        self.frame1121 = tk.Frame(master=self.frame112, background='white')       
        self.frame1121.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1, pady=(1,0))
        self.ready_label1 = tk.Label(self.frame1121, text=">> STATUS <<", width=10, height=1, bg='black', fg='white')
        self.ready_label1.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=(5,0))
        self.ready_label = tk.Label(self.frame1121, text="WAITING", width=10, height=1, bg='black', fg='white')
        self.ready_label.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=(0,5))
        
        tk.Grid.rowconfigure(self.frame1121, index=0, weight=1)
        tk.Grid.rowconfigure(self.frame1121, index=1, weight=1)
        tk.Grid.columnconfigure(self.frame1121, index=0, weight=1)
        #### END - FRAME 1.1.2.1 #

        #### START - FRAME 1.1.2.2 #
        self.frame1122 = tk.Frame(master=self.frame112, background='white')
        self.frame1122.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1, pady=(0,1))
        self.update_graph_button = tk.Button(self.frame1122, text="Update\nGraph", command=self.update, bg="steel blue", fg="white",)
        self.update_graph_button.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
        self.compute_button = tk.Button(self.frame1122, text="Compute", command=self.update, bg="steel blue", fg="white",)
        self.compute_button.grid(row=0, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
        
        tk.Grid.rowconfigure(self.frame1122, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame1122, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame1122, index=1, weight=1)
        tk.Grid.columnconfigure(self.frame1122, index=2, weight=1)
        #### END - FRAME 1.1.2.2 #

        tk.Grid.rowconfigure(self.frame112, index=0, weight=1)
        tk.Grid.rowconfigure(self.frame112, index=1, weight=1)
        tk.Grid.columnconfigure(self.frame112, index=0, weight=1)
        ### END - FRAME 1.1.2 #

        tk.Grid.rowconfigure(self.frame11, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame11, index=0, weight=0)
        tk.Grid.columnconfigure(self.frame11, index=1, weight=1)
        ## END - FRAME 1.1 #

        tk.Grid.rowconfigure(self.frame1, index=0, weight=0)
        tk.Grid.rowconfigure(self.frame1, index=1, weight=0)
        tk.Grid.rowconfigure(self.frame1, index=2, weight=0)
        tk.Grid.rowconfigure(self.frame1, index=3, weight=0)
        tk.Grid.columnconfigure(self.frame1, index=0, weight=0)
        # END - FRAME 1 #


        ## START - FRAME 1.2 #
        self.frame12 = tk.Frame(master=self.frame1, background='black')     
        self.frame12.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)

        tk.Grid.rowconfigure(self.frame12, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame12, index=0, weight=1)
        ## END - FRAME 1.2 #

        ## START - FRAME 1.3 #
        self.frame13 = tk.Frame(master=self.frame1, background='black')
        self.frame13.grid(row=2, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)

        ### START - FRAME 1.3.1 #
        self.frame131 = tk.Frame(master=self.frame13, background='white')
        self.frame131.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1, pady=1)
        self.number_of_green_boxes = tk.Label(self.frame131, text='Number of green boxes : ', bg='forestgreen', fg='black', anchor=tk.W)
        self.number_of_green_boxes.grid(row=3, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))
        self.green_area = tk.Label(self.frame131, text='Green area                        : ', bg='forestgreen', fg='black', anchor=tk.W)
        self.green_area.grid(row=4, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))
        self.show_safe_area_button = tk.Button(self.frame131, text="X", command=self.show_safe_area, width=2, height=1, bg='forest green')
        self.show_safe_area_button.grid(row=3, column=0, rowspan=2, sticky=tk.E, padx=10)        
        self.number_of_red_boxes = tk.Label(self.frame131, text='Number of red boxes     : ', bg='firebrick', fg='black', anchor=tk.W)
        self.number_of_red_boxes.grid(row=5, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))
        self.red_area = tk.Label(self.frame131, text='Red area                           : ', bg='firebrick', fg='black', anchor=tk.W)
        self.red_area.grid(row=6, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))
        self.show_unsafe_area_button = tk.Button(self.frame131, text="X", command=self.show_unsafe_area, width=2, height=1, bg='firebrick')
        self.show_unsafe_area_button.grid(row=5, column=0, rowspan=2, sticky=tk.E, padx=10)
        self.white_area_left = tk.Label(self.frame131, text='White area left                 : ', bg='white', fg='black', anchor=tk.W)
        self.white_area_left.grid(row=7, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))
        
        tk.Grid.rowconfigure(self.frame131, index=0, weight=1)
        tk.Grid.rowconfigure(self.frame131, index=1, weight=1)
        tk.Grid.rowconfigure(self.frame131, index=2, weight=1)
        tk.Grid.rowconfigure(self.frame131, index=3, weight=1)
        tk.Grid.rowconfigure(self.frame131, index=4, weight=1)
        tk.Grid.columnconfigure(self.frame131, index=0, weight=1)
        ### END - FRAME 1.3.1 #

        ### START - FRAME 1.3.2 #
        self.frame132 = tk.Frame(master=self.frame13, background='white')
        self.frame132.grid(row=0, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), pady=1)
        self.time = tk.Label(self.frame132, text='Computation Time :', bg='black', fg='white', anchor=tk.W)
        self.time.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))
        # self.time2 = tk.Label(self.frame132, text='Visualization Time    :', bg='black', fg='white', anchor=tk.W)
        # self.time2.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))
        # self.time3 = tk.Label(self.frame132, text='Total Time                 :', bg='black', fg='white', anchor=tk.W)
        # self.time3.grid(row=2, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))
        
        tk.Grid.rowconfigure(self.frame132, index=0, weight=1)
        tk.Grid.rowconfigure(self.frame132, index=1, weight=1)
        tk.Grid.rowconfigure(self.frame132, index=2, weight=1)
        tk.Grid.columnconfigure(self.frame132, index=0, weight=1)
        ### END - FRAME 1.3.2 #

        ### START - FRAME 1.3.3 #
        self.frame133 = tk.Frame(master=self.frame13, background='white')
        self.frame133.grid(row=0, column=2, sticky=(tk.N+tk.E+tk.S+tk.W), padx=1, pady=1)

        #### START - FRAME 1.3.3.1 #
        self.frame1331 = tk.Frame(master=self.frame133, background='black')
        self.frame1331.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))
        self.accuracy = tk.Label(self.frame1331, text='Accuracy: 2^{}'.format(variables.depth_limit), bg='black', fg='white', anchor=tk.W)
        self.accuracy.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))
        self.increase_accuracy_button = tk.Button(self.frame1331, text="+", command=self.increase_accuracy, bg='white', fg='black')
        self.increase_accuracy_button.grid(row=0, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=15)
        self.decrease_accuracy_button = tk.Button(self.frame1331, text="-", command=self.decrease_accuracy, bg='white', fg='black')
        self.decrease_accuracy_button.grid(row=0, column=2, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=15)

        tk.Grid.rowconfigure(self.frame1331, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame1331, index=0, weight=1)
        #### END - FRAME 1.3.3.1 #

        #### START - FRAME 1.3.3.2 #
        self.frame1332 = tk.Frame(master=self.frame133, background='black')
        self.frame1332.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W))

        tk.Grid.rowconfigure(self.frame1332, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame1332, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame1332, index=1, weight=1)
        #### END - FRAME 1.3.3.2 #
        
        tk.Grid.rowconfigure(self.frame133, index=0, weight=1)
        tk.Grid.rowconfigure(self.frame133, index=1, weight=1)
        tk.Grid.columnconfigure(self.frame133, index=0, weight=1)
        ### END - FRAME 1.3.3 #

        tk.Grid.rowconfigure(self.frame13, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame13, index=0, weight=1)
        tk.Grid.columnconfigure(self.frame13, index=1, weight=1)
        tk.Grid.columnconfigure(self.frame13, index=2, weight=1)
        ## END - FRAME 1.3 #

        ## START - FRAME 1.4 #
        self.frame14 = tk.Frame(master=self.frame1, background='white')
        self.frame14.grid(row=3, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
        ## END - FRAME 1.4 #

        # START - FRAME 2 #
        self.frame2 = tk.Frame(background='black')   
        self.frame2.grid(row=0, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=(0,5), pady=(10,5))

        ## START - FRAME 2.1 #
        self.frame21 = tk.Frame(master=self.frame2, background='black')      
        self.frame21.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
        self.get_file_path_button = tk.Button(self.frame21, text="OPEN\nFILE", command=self.open_file, width=6, height=2, bg='gray', fg='white')
        self.get_file_path_button.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
        self.reload_file_button = tk.Button(self.frame21, text="RELOAD\nFILE", command=self.reload_file, width=6, height=2, bg='gray', fg='white')
        self.reload_file_button.grid(row=0, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
        self.text_button = tk.Button(self.frame21, text="EDIT", command=self.edit, width=6, height=2, bg='gray', fg='white')
        self.text_button.grid(row=0, column=2, sticky=tk.NW, padx=5, pady=5)
        self.save_button = tk.Button(self.frame21, text="SAVE", command=self.save, width=6, height=2, bg='gray', fg='white')
        self.save_button.grid(row=0, column=3, sticky=tk.NW, padx=5, pady=5)
        self.file_path_label = tk.Label(self.frame21, text="no file loaded", width=20, height=2, bg='black', fg='white')
        self.file_path_label.grid(row=0, column=4, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
        self.text1 = tk.Entry(self.frame21, width=5)
        self.text1.grid(row=0, column=5, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
        self.text2 = tk.Entry(self.frame21, width=5)
        self.text2.grid(row=0, column=6, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
        self.border_button = tk.Button(self.frame21, text="GET", command=self.border, width=6, height=2, bg='gray', fg='white')
        self.border_button.grid(row=0, column=7, sticky=tk.NW, padx=5, pady=5)
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

        self.line = 0

        self.add_empty_graph()
        self.add_empty_axes()

        self.file_path = None

        self.parent.bind('+', lambda _: self.increase_accuracy())
        self.parent.bind('-', lambda _: self.decrease_accuracy())
        self.parent.bind('<Escape>', lambda _: self.parent.quit())
        self.parent.bind('o', lambda _: self.open_file())
        self.parent.bind('r', lambda _: self.reload_file())
        self.parent.bind('<space>', lambda _: self.update())

        

    def add_axes_field(self, update=False):       
        self.opt_x_axe.children['menu'].delete(0, 'end')
        self.opt_y_axe.children['menu'].delete(0, 'end')
        
        if len(variables.parameters) == 1:
            self.opt_x_axe.children['menu'].add_command(label=variables.parameters[0], command=self.variable_x_axe.set(variables.parameters[0]))
        else:
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

        self.opt_x_axe.lift()
        self.opt_y_axe.lift()


    def border(self):
        lim_inf = self.text1.get()
        if lim_inf:
            lim_inf = float(lim_inf)
        else:
            lim_inf = variables.x_axe_limit[0]
        lim_sup = self.text2.get()
        if lim_sup:
            lim_sup = float(lim_sup)
        else:
            lim_sup = variables.x_axe_limit[1]
        variables.x_axe_limit = [lim_inf, lim_sup]
        variables.x_axe_limit_temp = variables.x_axe_limit
        if len(variables.parameters) > 1:
            variables.y_axe_limit = [lim_inf, lim_sup]
        variables.y_axe_limit_temp = variables.y_axe_limit
        
        self.restore_default()


    def add_empty_graph(self):
        self.add_plot(plt.figure())

        plt.xlim(variables.x_axe_limit)
        plt.ylim(variables.y_axe_limit)

    
    def add_empty_axes(self):
        self.variable_x_axe = tk.StringVar(self)
        self.opt_x_axe = tk.OptionMenu(self.frame12, self.variable_x_axe, *[''])
        self.opt_x_axe.configure(state='disabled')
        self.opt_x_axe.grid(row=0, column=0, sticky=tk.S, pady=5)
        
        self.variable_y_axe = tk.StringVar(self)
        self.opt_y_axe = tk.OptionMenu(self.frame12, self.variable_y_axe, *[''])
        self.opt_y_axe.configure(state='disabled')
        self.opt_y_axe.grid(row=0, column=0, sticky=tk.W, padx=5)


    def get_graph_axes(self):
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


    def read_file(self):
        if self.file_path:
            self.file_path_label.configure(text=os.path.basename(self.file_path))

            constraints_parser.parse_from_file(self.file_path)

            self.text.delete('1.0', 'end-1c')
            self.text.insert('1.0', variables.Constraints)

            self.restore_default()


    def restore_default(self):
        Bounds = ()
        for _ in range(len(variables.parameters)):
            Bounds += (variables.x_axe_limit,)
        Bounds += (1,)
        variables.Queue = [Bounds]
        variables.Sub_Queue = []
        variables.G = []
        variables.R = []

        self.add_empty_graph()

        self.add_axes_field()


    def open_file(self):        
        self.file_path = tk.filedialog.askopenfilename()
        self.read_file()

    def reload_file(self):
        self.read_file()


    def edit(self):
        text = self.text.get('1.0', 'end-1c')
        if self.text.compare('1.0', '!=', 'end-1c') and text != str(variables.Constraints):
            
            constraints_parser.parse_from_textfield(text)
            
            self.restore_default()


    def save(self):
        if variables.Constraints is not None:
            path = tk.filedialog.asksaveasfilename(defaultextension='.smt2')
            if path is not None:
                variables.solver.add(variables.Constraints)
                smt2_file = open(path, 'w')
                smt2_file.write(variables.solver.to_smt2())
                smt2_file.close()


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
        self.line = FigureCanvasTkAgg(figure, master=self.frame12)
        
        toolbar_frame = tk.Frame(self.frame12, highlightbackground='black', highlightcolor='black', highlightthickness=1)
        toolbar_frame.grid(row=0, column=0, sticky=tk.NW, padx=(0,1), pady=(0,1))
        toolbar = NavigationToolbar2Tk(self.line, toolbar_frame)
        toolbar.config(background='white')
        toolbar._message_label.config(background='white')
        self.line = self.line.get_tk_widget()
        self.line.grid(row=0, column=0, sticky=tk.NW, padx=1,pady=1)


    def start_computation_with_visualize_and_time(self):
        time.create_timestamp()
        pasypy.main()
        time.create_timestamp()
        time.calculate_time()
        self.time.config(text='Computation Time : {} sec.'.format(round(time.total_time, 3)))

        figure = visualize.generate_graph()
        self.add_plot(figure)
        self.update_window()


    def update(self):
        if variables.Constraints is not None:
            self.ready_label.configure(text='COMPUTING...')
            self.ready_label.update()
            self.get_graph_axes()

            if variables.Sub_Queue:
                variables.Queue.extend(variables.Sub_Queue)
                variables.Sub_Queue = []

            self.start_computation_with_visualize_and_time()

            self.add_axes_field(update=True)

            self.ready_label.configure(text='FINISHED')


    def reset(self):
        Bounds = ()
        for _ in range(len(variables.parameters)):
            Bounds += (variables.x_axe_limit,)
        Bounds += (1,)
        variables.Queue = [Bounds]
        variables.Sub_Queue = []
        variables.G = []
        variables.R = []

        self.line.destroy()

        self.start_computation_with_visualize_and_time()


    def update_window(self):
        green_area = pasypy.calculate_area(variables.G)
        self.number_of_green_boxes.config(text='Number of green boxes : {}'.format(len(variables.G)))
        self.green_area.config(text='Green area                        : {:.2%}'.format(green_area))

        red_area = pasypy.calculate_area(variables.R)
        self.number_of_red_boxes.config(text='Number of red boxes     : {}'.format(len(variables.R)))
        self.red_area.config(text='Red area                           : {:.2%}'.format(red_area))

        self.white_area_left.config(text='White area left                 : {:.2%}'.format(1 - (green_area + red_area)))


if __name__ != "__main__":
    root = tk.Tk()
    app = MainApplication(root)

import tkinter as tk
import webbrowser


hyperplane = False
colorblind_mode = False
white_boxes = False
hatch_pattern = False
skip_visualization = False

safe_color = 'forestgreen'
unsafe_color = 'firebrick'


class Settings(tk.Frame):
    def __init__(self, parent):
        tk.Frame.__init__(self, parent)
        self.parent = parent
        self.window = None

    def on_click(self, event=None):
        if not self.window:
            self.window = tk.Toplevel()
            self.window.title('Settings')
            self.window.protocol('WM_DELETE_WINDOW', self._top_closes)
            self.window.geometry('+%d+%d' % ((self.winfo_x() + 700), (self.winfo_y() + 300)))
            self.window.configure(background='white')
            self.window.transient(self)
            self.tk.call('wm', 'iconphoto', self.window._w, tk.PhotoImage(file='gear.png'))
            self.settings_frame = tk.Frame(master=self.window, background='black')     
            self.settings_frame.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)

            self.hyperplane = tk.BooleanVar()
            self.hyperplane_option = tk.Checkbutton(self.settings_frame, text='Hyperplane',variable=self.hyperplane, onvalue=True, offvalue=False, command=self.set_hyperplane_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.hyperplane_option.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            if hyperplane:
                self.hyperplane_option.select()

            self.hatch_pattern = tk.BooleanVar()
            self.hatch_pattern_option = tk.Checkbutton(self.settings_frame, text='Hatch Pattern',variable=self.hatch_pattern, onvalue=True, offvalue=False, command=self.set_hatch_pattern_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.hatch_pattern_option.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            if hatch_pattern:
                self.hatch_pattern_option.select()

            self.white_boxes = tk.BooleanVar()
            self.white_boxes_option = tk.Checkbutton(self.settings_frame, text='White Boxes',variable=self.white_boxes, onvalue=True, offvalue=False, command=self.set_white_boxes_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.white_boxes_option.grid(row=2, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            if white_boxes:
                self.white_boxes_option.select()

            self.colorblind_mode = tk.BooleanVar()
            self.colorblind_option = tk.Checkbutton(self.settings_frame, text='Colorblind',variable=self.colorblind_mode, onvalue=True, offvalue=False, command=self.set_colorblind_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.colorblind_option.grid(row=3, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            if colorblind_mode:
                self.colorblind_option.select()

            self.skip_visualization = tk.BooleanVar()
            self.skip_visualization_option = tk.Checkbutton(self.settings_frame, text='Skip Visualization',variable=self.skip_visualization, onvalue=True, offvalue=False, command=self.set_skip_visualization_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.skip_visualization_option.grid(row=4, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            if skip_visualization:
                self.skip_visualization_option.select()

            self.github = tk.PhotoImage(file='GitHub-Emblem.png')
            self.github_label = tk.Label(self.settings_frame, image=self.github, bg='black')
            self.github_label.grid(row=5, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            self.github_label.bind('<Button-1>', self.get_help)

            tk.Grid.rowconfigure(self.settings_frame, index=0, weight=1)
            tk.Grid.rowconfigure(self.settings_frame, index=1, weight=1)
            tk.Grid.rowconfigure(self.settings_frame, index=2, weight=1)
            tk.Grid.rowconfigure(self.settings_frame, index=3, weight=1)
            tk.Grid.rowconfigure(self.settings_frame, index=4, weight=1)
            tk.Grid.columnconfigure(self.settings_frame, index=0, weight=1)

            self.settings_frame.update()
            self.window.minsize((self.settings_frame.winfo_width() + 10), (self.settings_frame.winfo_height() + 10))

    def _top_closes(self, event=None):
        self.window.destroy()
        self.window = None

    def get_help(self, event=None):
        webbrowser.open('https://github.com/awiegel/PaSyPy')

    def set_hyperplane_option(self):
        global hyperplane
        hyperplane = self.hyperplane.get()
        self.parent.start_calculation()

    def set_colorblind_option(self):
        global colorblind_mode, safe_color, unsafe_color
        colorblind_mode = self.colorblind_mode.get()
        if not colorblind_mode:
            safe_color = 'forestgreen'
            unsafe_color = 'firebrick'
        else:
            safe_color = 'dodgerblue'
            unsafe_color = 'goldenrod'

        self.parent.number_of_green_boxes.config(bg=safe_color)
        self.parent.green_area.config(bg=safe_color)
        self.parent.show_safe_area_button.config(bg=safe_color)
        self.parent.number_of_red_boxes.config(bg=unsafe_color)
        self.parent.red_area.config(bg=unsafe_color)
        self.parent.show_unsafe_area_button.config(bg=unsafe_color)
        self.parent.start_calculation()

    def set_white_boxes_option(self):
        global white_boxes
        white_boxes = self.white_boxes.get()
        self.parent.start_calculation()

    def set_hatch_pattern_option(self):
        global hatch_pattern
        hatch_pattern = self.hatch_pattern.get()
        self.parent.start_calculation()

    def set_skip_visualization_option(self):
        global skip_visualization
        skip_visualization = self.skip_visualization.get()
        self.parent.add_empty_graph()
        self.parent.add_empty_axes()

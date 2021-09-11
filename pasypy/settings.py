"""Contains settings used by this tool."""

import tkinter as tk
import webbrowser

from pasypy import color
from pasypy.color import Color

pre_sampling = True # pylint: disable=C0103 # is not a constant
sampling = True # pylint: disable=C0103 # is not a constant
hyperplane = False # pylint: disable=C0103 # is not a constant
white_boxes = False # pylint: disable=C0103 # is not a constant
colorblind_mode = False # pylint: disable=C0103 # is not a constant
hatch_pattern = False # pylint: disable=C0103 # is not a constant
skip_visualization = False # pylint: disable=C0103 # is not a constant


class Settings(tk.Frame):
    """Contains settings used by this tool."""

    def __init__(self, parent):
        """Creates all attributes as empty elements."""
        tk.Frame.__init__(self, parent)
        self.parent = parent
        self.window = None
        self.settings_frame = None
        self.pre_sampling = None
        self.pre_sampling_option = None
        self.sampling = None
        self.sampling_option = None
        self.hyperplane = None
        self.hyperplane_option = None
        self.white_boxes = None
        self.white_boxes_option = None
        self.hatch_pattern = None
        self.hatch_pattern_option = None
        self.colorblind_mode = None
        self.colorblind_option = None
        self.skip_visualization = None
        self.skip_visualization_option = None
        self.github = None
        self.github_label = None

    def on_click(self, event=None): # pylint: disable=W0613 # argument is required
        """The settings window gets only created when clicked on the settings wheel.

        :param event: Event listener, defaults to None
        """
        if not self.window:
            self.window = tk.Toplevel()
            self.window.title('Settings')
            self.window.protocol('WM_DELETE_WINDOW', self._top_closes)
            self.window.geometry('+%d+%d' % ((self.winfo_x() + 700), (self.winfo_y() + 300)))
            self.window.configure(background='white')
            self.window.transient(self)
            self.tk.call('wm', 'iconphoto', self.window._w, tk.PhotoImage(file='images/gear.png')) # pylint: disable=W0212 # only way to modify navigationtoolbar
            self.settings_frame = tk.Frame(master=self.window, background='black')
            self.settings_frame.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)

            self.pre_sampling = tk.BooleanVar()
            self.pre_sampling_option = tk.Checkbutton(self.settings_frame, text='Pre-Sampling',variable=self.pre_sampling, onvalue=True, offvalue=False,
                                                            command=self.set_pre_sampling_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.pre_sampling_option.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            if pre_sampling:
                self.pre_sampling_option.select()

            self.sampling = tk.BooleanVar()
            self.sampling_option = tk.Checkbutton(self.settings_frame, text='Sampling',variable=self.sampling, onvalue=True, offvalue=False,
                                                            command=self.set_sampling_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.sampling_option.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            if sampling:
                self.sampling_option.select()

            self.hyperplane = tk.BooleanVar()
            self.hyperplane_option = tk.Checkbutton(self.settings_frame, text='Hyperplane',variable=self.hyperplane, onvalue=True, offvalue=False,
                                                    command=self.set_hyperplane_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.hyperplane_option.grid(row=2, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            if hyperplane:
                self.hyperplane_option.select()

            self.white_boxes = tk.BooleanVar()
            self.white_boxes_option = tk.Checkbutton(self.settings_frame, text='White Boxes',variable=self.white_boxes, onvalue=True, offvalue=False,
                                                     command=self.set_white_boxes_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.white_boxes_option.grid(row=3, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            if white_boxes:
                self.white_boxes_option.select()

            self.hatch_pattern = tk.BooleanVar()
            self.hatch_pattern_option = tk.Checkbutton(self.settings_frame, text='Hatch Pattern',variable=self.hatch_pattern, onvalue=True, offvalue=False,
                                                       command=self.set_hatch_pattern_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.hatch_pattern_option.grid(row=0, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            if hatch_pattern:
                self.hatch_pattern_option.select()


            self.colorblind_mode = tk.BooleanVar()
            self.colorblind_option = tk.Checkbutton(self.settings_frame, text='Colorblind',variable=self.colorblind_mode, onvalue=True, offvalue=False,
                                                    command=self.set_colorblind_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.colorblind_option.grid(row=1, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            if colorblind_mode:
                self.colorblind_option.select()

            self.skip_visualization = tk.BooleanVar()
            self.skip_visualization_option = tk.Checkbutton(self.settings_frame, text='Skip Visual',variable=self.skip_visualization, onvalue=True, offvalue=False,
                                                            command=self.set_skip_visualization_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.skip_visualization_option.grid(row=2, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            if skip_visualization:
                self.skip_visualization_option.select()

            self.github = tk.PhotoImage(file='images/GitHub-Emblem.png')
            self.github_label = tk.Label(self.settings_frame, image=self.github, bg='black')
            self.github_label.grid(row=3, column=1, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            self.github_label.bind('<Button-1>', self.get_help)

            tk.Grid.rowconfigure(self.settings_frame, index=0, weight=1)
            tk.Grid.rowconfigure(self.settings_frame, index=1, weight=1)
            tk.Grid.rowconfigure(self.settings_frame, index=2, weight=1)
            tk.Grid.rowconfigure(self.settings_frame, index=3, weight=1)
            tk.Grid.columnconfigure(self.settings_frame, index=0, weight=1)
            tk.Grid.columnconfigure(self.settings_frame, index=1, weight=1)

            self.settings_frame.update()
            self.window.minsize((self.settings_frame.winfo_width() + 10), (self.settings_frame.winfo_height() + 10))

    def _top_closes(self, event=None): # pylint: disable=W0613 # argument is required
        """Called when settings window is closed.

        :param event: Event listener, defaults to None
        """
        self.window.destroy()
        self.window = None

    def set_pre_sampling_option(self):
        """Sets the 'Pre-Sampling' option from the checkbox."""
        global pre_sampling # pylint: disable=C0103 # is not a constant
        pre_sampling = self.pre_sampling.get()

    def set_sampling_option(self):
        """Sets the 'Sampling' option from the checkbox."""
        global sampling # pylint: disable=C0103 # is not a constant
        sampling = self.sampling.get()

    def set_hyperplane_option(self):
        """Sets the 'hyperplane' option from the checkbox."""
        global hyperplane # pylint: disable=C0103 # is not a constant
        hyperplane = self.hyperplane.get()
        self.parent.start_calculation()

    def set_white_boxes_option(self):
        """Sets the 'white boxes' option from the checkbox."""
        global white_boxes # pylint: disable=C0103 # is not a constant
        white_boxes = self.white_boxes.get()
        self.parent.start_calculation()

    def set_hatch_pattern_option(self):
        """Sets the 'hatch pattern' option from the checkbox."""
        global hatch_pattern # pylint: disable=C0103 # is not a constant
        hatch_pattern = self.hatch_pattern.get()
        self.parent.start_calculation()

    def set_colorblind_option(self):
        """Sets the 'colorblind' option from the checkbox."""
        global colorblind_mode # pylint: disable=C0103 # is not a constant
        colorblind_mode = self.colorblind_mode.get()
        if not colorblind_mode:
            color.safe_color = Color.GREEN.value
            color.unsafe_color = Color.RED.value
        else:
            color.safe_color = Color.BLUE.value
            color.unsafe_color = Color.YELLOW.value

        self.parent.number_of_green_boxes.config(bg=color.safe_color)
        self.parent.green_area.config(bg=color.safe_color)
        self.parent.show_safe_area_button.config(bg=color.safe_color)
        self.parent.number_of_red_boxes.config(bg=color.unsafe_color)
        self.parent.red_area.config(bg=color.unsafe_color)
        self.parent.show_unsafe_area_button.config(bg=color.unsafe_color)
        self.parent.start_calculation()

    def set_skip_visualization_option(self):
        """Sets the 'skip visualization' option from the checkbox."""
        global skip_visualization # pylint: disable=C0103 # is not a constant
        skip_visualization = self.skip_visualization.get()

    @staticmethod
    def get_help(event=None): # pylint: disable=W0613 # argument is required
        """Opens the link to the official github project of this tool.

        :param event: Event listener, defaults to None
        """
        webbrowser.open('https://github.com/awiegel/PaSyPy')

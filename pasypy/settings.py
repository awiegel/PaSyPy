import tkinter as tk
import webbrowser

from pasypy import visualize

show_hyperplane = False
colorblind_mode = False

class Settings(tk.Frame):
    def __init__(self, parent, *args, **kwargs):
        tk.Frame.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        self.window = None


    def on_click(self, event=None):
        if not self.window:
            self.window = tk.Toplevel()
            self.window.title('Settings')
            
            self.window.geometry('+%d+%d' % ((self.winfo_x() + 700), (self.winfo_y() + 300)))
            self.window.configure(background='white')
            self.window.transient(self)
            self.testframe = tk.Frame(master=self.window, background='black')     
            self.testframe.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            tk.Grid.rowconfigure(self.window, index=0, weight=1)
            tk.Grid.columnconfigure(self.testframe, index=0, weight=1)
            
            self.window.protocol('WM_DELETE_WINDOW', self.top_closes)

            self.show_hyperplane = tk.BooleanVar()
            self.hyperplane_option = tk.Checkbutton(self.testframe, text='Hyperplane',variable=self.show_hyperplane, onvalue=True, offvalue=False, command=self.set_hyperplane_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.hyperplane_option.grid(row=0, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            
            if show_hyperplane:
                self.hyperplane_option.select()
            
            
            self.colorblind_mode = tk.BooleanVar()
            self.colorblind_option = tk.Checkbutton(self.testframe, text='Colorblind',variable=self.colorblind_mode, onvalue=True, offvalue=False, command=self.set_colorblind_option, font=('',10), bg='white', fg='black', anchor=tk.W)
            self.colorblind_option.grid(row=1, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            
            if colorblind_mode:
                self.colorblind_option.select()
            
            self.xdi = tk.PhotoImage(file='GitHub-Emblem.png')
            self.xd = tk.Label(self.testframe, image=self.xdi, bg='black')
            self.xd.grid(row=2, column=0, sticky=(tk.N+tk.E+tk.S+tk.W), padx=5, pady=5)
            self.xd.bind('<Button-1>', self.get_help)
            
            tk.Grid.rowconfigure(self.testframe, index=0, weight=1)
            tk.Grid.rowconfigure(self.testframe, index=1, weight=1)
            tk.Grid.rowconfigure(self.testframe, index=2, weight=1)
            tk.Grid.columnconfigure(self.testframe, index=0, weight=1)

            self.testframe.update()
            self.window.minsize((self.testframe.winfo_width() + 10), (self.testframe.winfo_height() + 10))


    def top_closes(self, event=None):
        self.window.destroy()
        self.window = None


    def get_help(self, event=None):
        webbrowser.open('https://github.com/awiegel/PaSyPy')


    def set_hyperplane_option(self):
        global show_hyperplane
        show_hyperplane = self.show_hyperplane.get()
        self.parent.start_calculation()


    def set_colorblind_option(self):
        global colorblind_mode
        colorblind_mode = self.colorblind_mode.get()
        if not colorblind_mode:
            visualize.safe_color = 'forestgreen'
            visualize.unsafe_color = 'firebrick'
        else:
            visualize.safe_color = 'dodgerblue'
            visualize.unsafe_color = 'goldenrod'
        
        self.parent.number_of_green_boxes.config(bg=visualize.safe_color)
        self.parent.green_area.config(bg=visualize.safe_color)
        self.parent.show_safe_area_button.config(bg=visualize.safe_color)
        
        self.parent.number_of_red_boxes.config(bg=visualize.unsafe_color)
        self.parent.red_area.config(bg=visualize.unsafe_color)
        self.parent.show_unsafe_area_button.config(bg=visualize.unsafe_color)
        
        self.parent.start_calculation()

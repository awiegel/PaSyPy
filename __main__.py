import os

if __name__ == "__main__":
    if not os.path.exists('logs'):
        os.makedirs('logs')

    open('logs/safe_area.log', 'w').close()
    open('logs/unsafe_area.log', 'w').close()

    from pasypy import gui
    gui.root.mainloop()

# cross platform support for opening files (for example images)
import sys


def get_command_for_open():
    if sys.platform == 'win32':
        return 'start'
    elif sys.platform == 'darwin':
        return 'open'
    else:
        return 'xdg-open'

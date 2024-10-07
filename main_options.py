import sys


DEFINED_FLAGS = ["-pre", "-VC", "-inner", "-weak_post", "-run"]


def get_main_options():
    flags = {opt[1:]: False for opt in DEFINED_FLAGS}

    index = 2
    while index < len(sys.argv):
        opt = sys.argv[index]
        if opt not in DEFINED_FLAGS:
            print(f"Error: unrecognized flag {opt}")
            exit()
        else: 
            flags[opt[1:]] = True

        index += 1

    return flags




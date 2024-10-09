import sys


DEFINED_FLAGS = ["-pre", "-VC", "-inner", "-weak_post", "-run", "-ignore_unknown", "-annot"]

true_values = {"true", "1", "yes", "on"}
false_values = {"false", "0", "no", "off"}

def get_main_options():

    flags = {opt[1:]: False for opt in DEFINED_FLAGS}
    index = 1
    while index < len(sys.argv):
        arg = sys.argv[index]
        
        if arg.startswith('-'):  # Identify a flag
            if arg not in DEFINED_FLAGS:
                print(f"Error: unrecognized flag {arg}")
                exit()
            # Check for a value associated with the flag
            if index + 1 < len(sys.argv) and not sys.argv[index + 1].startswith('-'):
                value = sys.argv[index + 1].lower()
                # Handle 'true' and 'false' values
                if value in true_values:
                    flags[arg[1:]] = True
                elif value in false_values:
                    flags[arg[1:]] = False
                else:
                    print(f"Error: invalid value: {value} for flag: {arg}")
                    exit()
                index += 2  # Move past the value
            else:
                flags[arg[1:]] = True  # If no value, just set the flag as True
                index += 1
        else:
            index += 1
    
    return flags






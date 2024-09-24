
from Parser.parser_node import ParserNode
from Parser.Tokenizer.tokens import Token



LOGICAL_COMMANDS = ["assert", "assume", "inv"]

# function that accepts a block, and checks that all function applications 
# in the block are valid. Note that logical funcions will not be defined, thus they 
# will not be known to the parser. 
# In addition, a value of (-1) in the parsing_environment means a 
# function is illegal to use.
# return None if there is no problem, 
# else the block with the problem and a string expressing the problem
def function_applications_legal(block: ParserNode, 
                                parsing_environment: dict[str, int] = None, 
                                allow_logical: bool = False):
    if block is None:
        return
    
    if parsing_environment is None:
        parsing_environment = {}

    if block.name == "apply":

        func_name, func_param = block.children
        func_name = func_name.value.value

        if func_param is None:
            func_param = []
        elif func_param.name == "comma":
            func_param = func_param.children
        else:
            func_param = [func_param]
        
        num_params = len(func_param)

        if func_name in parsing_environment:
            # we know this function. Make sure we have the correct number of params
            if parsing_environment[func_name] == -1:
                return block, f"Illegal use of {func_name} (in the pre/post condition of {func_name})"
            if parsing_environment[func_name] != num_params:
                return block, f"{func_name} exprects {parsing_environment[func_name]} parameters, got {num_params}"
        else:
            # we don't know the function, but maybe we allow logical functions
            if not allow_logical:
                return block, f"unkown function {func_name}"
    
    elif block.name == "seq":
        # in this case we need to first scan all children to gather 
        # all function definitions, and then continue
        for child in block.children:
            if child.name == "def":
                func_name = child.children[0].value.value
                func_param = child.children[1]
                
                if func_param is None:
                    num_params = 0
                elif func_param.name == "comma":
                    num_params = len(func_param.children)
                else:
                    num_params = 1
                
                parsing_environment[func_name] = num_params

    elif block.name == "def":
        # in this case, just make sure the assume/assert statements do not 
        # contain the function itself
        func_name, func_params, func_pre, func_code, func_post = block.children
        old = parsing_environment[func_name.value.value]
        parsing_environment[func_name.value.value] = -1
        
        # verify the pre and post
        validity = function_applications_legal(func_pre, parsing_environment.copy(), True) 
        if validity != None:
            return validity
        
        validity = function_applications_legal(func_post, parsing_environment.copy(), True) 
        if validity != None:
            return validity

        parsing_environment[func_name.value.value] = old 
        return function_applications_legal(func_code, parsing_environment.copy(), allow_logical)

    allow_logical = allow_logical or block.name in LOGICAL_COMMANDS
    for child in block.children:
        validity = function_applications_legal(child, parsing_environment.copy(), allow_logical) 
        if validity != None:
            return validity



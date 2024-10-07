
from Interpereter.enviornment import Enviornment
from Parser.parser_node import ParserNode, POSSIBLE_NODE_NAMES


"""
POSSIBLE_NODE_NAMES = [
    "op+", "op-", "op*", "op/", "op&&", "op||", "leaf",       # expression types
    "while", "if", "skip", "assign", "assert", "inv", "seq",  # command types
    "print"  
]
"""


infix_to_function = {
    "op+": lambda x, y: x + y,
    "op-": lambda x, y: x - y,
    "op*": lambda x, y: x * y,
    "op/": lambda x, y: x / y,
    "op>": lambda x, y: int(x>y),
    "op<": lambda x, y : int(x<y),
    "op<=": lambda x, y: int(x<=y),
    "op>=": lambda x, y: int(x>=y),
    "op=": lambda x, y: int(x==y),
    "op!=": lambda x, y: int(x!=y),
    "op&&": lambda x, y: x and y,
    "op||": lambda x, y: x or y,
    "op->": lambda x, y: (not x) or y,
}

prefix_to_function = {
    "op+": lambda x: x,
    "op-": lambda x: - x,
    "op!": lambda x: int(x == 0)
}

# return: if success :  0, env
#         else       :  1, error_message
def pattern_match(params, function_params):
    if function_params.name == "comma":
        if type(params) != list:
            return 1, f"function expects {len(function_params)} parameters"
        
        function_params = function_params.children
        if len(params) != len(function_params):
            return 1, f"function expects {len(function_params)} parameters"
        
        env = Enviornment()
        for (func_param, value) in zip(function_params, params):
            env[func_param.value.value] = value

        return 0, env
    
    else:
        if type(params) == list:
            return 1, "function expects single parameter"
        env = Enviornment()
        env[function_params.value.value] = params
        return 0, env


# for success: 0, value, None
# for error:   1, error_msg, token
def evaluate(node: ParserNode, env: Enviornment):

    # print(f"evaluating {node} in env {env}")

    if node.name == "leaf":
        if node.value.name == "int":
            return 0, int(node.value.value), None
        elif node.value.name == "var":
            var = node.value.value
            if var not in env:
                return 1, f"variable {var} not defined.", node.value
            return 0, env[var], None
        else:
            return 1, f"{node.value} unrecognized leaf type", node.value
    
    elif node.name == "op&&":
        left, right = node.children
        fail, left_value, tok = evaluate(left, env)
        if fail:
            return fail, left_value, tok
        if not left_value:
            return 0, left_value, None
        fail, right_value, tok = evaluate(right, env)
        if fail:
            return fail, right_value, tok
        return 0, right_value, None
        
    elif node.name == "op||":
        left, right = node.children
        fail, left_value, tok = evaluate(left, env)
        if fail:
            return fail, left_value, tok
        if left_value:
            return 0, left_value, None
        fail, right_value, tok = evaluate(right, env)
        if fail:
            return fail, right_value, tok
        return 0, right_value, None
    
    elif node.name[:2] == "op":
        
        if len(node.children) == 1:
            if node.name not in prefix_to_function:
                return 1, f"unrecognized prefix {node.name}"
            fail, child_val, tok = evaluate(node.children[0], env)
            if fail:
                return fail, child_val, tok
            return 0, prefix_to_function[node.name](child_val), None
        
        elif len(node.children) == 2:
            if node.name not in infix_to_function:
                return 1, f"unrecognized infix {node.name}"
            fail, left_val, tok = evaluate(node.children[0], env)
            if fail:
                return fail, left_val, tok
            
            fail, right_value, tok = evaluate(node.children[1], env)
            if fail:
                return fail, right_value, tok
            
            if node.name == "op/" and right_value == 0:
                return 1, "division by 0", node.value
            
            return 0, infix_to_function[node.name](left_val, right_value), None

    elif node.name == "comma":
        children_values = []
        for child in node.children:
            fail, child_value, token = evaluate(child, env)
            if fail:
                return fail, child_val, token
            
            children_values.append(child_value)
        
        return 0, children_values, None

    elif node.name == "apply":

        name, params = node.children
        if name.value.value not in env.functions:
            return 1, f"fucntion {name.value.value} not defined.", node.value
        
        # print(name, params)

        func = env.functions[name.value.value]
        func_name, func_params, func_pre, func_body, func_post = func.children

        fail, params, tok = evaluate(params, env)
        if fail:
            return fail, params, tok

        fail, new_env = pattern_match(params, func_params)
        if fail:
            return fail, new_env, node.value
        
        fail, returned = execute(func_body, new_env)

        if fail:
            return (fail, 
                    f"Error in function call in " + \
                    f"{node.value.lineno}.{node.value.charno}: {returned}",
                    node.value)
        
        if returned == None:
            returned = 0

        return fail, returned, tok

    return 1, f"unrecognized operator {node.name}", node
    


# for success return 0, value (if there was a return statement)
# for failure return 1, error_msg
def execute(node: ParserNode, env=None):
    if env == None:
        env = Enviornment()

    if node.name == "while":
        cond_exp, while_inv, while_body = node.children
        while True:
            fail, cond_val, tok = evaluate(cond_exp, env)
            if fail:
                return fail,  f"Error in {tok.lineno}.{tok.charno}: {cond_val}"
            if not cond_val:
                break
            
            if while_inv != None:
                fail, inv_val, tok = evaluate(while_inv, env)
                if fail:
                    return fail,  f"Error in {tok.lineno}.{tok.charno}: {cond_val}"
                if not inv_val:
                    return 1, f"Inv Error in {while_inv.value.lineno}.{while_inv.value.charno}."

            fail, error_msg = execute(while_body, env)
            if fail:
                return fail, error_msg

        return 0, None

    elif node.name == "if":
        cond_exp, then_body, else_body = node.children
        
        fail, cond_val, tok = evaluate(cond_exp, env)
        if fail:
            return fail,  f"Error in {tok.lineno}.{tok.charno}: {cond_val}"
        
        if_body = else_body
        if cond_val:
            if_body = then_body
        
        fail, error_msg = execute(if_body, env)
        if fail:
            return fail, error_msg
        
        return 0, None

    elif node.name in ["skip", "forall"]:
        return 0, None

    elif node.name == "assign":
        var, exp = node.children
        
        fail, value, tok = evaluate(exp, env)
        if fail:
            return fail,  f"Error in {tok.lineno}.{tok.charno}: {value}"
        
        env[var.value.value] = value

        return 0, None

    elif node.name == "print":
        exp, = node.children
        
        fail, value, tok = evaluate(exp, env)
        if fail:
            return fail,  f"Error in {tok.lineno}.{tok.charno}: {value}"
        
        print("PRINT FROM WHILE:", value)

        return 0, None
    
    elif node.name == "error":
        return 1, f"Error thrown in line {node.value.lineno}"

    elif node.name in ["assert", "inv"]:
        exp = node.children[0]
        
        fail, value, tok = evaluate(exp, env)
        if fail:
            return fail,  f"Error in {tok.lineno}.{tok.charno}: {value}"
        
        if not value:
            return 1, f"Assert Error in {node.value.lineno}.{node.value.charno}."

        return 0, None

    elif node.name == "assume" :
        exp = node.children[0]
        
        fail, value, tok = evaluate(exp, env)
        if fail:
            return fail,  f"Error in {tok.lineno}.{tok.charno}: {value}"
        
        if not value:
            print(f"Assume Warning: the assumption failed in line"
                  f"{node.value.lineno}.{node.value.charno}")

        return 0, None

    elif node.name == "seq":
        returned = None
        
        for child in node.children:
            fail, returned = execute(child, env)
            if fail:
                return fail, returned
        
        return 0, returned

    elif node.name == "return":
        ret_expression = node.children[0]
        fail, value, tok = evaluate(ret_expression, env)
        if fail:
            return fail,  f"Error in {tok.lineno}.{tok.charno}: {value}"
        
        return 0, value

    elif node.name == "def":
        print(node.children)
        func_name, _, _, _, _ = node.children
        env.functions[func_name.value.value] = node

    else:
        return 1, f"Error in {node.value.lineno}.{node.value.charno}: unrecognized command: {node.name}"

    return 0, None


from Interpereter.enviornment import Enviornment
from Parser.parser_node import ParserNode, POSSIBLE_NODE_NAMES
from Interpereter.evaluate import evaluate

"""
POSSIBLE_NODE_NAMES = [
    "op+", "op-", "op*", "op/", "op&&", "op||", "leaf",       # expression types
    "while", "if", "skip", "assign", "assert", "inv", "seq",  # command types
    "print"  
]
"""


# for success return 0, None
# for failure return 1, error_msg
def execute(node: ParserNode, env=None):
    if env == None:
        env = Enviornment()

    if node.name == "while":
        cond_exp, while_body = node.children
        while True:
            fail, cond_val, tok = evaluate(cond_exp, env)
            if fail:
                return fail,  f"Error in {tok.lineno}.{tok.charno}: {cond_val}"
            if not cond_val:
                break

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

    elif node.name == "skip":
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
    
    elif node.name in ["assert", "inv", "assume"]:
        exp = node.children[0]
        
        fail, value, tok = evaluate(exp, env)
        if fail:
            return fail,  f"Error in {tok.lineno}.{tok.charno}: {value}"
        
        if not value:
            return 1, f"Assert Error in {node.value.lineno}.{node.value.charno}."

        return 0, None

    elif node.name == "seq":
        for child in node.children:
            fail, error_msg = execute(child, env)
            if fail:
                return fail, error_msg
        
        return 0, None

    else:
        return 1, f"Error in {node.value.lineno}.{node.value.charno}: unrecognized command: {node.name}"


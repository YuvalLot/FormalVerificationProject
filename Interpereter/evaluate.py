
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
}

prefix_to_function = {
    "op+": lambda x: x,
    "op-": lambda x: - x,
    "op!": lambda x: int(x == 0)
}

# for success: 0, value, None
# for error:   1, error_msg, token
def evaluate(node: ParserNode, env: Enviornment):
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

    return 1, f"unrecognized operator {node.name}", node
    





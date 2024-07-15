
from Parser.parser_node import ParserNode
from Parser.Tokenizer.tokens import Token


INFIXES = {
    "op+": 5,
    "op-": 5,
    "op*": 3, 
    "op/": 3, 
    "op>": 7,
    "op<": 7,
    "op>=": 7,
    "op<=": 7,
    "op=": 9
}

PREFIXES = ["op+", "op-"]

OPERATORS = set(INFIXES.keys())

IDENTIFIERS = ["var", "int"]

def collapse_once(node_stack, op_stack):
    if op_stack[-1][1] == "P":
        op = op_stack.pop()[0]
        top = node_stack.pop()
        node_stack.append(ParserNode(
            op.name, op, [top], is_expression=True
        ))
    elif op_stack[-1][1] == "I":
        op = op_stack.pop()[0]
        if len(node_stack) < 2:
            op_stack.append((op, "I"))
            return 1
        first, second = node_stack.pop(), node_stack.pop()
        node_stack.append(ParserNode(
            op.name, op, [second, first], is_expression=True
        ))
    elif op_stack[-1][1] == "LP":
        pass
    else:
        return 1
    
    return 0


def parse_expression(block: list[Token]):
    node_stack = []
    op_stack = []
    last_added = 1  # 0 for node, 1 for operator

    for tok in block:
        if tok.name in IDENTIFIERS:
            if last_added == 0:
                top = node_stack.pop()
                node_stack.append(
                    ParserNode("apply", tok, [top], is_expression=True)
                )
            else:
                node_stack.append(
                    ParserNode("leaf", tok, [], is_expression=True)
                )
            last_added = 0
 
        elif tok.name in OPERATORS:
            if last_added == 1:
                # must interperatr as an infix
                if tok.name not in PREFIXES:
                    return tok, f"{tok.value} not a prefix"
                op_stack.append((tok, 'P'))
            else:
                # infix 
                while len(op_stack) > 0 and op_stack[-1][1] != "LP" and \
                    (op_stack[-1][1] == "P" or 
                        INFIXES[op_stack[-1][0].name] <= INFIXES[tok.name]):
                    # can't add due to precedence
                    # must collapse 
                    collapse_once(node_stack, op_stack)

                op_stack.append((tok, "I"))
            last_added = 1

        elif tok.name == "lparen":
            op_stack.append((tok, "LP"))
            last_added = 1

        elif tok.name == "rparen":
            if last_added == 1:
                return tok, "Cannot close"      

            while len(op_stack) > 0 and op_stack[-1][1] != "LP":
                if collapse_once(node_stack, op_stack) == 1:
                    return op_stack[-1][0], "Illegal token"
            
            if len(op_stack) == 0:
                return tok, "unopened RP"
            
            op_stack.pop()

            last_added = 0          

        
        else:
            return tok, "unrecognized token"
    
    while len(op_stack) > 0:
        if collapse_once(node_stack, op_stack) == 1:
            return op_stack[-1][0], "Illegal token"

    if len(node_stack) != 1:
        return None, "Empty Expression"
    
    return node_stack[0]
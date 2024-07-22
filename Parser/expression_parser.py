
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
    "op=": 9,
    "op!=": 9,
    "op&&": 11,
    "op||": 11,
}

PREFIXES = ["op+", "op-", "op!"]

OPERATORS = set(INFIXES.keys())
OPERATORS.add("op!")

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


# given a mathematical expression (in infix notation)
# produce a parsing tree of the expression
# for success, return (0, expression, None)
# for failure, return (1, error_token, error_message)
def parse_expression(block: list[Token]):
    node_stack = []  # stack for nodes (expression)
    op_stack = []  # stack for operations
    last_added = 1  # 0 for node, 1 for operator

    for tok in block:
        if tok.name in IDENTIFIERS:
            if last_added == 0:
                # two nodes added one after the other, 
                # for now interpert as application of first on second
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
                    return 1, tok, f"{tok.value} not a prefix"
                op_stack.append((tok, 'P'))
            else:
                # infix 
                if tok.name not in INFIXES:
                    return 1, tok, f"{tok.value} not an infix"
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
                return 1, tok, "illegal rparen"      

            while len(op_stack) > 0 and op_stack[-1][1] != "LP":
                if collapse_once(node_stack, op_stack) == 1:
                    return 1, op_stack[-1][0], "Illegal token"
            
            if len(op_stack) == 0:
                return 1, tok, "unopened RP"
            
            op_stack.pop()

            last_added = 0          

        
        else:
            return 1, tok, "unrecognized token"
    
    while len(op_stack) > 0:
        if collapse_once(node_stack, op_stack) == 1:
            return 1, op_stack[-1][0], "Illegal token"

    if len(node_stack) != 1:
        return 1, block[0], "Illegal expression"
    
    return 0, node_stack[0], None
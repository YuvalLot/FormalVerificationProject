
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
    "op&&": 13,
    "op||": 15,
    "op->": 11,
    "comma": 17
}

PREFIXES = ["op+", "op-", "op!"]

OPERATORS = set(INFIXES.keys())
OPERATORS.add("op!")
OPERATORS.add("comma")

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
        
        # NOTE: design 'problem': should ((1,2), 3) be different from (1,(2,3)),
        #       should we even allow nested commas? 
        if op.name == "comma":
            first, second = node_stack.pop(), node_stack.pop()

            if first.value.name == "comma":
                first_children = first.children
            else:
                first_children = [first]

            if second.value.name == "comma":
                second_children = second.children
            else:
                second_children = [second]

            node_stack.append(
                ParserNode(op.name, op, second_children + first_children, is_expression=True)
            )
            return 0
            

        else:

            first, second = node_stack.pop(), node_stack.pop()
            if first.name == "comma" or second.name == "comma":
                op_stack.append((op, "I"))
                return 1  # can't do operations on commas
            
            node_stack.append(ParserNode(
                op.name, op, [second, first], is_expression=True
            ))

    elif op_stack[-1][1] in ["LP0", "LP1"]:
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
                if top.name != "leaf" or top.value.name != "var":
                    return 1, top.value, f"{str(top)} is not applciable"
                value_node = ParserNode("leaf", tok, [], is_expression=True)
                node_stack.append(
                    ParserNode("apply", top.value, [top, value_node], is_expression=True)
                )
            else:
                node_stack.append(
                    ParserNode("leaf", tok, [], is_expression=True)
                )
            last_added = 0
 
        elif tok.name in OPERATORS:
            if last_added == 1:
                # must interperatr as an prefix
                if tok.name not in PREFIXES:
                    return 1, tok, f"{tok.value} not a prefix"
                op_stack.append((tok, 'P'))
            else:
                # infix 
                if tok.name not in INFIXES:
                    return 1, tok, f"{tok.value} not an infix"
                while len(op_stack) > 0 and op_stack[-1][1] not in ["LP0", "LP1"] and \
                    (op_stack[-1][1] == "P" or 
                        INFIXES[op_stack[-1][0].name] <= INFIXES[tok.name]):
                    # can't add due to precedence
                    # must collapse 
                    if collapse_once(node_stack, op_stack):
                        return 1, tok, f"{op_stack[-1][0].value} not used properly"

                op_stack.append((tok, "I"))
            last_added = 1

        elif tok.name == "lparen":
            op_stack.append((tok, f"LP{last_added}"))
            last_added = 1

        elif tok.name == "rparen":

            if last_added == 1:
                # operator right before a right parantheses is illegal,
                # unless we have a function application with no parameters
                # e.g., f () 
                if op_stack[-1][1] == "LP0":
                    op_stack.pop()
                    identifer = node_stack.pop()
                    if identifer.name != "leaf" and identifer.value.name != "var":
                        return 1, identifer.value, "illegal function"  
                    node_stack.append(
                        ParserNode("apply", identifer.value, [identifer, None], is_expression=True)
                    )
                    last_added = 0      
                    continue

                return 1, tok, "illegal rparen"      

            while len(op_stack) > 0 and op_stack[-1][1] not in ["LP0", "LP1"]:
                if collapse_once(node_stack, op_stack) == 1:
                    return 1, tok, f"{op_stack[-1][0].value} not used properly"

                
            if len(op_stack) == 0:
                return 1, tok, "unopened RP"
            
            LP = op_stack.pop()
            if LP[1] == "LP0":
                # function application
                first, second = node_stack.pop(), node_stack.pop()
                if second.name != "leaf" or second.value.name != "var":
                    return 1, second.value, "illegal function"
                node_stack.append(
                    ParserNode("apply", second.value, [second, first], is_expression=True)
                )

            last_added = 0          

        
        else:
            return 1, tok, "unrecognized token"
    
    while len(op_stack) > 0:
        if collapse_once(node_stack, op_stack) == 1:
            return 1, tok, f"{op_stack[-1][0].value} not used properly"

    while len(node_stack) > 1:
        first, second = node_stack.pop(), node_stack.pop()
        if second.value.name == "var":
            node_stack.append(
                ParserNode("apply", second.value, [second, first], is_expression=True)
            )
        else:
            return 1, second.value, f"{second.value.value} is not applciable"
    
    return 0, node_stack[0], None
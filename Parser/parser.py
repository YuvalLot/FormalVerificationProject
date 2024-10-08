
from Parser.parser_node import ParserNode
from Parser.Tokenizer.tokens import Token

from Parser.expression_parser import parse_expression
from Parser.command_parser import parse_command

from Parser.validate_functions import functions_legal


STRUCTURE_TOKENS = [
    "semi", "lcurly", "rcurly", "if", "then", "else", "while",

    "assign", "skip", "assert", "inv", "print", "assume", "error",
    "def", "return", "forall", "::"
]


# if there is an error, return the token where the parsing error occurs,
# and a string describing the error
# for success, return (0, command)
# for error, return (1, error_msg)
def parse(token_list: list[Token]):
    
    # first, split by structure tokens
    blocks = []
    curr = []
    for tok in token_list:
        if tok.name in STRUCTURE_TOKENS:
            if len(curr) > 0:
                blocks.append(curr)
            blocks.append(tok)
            curr = []
        else:
            curr.append(tok)

    for (i, block) in enumerate(blocks):
        if type(block) == Token:
            continue
        block : list[Token]
        # not in a structure token
        # hence we are in an expression, which we need to parse like expressions 
        # for this we use the infix to postfix algorithm 
        failure, expression, msg = parse_expression(block)
        if failure:
            return 1, f"Parsing Error in {expression.lineno}.{expression.charno}: {msg}"
        
        blocks[i] = expression
    
    # now parse the commands
    fail, end, command = parse_command(0, blocks)
    if fail:
        lineno, charno = 0, 0
        if type(end) == Token:
            lineno, charno = end.lineno, end.charno
        else:
            lineno, charno =end.value.lineno, end.value.charno
        return 1, f"Error in {lineno}.{charno}: {command}"
    
    if end != len(blocks):
        lineno, charno = 0, 0
        if type(end) == Token:
            lineno, charno = blocks[end].lineno, blocks[end].charno
        else:
            lineno, charno = blocks[end].value.lineno, blocks[end].value.charno
        return 1, f"EOF error in {lineno}.{charno}."

    # now go back and check that all of the expressions are valid
    valid_funcs = functions_legal(command)
    if valid_funcs is not None:
        block, msg = valid_funcs
        return 1, f"Parsing error in {block.value.lineno}.{block.value.charno}: {msg}"

    return 0, command

    






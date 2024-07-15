
from Parser.parser_node import ParserNode
from Parser.Tokenizer.tokens import Token

from Parser.expression_parser import parse_expression


STRUCTURE_TOKENS = [
    "semi", "lcurly", "rcurly", "if", "then", "else", "while", "do",
    "assign",
]


def lower_grade(blocks: list[(Token | ParserNode, int)], maximal_grade: int):
    for index in len(blocks):
        
        block, grade = blocks[index]
        if grade == maximal_grade:
            pass


# if there is an error, return the token where the parsing error occurs,
# and a string describing the error
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
    
    if len(curr) > 0:
        return Token("EOF", "EOF", float("inf"), float("inf")), "EOF error"

    for (i, block) in enumerate(blocks):
        if type(block) == Token:
            continue
        block : list[Token]
        # not in a structure token
        # hence we are in an expression, which we need to parse like expressions 
        # for this we use the infix to postfix algorithm 
        expression = parse_expression(block)
        if type(expression) != ParserNode:
            return expression
        
        blocks[i] = expression
    
    # now we want to grade seperate our blocks
    graded_blocks = []
    num = maximal_grade = 0
    for block in blocks:
        if type(block) == Token and block.name == "lcurly":
            num += 1
            maximal_grade = max(num, maximal_grade)
        elif type(block) == Token and block.name == "rcurly":
            num -= 1
            if num < 0:
                return block, "unopened rcurly"
        else:
            graded_blocks.append(
                (block, num)
            )

    for block, num in graded_blocks:
        print("\t"*num + str(block))

    # parse each grade seperately
    for _ in range(maximal_grade):
        
    






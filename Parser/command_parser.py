
from Parser.parser_node import ParserNode
from Parser.Tokenizer.tokens import Token


def is_token(block, name: str):
    return type(block) == Token and block.name == name

def is_expression(block):
    return type(block) == ParserNode and block.is_expression


# gets a list of blocks, and returns a list of blocks that parse
# the code in the current nested level (i.e., until the first unopened } or EOF)
# Success case: returns (0, next_position: int, Parsed Command)
# Failure case: returns (1, failed token or None, string describing error)
def parse_command(curr_pos: int, blocks: list):
    commands = []
    i = curr_pos
    block = None

    while i < len(blocks):
        block = blocks[i]
        if is_token(block, "while"):
            # we're in a while
            # we expect:
            #  while [cond_exp] do {...} ;
            if i + 3 >= len(blocks) or \
                 not is_expression(blocks[i + 1]) or \
                 not is_token(blocks[i + 2], "lcurly"):
                
                error_msg = "Illegal While Structure"
                if i + 3 >= len(blocks):
                    error_msg = "Not enough tokens after while"
                if not is_expression(blocks[i + 1]):
                    error_msg = "While should be followed with a conditional expression"
                if not is_token(blocks[i+2], "lcurly"):
                    error_msg = "While (cond) should be followed by left curly braces"
                return 1, block, error_msg
            
            while_cond = blocks[i + 1]

            # parse the inner while command
            succ, i, while_command = parse_command(i + 3, blocks)
            if succ:
                return succ, i, while_command
            # assert it ends with an rcurly, semi-colon
            if i + 1 >= len(blocks) or \
                not is_token(blocks[i], "rcurly") or \
                not is_token(blocks[i+1], "semi"):
                return 1, block, "Illegal While Structure"

            commands.append(ParserNode("while", block, [while_cond, while_command]))
            
            i += 2
            
        elif is_token(block, "if"):
            # we're in an if statement
            # we expect:
            #  if [cond_exp] then {...} else {...} ;
            if i + 4 >= len(blocks) or \
                 not is_expression(blocks[i + 1]) or \
                 not is_token(blocks[i+2], "then") or \
                 not is_token(blocks[i+3], "lcurly"):
                return 1, block, "Illegal If Structure"
            
            if_cond = blocks[i + 1]

            # parse the 'then' command
            succ, i, then_command = parse_command(i + 4, blocks)
            if succ:
                return succ, i, then_command
            
            # next we expect rcurly, else, lcurly
            if i + 3 >= len(blocks) or \
                 not is_token(blocks[i], "rcurly") or \
                 not is_token(blocks[i+1], "else") or \
                 not is_token(blocks[i+2], "lcurly"):
                return 1, block, "Illegal If Structure"
            
            # parse the 'else' command
            succ, i, else_command = parse_command(i + 3, blocks)
            if succ:
                return succ, i, else_command

            # assert it ends with an rcurly, semi-colon
            if i + 1 >= len(blocks) or \
                not is_token(blocks[i], "rcurly") or \
                not is_token(blocks[i+1], "semi"):
                return 1, block, "Illegal If Structure"

            commands.append(ParserNode("if", block, [if_cond, then_command, else_command]))
            
            i += 2

        elif is_token(block, "skip"):
            # we're in a skip command
            # we expect:
            #  skip ; 
            if i + 1 >= len(blocks) or \
                 not is_token(blocks[i+1], "semi"):
                return 1, block, "Illegal Skip Structure"
            
            commands.append(ParserNode("skip", block, []))
            
            i += 2

        elif is_token(block, "assert"):
            # we're in a assert command
            # we expect:
            #  assert [cond_exp] ; 
            if i + 2 >= len(blocks) or \
                 not is_expression(blocks[i+1]) or \
                 not is_token(blocks[i+2], "semi"):
                return 1, block, "Illegal Assert Structure"
            
            commands.append(ParserNode("assert", block, [blocks[i+1]]))
            
            i += 3

        elif is_token(block, "inv"):
            # we're in an inv command
            # we expect:
            #  inv [cond_exp] ; 
            if i + 2 >= len(blocks) or \
                 not is_expression(blocks[i+1]) or \
                 not is_token(blocks[i+2], "semi"):
                return 1, block, "Illegal Inv Structure"
            
            commands.append(ParserNode("inv", block, [blocks[i+1]]))
            
            i += 3

        elif i + 1 < len(blocks) and is_token(blocks[i+1], "assign"):
            # we're in an assign command
            # we expect:
            # [assignable_expression] := [exp] ; 
            if i + 3 >= len(blocks) or \
                 not is_expression(block) or \
                 not block.value.name == "var" or \
                 not is_expression(blocks[i+2]) or \
                 not is_token(blocks[i+3], "semi"):
                return 1, block, "Illegal Assign Structure"
            
            commands.append(
                ParserNode("assign", blocks[i+1], [block, blocks[i + 2]])
            )
            
            i += 4
        
        elif type(block) == ParserNode:
            # we're in a single expression:
            # exp ;
            # just need to compute it
            if i + 1 >= len(blocks) or not is_expression(blocks[i + 1]):
                return 1, block, "Illegal expression"
            commands.append(block)

            i += 2

        elif is_token(block, "rcurly"):
            seq = ParserNode("seq", block, commands)
            return 0, i, seq
    
        else:
            return 1, block, "Illegal command"
        
    seq = ParserNode("seq", block, commands)
    return 0, i, seq


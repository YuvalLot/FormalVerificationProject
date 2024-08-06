
from Parser.parser_node import ParserNode
from Parser.Tokenizer.tokens import Token


def is_token(block, name: str):
    return type(block) == Token and block.name == name

def is_expression(block):
    return type(block) == ParserNode and block.is_expression


# TODO: function that checks if an expression is a valid signature
def valid_signature(block):
    return is_expression(block) and block.name == "apply"

def is_assignable(block):
    return is_expression(block) and (
        (block.name == "leaf" and block.value.name == "var"))
    """
        or (block.name == "comma" and 
            all(is_assignable(child) for child in block.children)
    """

def expression_len(block):
    if block.name == "comma":
        return len(block.children)
    else:
        return 1

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
            #  while [cond_exp] {...} ;
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

            # while_command should be of ParserNode type: seq
            # if the first element is an inv, pull it out and add it in the while
            if len(while_command.children) > 0 and \
                while_command.children[0].name == "inv":
                invariance = while_command.children.pop(0)
            else:
                invariance = None

            commands.append(ParserNode("while", block, [while_cond, invariance, while_command]))
            
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

        elif is_token(block, "print"):
            # print command
            # expect:
            #  print expression ;
            if i + 2 >= len(blocks) or \
                not is_expression(blocks[i + 1]) or \
                not is_token(blocks[i + 2], "semi"):
                return 1, block, "Illegal Print Structure"
            
            commands.append(ParserNode("print", block, [blocks[i+1]]))
            
            i += 3

        elif is_token(block, "return"):
            # return command
            # expect:
            #  return expression ;
            if i + 2 >= len(blocks) or \
                not is_expression(blocks[i + 1]) or \
                blocks[i+1].name == "comma" or \
                not is_token(blocks[i + 2], "semi"):
                return 1, block, "Illegal Return Structure"
            
            # TODO: we might want to add some parameter to this function 
            #       that checks if we are inside a function, so that we 
            #       can recognize return outside a function as a parsing error

            # TODO: For now, I've decided that function return a single value
            #       in the future, we might want to allow more flexibility, 
            #       and in general allow more things to be done with tuples (commas)
            #       Right now, tuples are only used for passing multiple arguments.
            
            commands.append(ParserNode("return", block, [blocks[i+1]]))
            
            i += 3

        elif is_token(block, "assume"):
            # we're in a assume command
            # we expect:
            #  assume [cond_exp] ; 
            if i + 2 >= len(blocks) or \
                 not is_expression(blocks[i+1]) or \
                 not is_token(blocks[i+2], "semi"):
                return 1, block, "Illegal Assume Structure"
            
            commands.append(ParserNode("assume", block, [blocks[i+1]]))
            
            i += 3

        elif i + 1 < len(blocks) and is_token(blocks[i+1], "assign"):
            # we're in an assign command
            # we expect:
            # [assignable_expression] := [exp] ; 
            
            if i + 3 >= len(blocks) or \
                 not is_assignable(block) or \
                 not is_expression(blocks[i+2]) or \
                 not is_token(blocks[i+3], "semi"):
                
                # TODO: specialize errors here, e.g. if it is an expression but not a 
                #       leaf of type val, then write that you can only assign variables
                return 1, block, "Illegal Assign Structure"

            commands.append(
                ParserNode("assign", blocks[i+1], [block, blocks[i + 2]])
            )
            
            i += 4
        
        elif type(block) == ParserNode:
            # we're in a single expression:
            # exp ;
            # just need to compute it
            if i + 1 >= len(blocks) or not is_token(blocks[i+1], "semi"):
                return 1, block, "Illegal expression"
            commands.append(block)

            i += 2

        elif is_token(block, "rcurly"):
            seq = ParserNode("seq", block, commands)
            return 0, i, seq
    
        elif is_token(block, "error"):
            # we're in an error command
            # we expect:
            #  error ; 
            if i + 1 >= len(blocks) or \
                 not is_token(blocks[i+1], "semi"):
                return 1, block, "Illegal Error Structure"
            
            commands.append(ParserNode("error", block, []))
            
            i += 2

        elif is_token(block, "def"):
            # we're in a function definition
            # we expect:
            #  def function_signature {...} ;
            if i + 3 >= len(blocks) or \
                 not valid_signature(blocks[i + 1]) or \
                 not is_token(blocks[i + 2], "lcurly"):
                
                error_msg = "Illegal Def Structure"
                if i + 3 >= len(blocks):
                    error_msg = "Not enough tokens after def"
                if not valid_signature(blocks[i + 1]):
                    error_msg = "def should be followed by a valid function signature"
                if not is_token(blocks[i+2], "lcurly"):
                    error_msg = "missing left curly after def"
                return 1, block, error_msg
            
            func_name = blocks[i + 1].children[0]
            func_params = blocks[i + 1].children[1]

            # parse the inner while command
            succ, i, func_command = parse_command(i + 3, blocks)
            if succ:
                return succ, i, func_command
            
            # assert it ends with an rcurly, semi-colon
            if i + 1 >= len(blocks) or \
                not is_token(blocks[i], "rcurly") or \
                not is_token(blocks[i+1], "semi"):
                return 1, block, "Illegal Def Structure"

            # func_command should be of ParserNode type: seq
            # if the first element is an assert, pull it out and add it in the def
            if len(func_command.children) > 0 and \
                func_command.children[0].name == "assert":
                func_assert = func_command.children.pop(0)
            else:
                func_assert = None

            commands.append(
                ParserNode("def", block, 
                           [func_name, func_params, func_assert, func_command])
                           )
            
            i += 2

        else:
            return 1, block, "Illegal command"
        
    seq = ParserNode("seq", block, commands)
    return 0, i, seq


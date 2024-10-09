
from Parser.parser_node import ParserNode
from Parser.Tokenizer.tokens import Token


def is_token(block, name: str):
    return type(block) == Token and block.name == name

def is_expression(block):
    if type(block) != ParserNode or not block.is_expression:
        return False

    return True


# can appear after a forall
def is_quantafiable(block):
    return (block.name == "leaf" and block.value.name == "var") or \
        (block.name == "comma" and 
            all(child.name == "leaf" and child.value.name == "var" 
                for child in block.children))


# function that checks if an expression is a valid signature of a funciton
def valid_signature(block):
    if not is_expression(block) or block.name != "apply" or \
        len(block.children) != 2:
        return False

    func_name, func_par = block.children
    if func_name.name != "leaf" or func_name.value.name != "var":
        return False
    
    # valid parameters: no parameters, one single variable, 
    # or a comma, each one a single variable
    param_valid = (func_par == None) or \
        (func_par.name == "leaf" and func_par.value.name == "var") or \
        (func_par.name == "comma" and 
            all(child.name == "leaf" and child.value.name == "var" 
                for child in func_par.children) and 
            len(set(child.value.value for child in func_par.children)) == len(func_par.children))
    
    return param_valid


# function that checks if something can appear in left side if := operator
def is_assignable(block):
    return is_expression(block) and (
        (block.name == "leaf" and block.value.name == "var"))


# function that checks if something can appear in the right side of := operator
def can_be_assigned(block):
    return is_expression(block) and block.name != "comma"


def expression_len(block):
    if block.name == "comma":
        return len(block.children)
    else:
        return 1

# gets a list of blocks, and returns a list of blocks that parse
# the code in the current nested level (i.e., until the first unopened } or EOF)
# Success case: returns (0, next_position: int, Parsed Command)
# Failure case: returns (1, failed token or None, string describing error)
def parse_command(curr_pos: int, blocks: list, 
                  inside_function: int = 0):
    commands = []
    i = curr_pos
    block = None

    # after a return command, we only allow logical commands (assert, assume, inv)
    seen_return = False

    while i < len(blocks):
        block = blocks[i]
        
        if is_token(block, "while"):
            if seen_return:
                return 1, block, "Illegal command after return"
            
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
            succ, i, while_command = parse_command(i + 3, blocks, 
                                                   inside_function)
            if succ:
                return succ, i, while_command
            
            # assert it ends with an rcurly, semi-colon
            if i + 1 >= len(blocks) or \
                not is_token(blocks[i], "rcurly") or \
                not is_token(blocks[i+1], "semi"):
                return 1, block, "Expected end of block and semi-colon after while"

            # while_command should be of ParserNode type: seq
            # if the first element is an inv, pull it out and add it in the while
            if len(while_command.children) > 0 and \
                while_command.children[0].name == "inv":
                invariance = while_command.children.pop(0)
            else:
                invariance = None

            commands.append(ParserNode("while", block, [while_cond, invariance, while_command]))
            
            if while_command.contains_return:
                return 1, while_cond.contains_return, "return should only appear once at the end of function"

            i += 2
            
        elif is_token(block, "if"):
            if seen_return:
                return 1, block, "Illegal command after return"
            
            # we're in an if statement
            # we expect:
            #  if [cond_exp] then {...} else {...} ;
            if i + 1 >= len(blocks) or not is_expression(blocks[i + 1]):
                return 1, block, "Expected condition after if (in if command)"
            
            if i + 2 >= len(blocks) or not is_token(blocks[i+2], "then"):
                return 1, block, "Expected 'then' after condition (in if command)"

            if i + 3 >= len(blocks) or not is_token(blocks[i+3], "lcurly"):
                return 1, block, "Expected '{' after then (in if command)"
            
            if_cond = blocks[i + 1]

            # parse the 'then' command
            succ, i, then_command = parse_command(i + 4, blocks, 
                                                  inside_function)
            if succ:
                return succ, i, then_command
            
            if i >= len(blocks) or not is_token(blocks[i], "rcurly"):
                return 1, block, "Expected '}' after then block (in if command)"
            
            if i + 1 >= len(blocks) or not is_token(blocks[i+1], "else"):
                return 1, block, "Expected 'else' clause (in if command)"

            if i + 2 >= len(blocks) or not is_token(blocks[i+2], "lcurly"):
                return 1, block, "Expected '{' after else (in if command)"
            
            # parse the 'else' command
            succ, i, else_command = parse_command(i + 3, blocks, 
                                                  inside_function)
            if succ:
                return succ, i, else_command

            # assert it ends with an rcurly, semi-colon
            if i + 1 >= len(blocks) or \
                not is_token(blocks[i], "rcurly") or \
                not is_token(blocks[i+1], "semi"):
                return 1, block, "Expected '};' at the end of if"

            commands.append(ParserNode("if", block, [if_cond, then_command, else_command]))
            
            if bool(then_command.contains_return) != bool(else_command.contains_return):
                return (1, then_command.contains_return or else_command.contains_return, 
                        "Return should appear in both then and else clauses, or in neither one")

            i += 2

        elif is_token(block, "skip"):
            if seen_return:
                return 1, block, "Illegal command after return"
                
            # we're in a skip command
            # we expect:
            #  skip ; 
            if i + 1 >= len(blocks) or \
                 not is_token(blocks[i+1], "semi"):
                return 1, block, "Expected ';' after skip"
            
            commands.append(ParserNode("skip", block, []))
            
            i += 2

        elif is_token(block, "assert"):
            # we're in a assert command
            # we expect:
            #  assert [cond_exp] ; 
            if i + 1 >= len(blocks) or \
                 not is_expression(blocks[i+1]):
                return 1, block, "Expected condition after assert" 
            if i + 2 >= len(blocks) or \
                 not is_token(blocks[i+2], "semi"):
                return 1, block, "Expected ';' at the end of assert command"
            
            commands.append(ParserNode("assert", block, [blocks[i+1]]))
            
            i += 3

        elif is_token(block, "inv"):
            # we're in an inv command
            # we expect:
            #  inv [cond_exp] ; 
            if i + 1 >= len(blocks) or \
                 not is_expression(blocks[i+1]):
                return 1, block, "Expected condition after inv" 
            if i + 2 >= len(blocks) or \
                 not is_token(blocks[i+2], "semi"):
                return 1, block, "Expected ';' at the end of inv command"
            
            commands.append(ParserNode("inv", block, [blocks[i+1]]))
            
            i += 3

        elif is_token(block, "print"):
            if seen_return:
                return 1, block, "Illegal command after return"
            
            # print command
            # expect:
            #  print expression ;
            if i + 1 >= len(blocks) or \
                 not is_expression(blocks[i+1]):
                return 1, block, "Expected expression after print" 
            if i + 2 >= len(blocks) or \
                 not is_token(blocks[i+2], "semi"):
                return 1, block, "Expected ';' at the end of print command"
            
            commands.append(ParserNode("print", block, [blocks[i+1]]))
            
            i += 3

        elif is_token(block, "return"):
            if seen_return:
                return 1, block, "Illegal command after return"
            
            # return command
            # expect:
            #  return expression ;
            if i + 1 >= len(blocks) or \
                not is_expression(blocks[i + 1]) or \
                blocks[i+1].name == "comma":
                return 1, block, "Illegal Return (should return a single value)"
            
            if i + 2 >= len(blocks) or not is_token(blocks[i + 2], "semi"):
                return 1, block, "Expected ';' after return"
            
            if inside_function == 0:
                return 1, block, "Return outside of a function is not allowed"
            
            commands.append(ParserNode("return", block, [blocks[i+1]]))
            
            i += 3
            seen_return = True

        elif is_token(block, "assume"):
            # we're in a assume command
            # we expect:
            #  assume [cond_exp] ; 
            if i + 1 >= len(blocks) or \
                 not is_expression(blocks[i+1]):
                return 1, block, "Expected condition after assume" 
            if i + 2 >= len(blocks) or \
                 not is_token(blocks[i+2], "semi"):
                return 1, block, "Expected ';' at the end of assume command"
            
            commands.append(ParserNode("assume", block, [blocks[i+1]]))
            
            i += 3

        elif i + 1 < len(blocks) and is_token(blocks[i+1], "assign"):
            if seen_return:
                return 1, block, "Illegal command after return"
            
            # we're in an assign command
            # we expect:
            # [assignable_expression] := [exp] ; 
            
            if i + 3 >= len(blocks) or \
                 not is_assignable(block) or \
                 not can_be_assigned(blocks[i+2]) or \
                 not is_token(blocks[i+3], "semi"):
                
                if not is_assignable(block):
                    return 1, block, f"{block} is not assignable"
                
                if i + 2 >= len(blocks):
                    return 1, blocks[i+1], f"Expected value after ':='"
                
                if not can_be_assigned(blocks[i+2]):
                    return 1, blocks[i+2], f"E{blocks[i+2]} cannot be assigned to a variable"

                return 1, block, "Expected ';' at the end of assignment"

            commands.append(
                ParserNode("assign", blocks[i+1], [block, blocks[i + 2]])
            )
            
            i += 4
        
        elif type(block) == ParserNode:
            if seen_return:
                return 1, block, "Illegal command after return"
            
            # we're in a single expression:
            # exp ;
            # just need to compute it
            if i + 1 >= len(blocks) or not is_token(blocks[i+1], "semi"):
                return 1, block, "Expected ';' after expression"
            commands.append(block)

            i += 2

        elif is_token(block, "rcurly"):
            seq = ParserNode("seq", block, commands)
            return 0, i, seq

        elif is_token(block, "error"):
            if seen_return:
                return 1, block, "Illegal command after return"
            # we're in an error command
            # we expect:
            #  error ; 
            if i + 1 >= len(blocks) or \
                 not is_token(blocks[i+1], "semi"):
                return 1, block, "Expected ';' after error"
            
            commands.append(ParserNode("error", block, []))
            
            i += 2

        elif is_token(block, "def"):
            if seen_return:
                return 1, block, "Illegal command after return"
            # we're in a function definition
            # we expect:
            #  def function_signature {...} ;
            if i + 3 >= len(blocks) or \
                 not valid_signature(blocks[i + 1]) or \
                 not is_token(blocks[i + 2], "lcurly"):
                
                error_msg = "Illegal Def Structure"
                
                if i + 1 >= len(blocks) or not valid_signature(blocks[i + 1]):
                    error_msg = "def should be followed by a valid function signature"
                
                if i + 2 >= len(blocks) or not is_token(blocks[i+2], "lcurly"):
                    error_msg = "missing '{' after def"

                return 1, block, error_msg
            
            func_name = blocks[i + 1].children[0]
            func_params = blocks[i + 1].children[1]

            # parse the inner while command
            succ, i, func_command = parse_command(i + 3, blocks, 
                                                  inside_function + 1)
            if succ:
                return succ, i, func_command
            
            # assert it ends with an rcurly, semi-colon
            if i + 1 >= len(blocks) or \
                not is_token(blocks[i], "rcurly") or \
                not is_token(blocks[i+1], "semi"):
                return 1, block, "Missing '};' after def"

            # func_command should be of ParserNode type: seq
            # if the first element is an assume, and/or the last is an assert
            # pull it out and add it in the def

            if len(func_command.children) > 0 and \
                func_command.children[0].name == "assume":
                func_assumes = func_command.children.pop(0)
            else:
                func_assumes = None

            if len(func_command.children) > 0 and \
                func_command.children[-1].name == "assert":
                func_asserts = func_command.children.pop(-1)
            else:
                func_asserts = None


            # structure of function:
            # (func_name, func_params, func_assumes, func_command, func_asserts)
            commands.append(
                ParserNode("def", block, 
                           [func_name, func_params, func_assumes, func_command, func_asserts])
                           )
            
            i += 2
        
        elif is_token(block, "forall"):
            # we're in a forall command
            # we expect:
            # forall [variable] :: [assertion] ;
            if i + 4 >= len(blocks) or \
                not is_quantafiable(blocks[i + 1]) or \
                not is_token(blocks[i+2], "::") or \
                not is_expression(blocks[i+3]) or \
                not is_token(blocks[i+4], "semi"):
                return 1, block, "Illegal Forall Structure"
            variable = blocks[i+1]  # The variable(s) (e.g., x or y)
            assertion = blocks[i+3]  # The assertion using the variable

            if not assertion.free_variables.issubset(variable.free_variables):
                return 1, block, "Forall assertion should only contain quantified variables!"

            # Create the 'forall' ParserNode with the variable and assertion as children
            commands.append(ParserNode("forall", block, [variable, assertion]))

            i += 5  # Move past the forall structure

        else:
            return 1, block, "Illegal command"
        
    
    seq = ParserNode("seq", block, commands)

    return 0, i, seq


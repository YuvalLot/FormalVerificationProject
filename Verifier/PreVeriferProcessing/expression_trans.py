
from collections import defaultdict
from Parser.parser_node import ParserNode
from Parser.Tokenizer.tokens import Token


INT_VARIABLE_COUNT = 0

# for success, return a triplet of items:
# (
#       list of logical commands, assertions and assumptions
# ) 

# for failure, (error_msg, None)

def expression_trans(expression: ParserNode, functions: dict[str, (ParserNode)], 
                     flags):

    global INT_VARIABLE_COUNT

    if not expression.is_expression:
        print(expression)
        raise Exception("EXCEPTION: EXPRESSION IS NOT EXPRESSION, SHOULD NOT HAPPEND!")
    

    if expression.name == "leaf":
        return []
        

    elif expression.name[:2] == "op":

        operands = expression.children
        logics = []
        for operand in operands:
            logic = expression_trans(operand, functions, flags)
            logics += logic
    
        return logics


    elif expression.name == "apply":

        func_name, func_param = expression.children

        if func_param is None:
            func_param = []
        elif func_param.name == "comma":
            func_param = [child for child in func_param.children]
        else:
            func_param = [func_param]
        
        logics = []
        
        for operand in func_param:
            logic = expression_trans(operand, functions, flags)
            logics += logic

        if func_name.value.value in functions:
            func_definition = functions[func_name.value.value]
            org_func_name, func_param_signature, func_pre, func_code, func_post = func_definition.children
            
            if func_param_signature is None:
                func_param_signature = []
            elif func_param_signature.name == "comma":
                func_param_signature = [child for child in func_param_signature.children]
            else:
                func_param_signature = [func_param_signature] 

            # func_param_signature should be a list of variable names
            # need to match the new_params

            # assert func_pre[new_params / func_param_signature]
            # assume func_post(new_params, expression);

            dictionary = {
                param_name.value.value : param_value 
                for (param_name, param_value) in zip(func_param_signature, func_param)
            }

            if func_pre is not None:
                pre_condition = func_pre.children[0].substitute(dictionary)
                pre_logic = expression_trans(pre_condition, functions, 
                                                             flags)
                logics += pre_logic
                logics.append(
                    ParserNode("assert", func_name.value, [pre_condition])
                )
                logics[-1].verification_desc = f"pre-cond of {expression.to_while_str()} in line {expression.value.lineno}"
            
            if func_post is not None:
                int_variable = f"@{INT_VARIABLE_COUNT}"
                INT_VARIABLE_COUNT += 1

                dictionary["RET"] = ParserNode("leaf", 
                                               Token("var", int_variable, 0, 0)
                                               , [], is_expression=True)
                
                post_condition = func_post.children[0].substitute(dictionary)
                post_logic = expression_trans(post_condition, 
                                              functions, flags)
                logics += [pl.substitute({int_variable: expression}) for pl in post_logic]
                logics.append(ParserNode("assume", func_name.value, [post_condition.substitute({int_variable: expression})]))
                

            return logics

        else:
            # logical function
            return logics

    else:
        raise ValueError(f'TRANSLATE does not support {expression.name}')




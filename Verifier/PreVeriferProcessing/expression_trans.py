
from Parser.parser_node import ParserNode
from Parser.Tokenizer.tokens import Token

INT_VARIABLE_COUNT = 0
INT_VARIABLE_CORRESPONDENCE = {}

# for success, return a triplet of items:
# (
#       list of logical commands, assertions and assumptions
#       new expression [not None]
# ) 

# for failure, (error_msg, None)

def expression_trans(expression: ParserNode, functions: dict[str, ParserNode]):
    
    global INT_VARIABLE_COUNT

    if not expression.is_expression:
        raise Exception("EXCEPTION: EXPRESSION IS NOT EXPRESSION, SHOULD NOT HAPPEND!")
    

    if expression.name == "leaf":
        return ([], expression)
        

    elif expression.name[:2] == "op":

        operands = expression.children
        logics = []
        new_children = []
        for operand in operands:
            (logic, new_exp) = expression_trans(operand, functions)
            if new_exp is None:
                return (logic, new_exp)
            logics += logic
            new_children.append(new_exp)
    
        return (logics, ParserNode(expression.name, expression.value, new_children, 
                                   is_expression = True))


    elif expression.name == "apply":
        func_name, func_param = expression.children

        if func_param is None:
            func_param = []
        elif func_param.name == "comma":
            func_param = [child for child in func_param.children]
        else:
            func_param = [func_param]
        
        logics = []
        new_params = []
        for operand in func_param:
            (logic, new_exp) = expression_trans(operand, functions)
            if new_exp is None:
                return (logic, new_exp)
            logics += logic
            new_params.append(new_exp)

        new_params_parser_node = None
        if len(new_params) == 1:
            new_params_parser_node = new_params[0]
        elif len(new_params) > 1:
            new_params_parser_node = ParserNode("comma", expression.children[1].value, new_params, is_expression = expression.children[1].is_expression)
        

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
            # assume func_post(temp_variable) && temp_variable = func_name(new_params)

            dictionary = {
                param_name.value.value : param_value 
                for (param_name, param_value) in zip(func_param_signature, new_params)
            }

            dictionary["RET"] = ParserNode("leaf", Token("var", f"@{INT_VARIABLE_COUNT}",
                                                         expression.value.lineno, 
                                                         expression.value.charno), [], 
                                                         is_expression = True)
            INT_VARIABLE_CORRESPONDENCE[f"@{INT_VARIABLE_COUNT}"] = expression
            INT_VARIABLE_COUNT += 1

            if func_pre is not None:
                pre_condition = func_pre.children[0].substitute(dictionary)
                (pre_logic, new_pre_cond) = expression_trans(pre_condition, functions)
                if new_pre_cond is None:
                    return (pre_logic, new_pre_cond)
                logics += pre_logic
                logics.append(
                    ParserNode("assert", func_name.value, [new_pre_cond])
                )
            
            if func_post is not None:
                post_condition = func_post.children[0].substitute(dictionary)
                (post_logic, new_post_cond) = expression_trans(post_condition, functions)
                if new_post_cond is None:
                    return (post_logic, new_post_cond)
                logics += post_logic
                logics.append(
                    ParserNode("assume", func_name.value, [
                        ParserNode("op&&", 
                                   func_name.value, [new_post_cond, 
                                                     ParserNode("op=", func_name.value, 
                                                                [ParserNode("apply", expression.value, [func_name, new_params_parser_node], is_expression = True), dictionary["RET"]], is_expression = True)],
                                    is_expression = True)
                        ])
                )


            return (logics, dictionary["RET"])

        else:
            # logical function
            return (logics, 
                    ParserNode(expression.name, 
                               expression.value, 
                               [func_name, new_params_parser_node], 
                               is_expression = True))



    else:
        raise ValueError(f'TRANSLATE does not support {expression.name}')




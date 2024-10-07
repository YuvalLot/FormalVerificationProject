
from Parser.parser_node import ParserNode
from Verifier.PreVeriferProcessing.expression_trans import expression_trans

"""
PREPROCESSOR:

return a list of commands
"""
# TODO: Fancier infinite recursion check
def preprocess(code: ParserNode, functions = None, flags = None):

    functions = functions or {}

    if code.name == "seq":
        commands = code.children
        new_commands = []
        for command in commands:
            if command.name == "def":
                functions[command.children[0].value.value] = command

        for command in commands:
            new_commands += preprocess(command, functions.copy(), flags)

        return new_commands


    elif code.is_expression:
        logics, exp = expression_trans(code, functions, flags)
        return logics + [exp]
    
    elif code.name == "assign":
        variable = code.children[0]
        expression = code.children[1]
        (logics, new_exp) = expression_trans(expression, functions, flags)
        return logics + [ParserNode("assign", code.value, [variable, new_exp])]
    
    elif code.name in ["skip", "print"]:
        return [code]
    
    elif code.name == "if":

        if_cond, then_code, else_code = code.children

        (logics_cond, new_cond) = expression_trans(if_cond, functions, flags)
        new_then_codes = preprocess(then_code, functions.copy(), flags)
        new_else_codes = preprocess(else_code, functions.copy(), flags)

        return logics_cond + [
            ParserNode("if", code.value, 
                       [new_cond, 
                        ParserNode("seq", then_code.value, new_then_codes), 
                        ParserNode("seq", else_code.value, new_else_codes)])
        ]
        
    elif code.name in ["assert", "assume", "return"]:
        expression = code.children[0]
        (logics, new_exp) = expression_trans(expression, functions, flags)
        return logics + [ParserNode(code.name, code.value, [new_exp])]


    elif code.name == "while":
        while_cond, while_inv, while_body = code.children
        
        while_cond_logics, while_cond_new = expression_trans(while_cond, functions, flags)
        if while_inv is not None:
            while_inv_logics, while_inv_new = expression_trans(while_inv.children[0], functions, flags)
        else:
            while_inv_logics = []
            while_inv_new = None
        while_body_new = preprocess(while_body, functions.copy(), flags)

        return while_cond_logics + while_inv_logics + [
            ParserNode("while", code.value, [
                while_cond_new, 
                ParserNode("inv", while_inv.value, [while_inv_new]) 
                if while_inv is not None else None,
                ParserNode("seq", while_body.value, while_body_new + 
                                                    while_cond_logics + 
                                                    while_inv_logics)
            ])
        ] + while_cond_logics + while_inv_logics

    elif code.name == "error":
        return [code]

    elif code.name == "def": 
        """
        To verify a function definition, we add side effect(s) that verify the function's
        pre-condition implies the wlp of the function's post-condition
        """
        func_name, func_params, func_pre, func_code, func_post = code.children

        new_codes = []
        if func_pre is not None:
            new_codes += preprocess(func_pre, functions.copy(), flags)
        new_codes += preprocess(func_code, functions.copy(), flags)
        if func_post is not None:
            new_codes += preprocess(func_post, functions.copy(), flags)

        return [ParserNode("def", code.value, [
            func_name, func_params, None, 
            ParserNode("seq", func_code.value, new_codes), 
            None
        ])]

    elif code.name == "forall":
        return [code]

    else:
        raise ValueError(f"Error: command {code.name} not yet supported.")
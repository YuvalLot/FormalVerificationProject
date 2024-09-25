
from Parser.parser_node import ParserNode

INT_VARIABLE_COUNT = 0

# for success, return a triplet of items:
# (
#       assertion (to verify that function pre-condition is satisfied), 
#       assumption (guaranteed by function's post-condition), 
#       new expression
# ) 

# for failure, (line_number, error_msg)

def expression_trans(expression: ParserNode, functions: dict[str, ParserNode], ):
    
    if not expression.is_expression:
        raise Exception("EXCEPTION: EXPRESSION IS NOT EXPRESSION, SHOULD NOT HAPPEND!")
    
    if self.name == "leaf":
            if self.value.name == "int":
                return z3.IntVal(self.value.value)
            elif self.value.name == "var":
                return z3.Int(self.value.value)
            else:
                raise ValueError(f"Unknown leaf type: {self.value.name}.")
            
        elif self.name[:2] == "op":

            if len(self.children) == 1:
                if self.name in prefix_to_function:
                    return prefix_to_function[self.name](self.children[0].to_z3_inner())
                raise ValueError("Exception: Not supported")
            if len(self.children) == 2:
                if self.name in infix_to_function:
                    return infix_to_function[self.name](
                        self.children[0].to_z3_inner(),
                        self.children[1].to_z3_inner(),
                    )
                raise ValueError("Exception: Not supported")

        elif self.name == "apply":
            func_name, func_param = self.children
            if func_param is None:
                func_param = []
            elif func_param.name == "comma":
                func_param = [child.to_z3_inner() for child in func_param.children]
            else:
                func_param = [func_param.to_z3_inner()]
            
            num_params = len(func_param)
            infered_func_sig = [z3.IntSort()] * (num_params + 1)
            func_symbol = z3.Function(func_name.value.value, *infered_func_sig)

            return func_symbol(*func_param)

        else:
            raise ValueError(f'ParserNode.to_z3_inner does not support {self.name}')




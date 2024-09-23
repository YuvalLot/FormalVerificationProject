
from Parser.Tokenizer.tokens import Token
import z3


infix_to_function = {
    "op+": lambda x, y: x + y,
    "op-": lambda x, y: x - y,
    "op*": lambda x, y: x * y,
    "op/": lambda x, y: x / y,
    "op>": lambda x, y: x>y,
    "op<": lambda x, y : x<y,
    "op<=": lambda x, y: x<=y,
    "op>=": lambda x, y: x>=y,
    "op=": lambda x, y: x==y,
    "op!=": lambda x, y: x != y,
    "op&&": lambda x, y: z3.And(x,y),
    "op||": lambda x, y: z3.Or(x,y),
    "op->": lambda x, y: z3.Implies(x, y)
}

prefix_to_function = {
    "op+": lambda x: x,
    "op-": lambda x: - x,
    "op!": lambda x: z3.Not(x) if z3.is_bool(x) else z3.Not(x != 0),
}


class ParserNode:

    def __init__(self, name: str, value: Token, children,
                  is_expression = False) -> None:
        self.name = name 
        self.value = value
        self.children = children
        self.is_expression = is_expression

        self.is_loop_free = True
        if self.name == "while":
            self.is_loop_free = False
        if any(child and not child.is_loop_free for child in children):
            self.is_loop_free = False

        self.function_calls = []
        if self.name == "apply":
            self.function_calls.append(self.children[0])
        
        for child in self.children:
            self.function_calls.append(child.function_calls)

    def __str__(self) -> str:
        if self.name == "leaf":
            return self.value.value
        elif len(self.children) == 0:
            return f"({self.name})"
        else:
            return f"({self.name}  " + \
                   "  ".join(map(str, self.children)) + ")"
    
    def __repr__(self) -> str:
        return str(self)

    def to_python(self, tabs=0, tab_char="\t") -> str:
        raw_string = ""
        if self.name == "leaf":
            return tabs*tab_char + self.value.value
        elif self.name[:2] == "op":
            op = self.name[-1]
            if op == "=":
                op = "=="
            if len(self.children) == 1:
                raw_string = tabs*tab_char + f"({op} {self.children[0].to_python(tab_char=tab_char)})"
            else:
                raw_string = tabs*tab_char + f"({self.children[0].to_python(tab_char=tab_char)} {op} {self.children[1].to_python(tab_char=tab_char)})"
        elif self.name == "while":
            cond = self.children[0].to_python(tab_char=tab_char)
            code = self.children[1].to_python(tabs + 1, tab_char=tab_char)
            return tabs * tab_char + f"while {cond}:\n" + code
        elif self.name == "if":
            cond = self.children[0].to_python(tab_char=tab_char)
            then_clasue = self.children[1].to_python(tabs + 1, tab_char=tab_char)
            else_clause = self.children[2].to_python(tabs + 1, tab_char=tab_char)
            return (tabs * tab_char) + f"if ({cond}):\n" + then_clasue + \
                (tabs * tab_char) + f"else:\n" + else_clause
        elif self.name == "skip":
            return (tabs * tab_char) + "pass"
        elif self.name in ["assert", "inv"]:
            cond = self.children[0].to_python(tab_char=tab_char)
            return (tabs * tab_char) + f"{self.name} {cond}\n"
        elif self.name == "assign":
            variable = self.children[0].to_python(tab_char=tab_char)
            expression = self.children[1].to_python(tab_char=tab_char)
            return (tabs * tab_char) + f"{variable} = {expression}\n"
        elif self.name == "seq":
            raw_string = "".join(child.to_python(tabs, tab_char=tab_char) for child in self.children)
        else:
            return "unknown"
        return raw_string

    def substitute(self, dictionary):
        # dictionary: dict with {variable_name (str) : ParserNode}
                
        if self.name == "leaf":
            if self.value.name == "var" and self.value.value in dictionary:
                # possible problem: we "forget" info about the token
                return dictionary[self.value.value]
            else:
                return self
            
        if self.name[:2] == "op":
            return ParserNode(
                self.name, self.value, 
                [child.substitute(dictionary) for child in self.children],
                is_expression=self.is_expression
            )
        
        raise Exception("Not suppoerted (yet...)")

    def to_z3_inner(self):
        if not self.is_expression:
            raise ValueError("should not happen")
        
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

    def to_z3_bool(self):
        expression = self.to_z3_inner()
        if not z3.is_bool(expression):
            return expression != 0
        return expression
    
    def to_z3_int(self):
        expression = self.to_z3_inner()
        if not z3.is_int(expression):
            return expression + 0
        return expression
    
    def to_while_str(self):
        raw_string = ""

        if self.name == "leaf":
            return self.value.value
        
        elif self.name[:2] == "op":
            op = self.name[-1]

            if len(self.children) == 1:
                raw_string = f"({op} {self.children[0].to_while_str()})"
            else:
                raw_string = f"({self.children[0].to_while_str()} {op} {self.children[1].to_while_str()})"
        
        elif self.name == "apply":
            func_name, func_param  = self.children
            func_name = func_name.to_while_str()
            if func_param is None:
                func_param = []
            elif func_param.name == "comma":
                func_param = [child.to_while_str() for child in func_param.children]
            else:
                func_param = [func_param.to_while_str()]
            
            return f"{func_name} (" + ",".join(func_param) + ")"

        elif self.name == "while":
            cond = self.children[0].to_while_str()
            code = self.children[1].to_while_str()
            return f"while {cond}" + "{ " + code + " };"
        
        elif self.name == "if":
            cond = self.children[0].to_while_str()
            then_clasue = self.children[1].to_while_str()
            else_clause = self.children[2].to_while_str()
            return f"if ({cond})" + "{" + then_clasue + "}" + \
                f"else\n" + "{" + else_clause + "}"
        
        elif self.name == "skip":
            return "skip;"
        
        elif self.name in ["assert", "inv"]:
            cond = self.children[0].to_while_str()
            return + f"{self.name} {cond};"
        
        elif self.name == "assign":
            variable = self.children[0].to_while_str()
            expression = self.children[1].to_while_str()
            return  f"{variable} := {expression};"
        
        elif self.name == "seq":
            raw_string = "\n".join(child.to_while_str() for child in self.children)
        
        else:
            return "unknown"
        
        return raw_string


POSSIBLE_NODE_NAMES = [
    "op+", "op-", "op*", "op/", "op&&", "op||", "op~", "leaf", "apply",      # expression types
    "while", "if", "skip", "assign", "assert", "inv", "seq",  # command types
    "print", "assume", "error", "def", "return",
]



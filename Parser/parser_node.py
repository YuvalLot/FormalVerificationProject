
from Parser.Tokenizer.tokens import Token


class ParserNode:

    def __init__(self, name: str, value: Token, children,
                  is_expression = False) -> None:
        self.name = name 
        self.value = value
        self.children = children
        self.is_expression = is_expression

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

POSSIBLE_NODE_NAMES = [
    "op+", "op-", "op*", "op/", "leaf",                      # expression types
    "while", "if", "skip", "assign", "assert", "inv", "seq"  # command types
]




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
        else:
            return f"({self.value.value}  " + \
                   "  ".join(map(str, self.children)) + ")"
    
    def __repr__(self) -> str:
        return str(self)
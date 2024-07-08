
from Tokenizer.tokens import Token


class ParserNode:

    def __init__(self, name: str, value: Token, children) -> None:
        self.name = name, 
        self.value = value
        self.children = children
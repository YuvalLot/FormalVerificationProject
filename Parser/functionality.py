
from Tokenizer.tokens import Token
from Parser.parser_node import ParserNode

class Functionality:

    def __init__(self, name):
        self.name == name

    """
    Called after removing the functional from the functional stack, and now calling 
    collpase on the two stacks with the the functional.

    1 for error, 0 for success.
    """
    def collapse(self, functional_token: Token, 
                 functionals: list[Token], nodes: list[ParserNode]):
        return 1



class InfixOperator (Functionality):
    
    def collapse(self, functional_token: Token, 
                 functionals: list[Token], nodes: list[ParserNode]):
        
        assert functional_token.name == self.name

        if len(nodes) < 2:
            return 1
        
        first, second = nodes.pop(), nodes.pop()
        nodes.append(
            ParserNode(self.name, functional_token, [first, second])
        )


functional_token_list = []
functional_map = { functional.name : functional 
                  for functional in functional_token_list }

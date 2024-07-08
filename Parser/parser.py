
from Parser.functionality import functional_token_list, functional_map
from Parser.parser_node import ParserNode
from Tokenizer.tokens import Token


def parse(token_list: list[Token]):
    
    node_stack = []
    functional_stack = []  # list of pairs (token, functionality)

    for token in token_list:
        if token.name not in functional_map:
            node_stack.append(
                ParserNode("leaf", token, [])
            )
        else:
            # try to push in functionals, if perserves precedence
            # else, collapse top element
            functionality = functional_map[token.name]
            if len(functional_stack) == 0:
                pass


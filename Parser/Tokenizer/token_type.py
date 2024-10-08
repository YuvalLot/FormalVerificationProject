
class TokenType:

    def __init__(self, name, pattern):
        self.pattern = pattern
        self.name = name



reserved_words = ["print", "assert", "while", 
                  "if", "then", "else", "inv", 
                  "skip", "assume", "error", 
                  "def", "return","forall","::"]


valid_token_types = [TokenType(word, word) for word in reserved_words] + [
    
    TokenType("_comment", r'/\*(.||\n)*?\*/'),

    TokenType("int", r"[0-9]+"),
    TokenType("op+", r"\+"),
    TokenType("op->", r'\-\>'),
    TokenType("op<->", r'\<\-\>'),
    TokenType("op-", r"\-"),
    TokenType("op*", r"\*"),
    TokenType("op/", r"\/"),
    TokenType("op%", r"\%"),
    TokenType("comma", r'\,'),

    
    TokenType("op>=", r"\>\="),
    TokenType("op<=", r"\<\="),
    TokenType("op>", r"\>"),
    TokenType("op<", r"\<"),
    TokenType("op=", r"\="),
    TokenType("op!=", r"\!\="),

    TokenType("op&&", r'\&\&'),
    TokenType("op||", r'\|\|'),
    TokenType("op!", r"\!"),

    TokenType("assign", r"\:\="),
    TokenType("lparen", r"\("),
    TokenType("rparen", r"\)"),
    TokenType("lcurly", r"\{"),
    TokenType("rcurly", r"\}"),
    
    TokenType("_ignore", r"[ \n\t]+"),
    TokenType("_comment", r'\#.*'),
    
    TokenType("var", r"[a-zA-Z_][a-zA-Z0-9_]*"),
    TokenType("semi", r';'),

]

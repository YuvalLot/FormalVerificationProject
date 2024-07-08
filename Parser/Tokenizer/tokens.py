import re
from Tokenizer.token_type import TokenType, valid_token_types

class Token:

    def __init__(self, name, value, lineno, charno):
        self.name = name
        self.value = value
        self.lineno = lineno
        self.charno = charno

    def __str__(self) -> str:
        return f"({self.name}, {self.value}, {self.lineno}, {self.charno})"

def tokenize(input_string):
    tokens = []
    lineno, charno = 1, 1
    error_str = ""
    found_token = False
    while input_string != "":
        found_token = False
        for token_type in valid_token_types:
            temp_match = re.match(token_type.pattern, input_string)
            if temp_match == None:
                continue
            token = Token(token_type.name, temp_match.group(), lineno, charno)
            new_lines_count = token.value.count("\n")
            lineno = lineno + new_lines_count

            if new_lines_count == 0:
                charno = charno + len(token.value)
            else:
                charno = len(token.value.split("\n")[-1])

            if (token.name[0] != "_"):
                tokens.append(token)

            input_string = input_string[len(token.value):]
            
            found_token = True
            break

        if not found_token:
            return [Token("error", "error", lineno, charno)], 1
    
    return tokens, 0


if __name__ == "__main__":
    filename = input("enter file name: ")

    with open(filename, "r") as file:
        tokens, success = tokenize(file.read())
        for tok in tokens:
            print(tok)







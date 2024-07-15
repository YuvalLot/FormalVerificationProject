
import Parser.Tokenizer.tokens as Tokens
import Parser.parser as Parser

with open("file1.while", "r") as file1:
    text = file1.read()


tokens, success = Tokens.tokenize(text)

if success:
    print(f"token error: {tokens}")

print(Parser.parse(tokens))


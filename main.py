
import Parser.Tokenizer.tokens as Tokens
import Parser.parser as Parser
from Interpereter.interperter import execute
from Interpereter.enviornment import Enviornment


with open("file1.while", "r") as file1:
    text = file1.read()


tokens, success = Tokens.tokenize(text)

if success:
    print(f"Token error: {tokens}")

failure, parsed = Parser.parse(tokens)

if failure:
    print("Parsing error:", parsed)


env = Enviornment()
failure, msg = execute(parsed, env)
if failure:
    print("Execution error:", msg)

# print(env.assignments)

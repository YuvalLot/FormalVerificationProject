
import Parser.Tokenizer.tokens as Tokens
import Parser.parser as Parser
from Interpereter.interperter import execute
from Interpereter.enviornment import Enviornment
import sys

from Verifier.verify import verify
from Verifier.PreVeriferProcessing.preprocessor import preprocess



file_name = "file1.while" if (len(sys.argv) == 1) else sys.argv[1]
with open(file_name, "r") as file:
    text = file.read()

tokens, success = Tokens.tokenize(text)
# print(tokens)

if success:
    print(f"Token error: {tokens}")
    exit()

failure, parsed = Parser.parse(tokens)

if failure:
    print("Parsing error:", parsed)
    exit()

"""
env = Enviornment()
failure, msg = execute(parsed, env)
if failure:
    print("Execution error:", msg)

print(env.assignments)
print(env.functions)
"""

verify(parsed)


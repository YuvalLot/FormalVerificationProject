
import Parser.Tokenizer.tokens as Tokens
import Parser.parser as Parser
from Interpereter.interperter import execute
from Interpereter.enviornment import Enviornment
import sys

from Verifier.verify import verify
from Verifier.PreVeriferProcessing.preprocessor import preprocess

from main_options import get_main_options


program_args = [arg for arg in sys.argv if not arg.startswith('-')]
file_name = "file1.while" if (len(program_args) == 1) else program_args[1]
with open(file_name, "r") as file:
    text = file.read()


flags = get_main_options()


tokens, success = Tokens.tokenize(text)
# print(tokens)

if success:
    print(f"Token error: {tokens}")
    exit()

failure, parsed = Parser.parse(tokens)

if failure:
    print("Parsing error:", parsed)
    exit()

if flags["run"]:

    env = Enviornment()
    failure, msg = execute(parsed, env)
    if failure:
        print("Execution error:", msg)

    # print(env.assignments)
    # print(env.functions)
    exit()


verify(parsed, flags)


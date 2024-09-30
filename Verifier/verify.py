
from Parser.parser import ParserNode
from Verifier.verifcation_condition import verification_condition
from Verifier.PreVeriferProcessing.preprocessor import preprocess
from Verifier.PreVeriferProcessing.expression_trans import INT_VARIABLE_CORRESPONDENCE

import z3


# returns object of type Verification
def verify(code: ParserNode):

    # preprocess

    try:
        code = ParserNode("seq", code.value, preprocess(code))
        print("...............",code)
    except RecursionError:
        print("There was a recursion error in translating the functions")
        return
    
    print(code.to_while_str())

    vc = verification_condition(z3.BoolVal(True), code, z3.BoolVal(True), -1)
    print(INT_VARIABLE_CORRESPONDENCE)
    
    for (condition, line_number) in vc:
        print(f"verifying {condition} in line number(s): "
              f"{', '.join(map(str, line_number))}")
        solver = z3.Solver()

        solver.add(z3.Not(condition))

        if solver.check() == z3.sat:
            print(f"Unable to verify condition in line {line_number}, e.g.: ")
            model = solver.model()
            for v in model:
                name = v.name()
                if name in INT_VARIABLE_CORRESPONDENCE:
                    name = INT_VARIABLE_CORRESPONDENCE[name].to_while_str()
                
                print(f"{name} = {model[v]}")
            return
    
    print("Verified!")
   

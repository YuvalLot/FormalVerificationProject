
from Parser.parser import ParserNode
from Verifier.verification_condition import verification_condition, UNDEFINED_VAR_TRANS
from Verifier.PreVeriferProcessing.preprocessor import preprocess
from Verifier.PreVeriferProcessing.expression_trans import INT_VARIABLE_CORRESPONDENCE

import z3


# returns object of type Verification
def verify(code: ParserNode, 
           flags):

    # preprocess

    try:
        code = ParserNode("seq", code.value, preprocess(code, flags=flags))
    except RecursionError:
        print("There was a recursion error in translating the functions")
        return
    
    if flags["pre"]:
        print("==================================")
        print("Preprocessor results:\n")
        print(code.to_while_str())
        print("=================================\n")

    vc, logical_conds = verification_condition(z3.BoolVal(True), code, z3.BoolVal(True), -1)
    # print(INT_VARIABLE_CORRESPONDENCE)
    
    for (condition, line_number) in vc:
        if line_number == -1:
            # this is the EOF verfication that is used to kickstart the verification 
            # process. We can ignore it
            continue
        if logical_conds != []:
            for func_cond in logical_conds:
                condition = z3.Implies(func_cond,condition)
  
        if flags["VC"]:
            print(f"verifying {condition} in line number: {line_number}")

        solver = z3.Solver()
   
        solver.add(z3.Not(condition))
        status = solver.check()

        if status == z3.sat:
            print(f"Unable to verify condition in line {line_number}, e.g.:\n[")
            model = solver.model()
            for v in model:
                name = v.name()
                if name in UNDEFINED_VAR_TRANS:
                    name = UNDEFINED_VAR_TRANS[name]
                
                if name[0] == "@" and not flags["inner"]:
                    # internal variable
                    continue
                
                print(f"    {name} = {model[v]},")
            print("]")
            return
    
        if status == z3.unknown:
            print(f"Unable to prove or disprove line {line_number}")
            return

    print("Verified!")
   


from Parser.parser import ParserNode
from Verifier.verification_condition import verification_condition, UNDEFINED_VAR_TRANS
from Verifier.PreVeriferProcessing.preprocessor import preprocess


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

    vc, logical_conds = verification_condition(z3.BoolVal(True), code, z3.BoolVal(True), "",
                                               "" if flags["annot"] else None)
    # print(INT_VARIABLE_CORRESPONDENCE)
    
    if flags["annot"]:
        print("==================================")
        print("Annotated results:\n")
        print(code.annot)
        print("=================================\n")

    vc = list(vc)
    
    index = 0
    for (condition, cond_desc) in vc:
        if cond_desc == "":
            # this is the EOF verfication that is used to kickstart the verification 
            # process. We can ignore it
            continue
            
        index += 1

        if logical_conds != []:
            for func_cond in logical_conds:
                condition = z3.Implies(func_cond,condition)
  
        if flags["VC"]:
            print("=================================")
            print(f"VC #{index}:\n{condition}: {cond_desc}")

        solver = z3.Solver()
   
        solver.add(z3.Not(condition))
        status = solver.check()

        if status == z3.sat:
            print(f"Unable to verify: {cond_desc}, e.g.:\n[")
            model = solver.model()
            for v in model:
                name = v.name()
                if name in UNDEFINED_VAR_TRANS:
                    name, lineno = UNDEFINED_VAR_TRANS[name]
                    name = f"{name} [AFTER LOOP IN LINE {lineno}]"
                
                if name[0] == "@":
                    # internal variable
                    continue
                
                print(f"    {name} = {model[v]},")
            print("]")
            return
    
        if status == z3.unknown:
            print(f"Unable to prove or disprove: {cond_desc}")
            if flags["ignore_unknown"]:
                continue
            return
        
        if flags["VC"]:
            print("Verified!")

    if flags["VC"]:
        print("=================================")
        print("Verified all VCs!")
    else:
        print("Verified!")
   

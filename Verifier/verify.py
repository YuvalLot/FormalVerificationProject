
from Parser.parser import ParserNode
from Verifier.verifcation_condition import verification_condition

import z3


# returns object of type Verification
def verify(code: ParserNode):
    vc = verification_condition(z3.BoolVal(True), code, z3.BoolVal(True), -1)

    for (condition, line_number) in vc:
        print(f"verifying {condition} in line number(s): "
              f"{', '.join(map(str, line_number))}")
        solver = z3.Solver()

        solver.add(z3.Not(condition))

        if solver.check() == z3.sat:
            print(f"Unable to verify condition in line {line_number}, e.g.: ")
            print(solver.model())
            return
    
    print("Verified!")

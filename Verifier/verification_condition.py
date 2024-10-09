
from Parser.parser_node import ParserNode
from Verifier.helper import get_free_vars, join_conditions
import z3

"""
POSSIBLE_NODE_NAMES = [
    "op+", "op-", "op*", "op/", "op&&", "op||", "op~", "leaf",       # expression types
    "op%",

    "skip", "assign",  # command types
    "print"

    "while", "if", "seq",
]
"""

ALLOWED_COMMANDS = [
    "skip", "assign", "seq", "print", "if", "assume",
    "while", "def", "forall"
]

INNER_RET_VARIABLE = z3.Int("RET")

UNDEFINED_VAR_COUNT = 0
UNDEFINED_VAR_TRANS = {}


"""
returns a list of conditions so that {pre_cond}code{post_cond} is valid
if and only if the returns list is all valid.

returns: list[ ( z3.BoolRef, int ) ]
"""
def verification_condition(pre_cond: z3.BoolRef, 
                           code: ParserNode, 
                           post_cond: z3.BoolRef, 
                           post_line_no: int,
                           annot):

    side_eff = []
    wlps_linenos, logical_functions = weakest_liberal_pre(code, post_cond, post_line_no, side_eff, annot)

    return side_eff + \
        [(z3.Implies(pre_cond, wlp), lineno) for (wlp, lineno) in wlps_linenos], logical_functions

    # print(f"Trying to verify: {{ {pre_cond} }} {code} {{ {post_cond} }}")


"""
returns list[ (P: z3.BoolRef, derived_from_lines: int) ]

P: the weakest precondition {P} so that {P}code{Q} is valid, 
   if all of the conditions added to side_effects are valid

   The reason this is a list, and not an AND clause of all the items in the list, 
   is that we can track which requirements came from which lines

post_line_no: line number that derive P (for debugging purposes)
"""
def weakest_liberal_pre(code: ParserNode,
                        post_cond: z3.BoolRef,
                        post_line_no: int,
                        side_effects: list[(z3.BoolRef, int)],
                        annot):
    
    global UNDEFINED_VAR_COUNT
    
    assert isinstance(post_cond, z3.BoolRef), f"{post_cond}"

    # print(f"Trying to verify: {{ {pre_cond} }} {code} {{ {post_cond} }}")

    if code.name == "assign":
        variable = code.children[0].to_z3_int()
        expression = code.children[1].to_z3_int()
        updated_post = z3.substitute(
            post_cond, 
            (variable, expression)
            )
        
        if annot is not None:
            code.annot = annot + code.to_while_str()

        return [ (updated_post, post_line_no) ], []
    
    if code.name in ["skip", "print"] or code.is_expression:
        if annot is not None:
            code.annot = annot + code.to_while_str()
        return [(post_cond, post_line_no)], []
    
    if code.name == "if":

        if_cond, then_code, else_code = code.children
        if_cond = if_cond.to_z3_bool()
        new_annot = "\t" + annot if annot is not None else None
        then_wlps, _ = weakest_liberal_pre(then_code, post_cond, post_line_no, side_effects, new_annot)
        else_wlps, _ = weakest_liberal_pre(else_code, post_cond, post_line_no, side_effects, new_annot)

        ret = []

        # for each wlp of the then_clause, need to verify that the condition implies it
        for (then_wlp, then_lineno) in then_wlps:
            ret.append((
                z3.Implies(if_cond, then_wlp), then_lineno
            ))
        
        for (else_wlp, else_lineno) in else_wlps:
            ret.append((
                z3.Implies(z3.Not(if_cond), else_wlp), else_lineno
            ))

        # for each verification the then_clause needs to do, and each 
        # verifiction the else part needs to do, 
        # verify both
        """
        for (then_wlp, then_lineno) in then_wlps:
            for (else_wlp, else_lineno) in else_wlps:
                ret.append( 
                    ( 
                        z3.Or(z3.And(if_cond, then_wlp), 
                              z3.And(z3.Not(if_cond), else_wlp)),
                        then_lineno.union(else_lineno) 
                    )
                )
        """
        if annot is not None:
            code.annot = annot + f"if {code.children[0].to_while_str()} then {{\n" + \
                         then_code.annot + f"\n{annot}}} else {{" + \
                         else_code.annot + f"\n{annot}}};"
            

        return ret, []

    if code.name == "seq": 
        current_posts = [(post_cond, post_line_no)]
        if annot is not None:
            code.annot = annot + join_conditions(current_posts)
       # to verify a sequence, calculate the wlp of each statement in reverse order
        index = len(code.children) - 1
        new_logical_funcs = []

        while index >= 0:
            child = code.children[index]
            index -= 1
            
            next_posts = []
            

            for (current_post, current_derived) in current_posts:
                # 'chain' the post conditions:
                # whatever pre conditions needed ro get all post conditions
                # gained so far
                next_wlp = \
                    weakest_liberal_pre(child, 
                                        current_post,
                                        current_derived, 
                                        side_effects, annot)
                next_posts += next_wlp[0]

                for item in next_wlp[1]:
                    if item not in new_logical_funcs:
                        new_logical_funcs.append(item)
                
            if annot is not None:
                code.annot = annot + join_conditions(next_posts) + "\n" + \
                    child.annot + "\n" + code.annot
            current_posts = next_posts

        return current_posts, new_logical_funcs

    if code.name == "assert":
        condition_asserted = code.children[0].to_z3_bool()
        
        """
        We want to support two seperate goals when encountering 'assert b':
        1. we want to verify that the assert is true, 
           i.e. the precondition implies b
        2. we want to verify that the precondition implies (b -> post condition)
        note that these two together are equivalent to 
        the precondition implying the post condition and the assettion b.

        if post_cond is exactly the value True, we skip 2 (since it is obvious)
        """
        
        if annot is not None:
            code.annot = annot + code.to_while_str()

        if post_cond == z3.BoolVal(True):
            return [(condition_asserted, code.value.lineno)], []
        
        return [(condition_asserted, code.value.lineno), 
            (z3.Implies(condition_asserted, post_cond), post_line_no)], []
        
    
    if code.name == "assume":
        """
        this is similar to the assert case, except we only check that 
        if we reached here and the assumption happens, then the rest also happens
        formally, we can imagine 'assume b' is equivalent to:
            if b then skip else while (1) {skip} ;
        {P} assume b {Q} is (partially) correct if and only if 
            P -> (b -> Q), 
        since if P is true but b is false, the program will not stop, 
        making the Hoare triple valid.
        """
        if annot is not None: 
            code.annot = annot + code.to_while_str()

        condition_assumed = code.children[0].to_z3_bool()
        return [(z3.Implies(condition_assumed, post_cond), post_line_no)], []

    if code.name == "while":

        while_cond, while_inv, while_body = code.children
        
        if while_inv is None:
            print("WARNING: loop without inv")
            while_inv_line = code.value.lineno
            while_inv = z3.BoolVal(True)
        
        else:
            while_inv_line = while_inv.value.lineno
            while_inv = while_inv.children[0].to_z3_bool()
        
        while_cond = while_cond.to_z3_bool() 

        involved_variables : set = while_body.changing_vars

        """
        old approach:
        side_effects.append(
            (z3.Implies(z3.And(while_inv, z3.Not(while_cond)), post_cond), post_line_no),
        )
        """

        # side effects that make sure the loop is correct, i.e. the loop invariant
        # is preserved 
        # if the internal verification has alreay been added, no need to add again
        if not code.added_internal_verification:
            new_annot = "\t" + annot if annot is not None else None
            wlps_while_inv, _ = weakest_liberal_pre(
                while_body, while_inv, while_inv_line, side_effects, new_annot
            )
            if annot is not None:
                code.annot = annot + f"while ({code.children[0].to_while_str()}) {{" + \
                    while_body.annot + "\n" + annot + "}"

            for (wlp_inv, lines_derived) in wlps_while_inv:
                
                side_effects.append(
                    (
                        z3.Implies(z3.And(while_cond, while_inv), wlp_inv), 
                        lines_derived
                    )
                )
            
            code.added_internal_verification = True

        dictionary = []
        for variable in involved_variables:
            undefined_variable = z3.Int(f"${UNDEFINED_VAR_COUNT}")
            
            dictionary.append((z3.Int(variable), undefined_variable))
            UNDEFINED_VAR_TRANS[f"${UNDEFINED_VAR_COUNT}"] = (variable, 
                                                              code.value.lineno)
            
            UNDEFINED_VAR_COUNT += 1

        undefined_inv = z3.substitute(while_inv, dictionary)   
        undefined_cond = z3.substitute(while_cond, dictionary)   
        undefined_post = z3.substitute(post_cond, dictionary)

        return [(while_inv, while_inv_line), 
                (z3.Implies(
                    z3.And(undefined_inv, z3.Not(undefined_cond)), 
                    undefined_post), post_line_no)
        ], []

    if code.name == "error":
        if annot is not None: 
            code.annot = annot + code.to_while_str()
        return [z3.BoolVal(False), code.value.lineno], []

    if code.name == "def": 
        """
        To verify a function definition, we add side effect(s) that verify the function's
        pre-condition implies the wlp of the function's post-condition
        """

        func_name, func_param, _, func_code, _ = code.children

        # add the side effects
        if not code.added_internal_verification:
            new_annot = "\t" + annot if annot is not None else None
            func_verification = verification_condition(z3.BoolVal(True), 
                                                func_code, 
                                                z3.BoolVal(True), 
                                                code.value.lineno, 
                                                annot = new_annot)
            side_effects += func_verification[0]
            code.added_internal_verification = True
            if annot is not None:
                code.annot = annot + f"def {func_name.to_while_str()}({func_param.to_while_str()}) {{\n" + \
                    func_code.annot + "\n" + annot + "};"

        # other than the side effects, function definition essentially acts as a skip;
        return [(post_cond, post_line_no)], []

    if code.name == "return":
        # {P} return e; {Q} 
        # is valid iff P => Q[e/RET]
        if annot is not None: 
            code.annot = annot + code.to_while_str()

        updated_post = z3.substitute(post_cond, 
                                     (INNER_RET_VARIABLE, code.children[0].to_z3_int())
                                     )
        
        return [(updated_post, post_line_no)], []

    if code.name == "forall":
        variable = code.children[0]
        if variable.name == "leaf":
            variables = [variable.to_z3_int()]
        else:
            variables = [v.to_z3_int() for v in variable.children]
        expression = code.children[1].to_z3_bool()
    
        forall_assumption = z3.ForAll(variables, expression)

        if annot is not None: 
            code.annot = annot + code.to_while_str()
    
        return [(post_cond, post_line_no)], [forall_assumption]


    else:
        raise ValueError(f"Error: command {code.name} not yet supported.")




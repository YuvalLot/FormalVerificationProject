
from Parser.parser_node import ParserNode
import z3

"""
POSSIBLE_NODE_NAMES = [
    "op+", "op-", "op*", "op/", "op&&", "op||", "op~", "leaf",       # expression types
    
    "skip", "assign",  # command types
    "print"

    "while", "if", "seq",
]
"""

ALLOWED_COMMANDS = [
    "skip", "assign", "seq", "print", "if", "assume",
    "while"
]


"""
returns a list of conditions so thet {pre_cond}code{post_cond} is valid
if and only if the returns list is all valid.

returns: list[(z3.BoolRef, int)]
"""
def verification_condition(pre_cond: z3.BoolRef, 
                           code: ParserNode, 
                           post_cond: z3.BoolRef, 
                           post_line_no: int):
    assert not code.is_expression

    side_eff = []
    wlp, lineno = weakest_liberal_pre(code, post_cond, {post_line_no}, side_eff)
    
    side_eff.append((z3.Implies(pre_cond, wlp), lineno))

    return side_eff

    # print(f"Trying to verify: {{ {pre_cond} }} {code} {{ {post_cond} }}")

"""
returns (P: z3.BoolRef, derived_from_lines: list[int])

P: the weakest precondition {P} so that {P}code{Q} is valid, 
   if all of the conditions added to side_effects are valid

derived_from_line: line number that derives P

"""
def weakest_liberal_pre(code: ParserNode,
                        post_cond: z3.BoolRef,
                        post_line_no: set[int],
                        side_effects: list[(z3.BoolRef, int)]):
    assert not code.is_expression
    assert isinstance(post_cond, z3.BoolRef), f"{post_cond}"


    # print(f"Trying to verify: {{ {pre_cond} }} {code} {{ {post_cond} }}")

    if code.name == "assign":
        variable = code.children[0].to_z3_int()
        expression = code.children[1].to_z3_int()
        updated_post = z3.substitute(
            post_cond, 
            (variable, expression)
            )
        return updated_post, post_line_no
    
    if code.name in ["skip", "print"]:
        return post_cond, post_line_no
    
    if code.name == "if":
        if_cond, then_code, else_code = code.children
        if_cond = if_cond.to_z3_bool()
        then_wlp, then_lineno = weakest_liberal_pre(then_code, post_cond, post_line_no, side_effects)
        else_elp, else_lineno = weakest_liberal_pre(else_code, post_cond, post_line_no, side_effects)
        return z3.Or(z3.And(if_cond, then_wlp), 
                     z3.And(z3.Not(if_cond), else_elp)), then_lineno.union(else_lineno)

    """
    if b then {while b' {inv} } else {code;} 
    {Q}
    """

    if code.name == "seq": 
        current_post = post_cond 
        current_derived = post_line_no
        index = len(code.children) - 1

        while index >= 0:
            child = code.children[index]
            index -= 1

            current_post, current_derived = \
                weakest_liberal_pre(child, 
                                    current_post,
                                    current_derived, 
                                    side_effects)
        
        return current_post, current_derived

    if code.name == "assert":
        condition_asserted = code.children[0].to_z3_bool()
        if post_cond == z3.BoolVal(True):
            return condition_asserted, {code.value.lineno}
        return z3.And(post_cond, condition_asserted), post_line_no
        """
        TODO: for the future, support two seperate seqrches
        return condition_asserted, code.lineno
        return z3.Or(post_cond, z3.Not(condition_asserted)), post_line_no
        """
    
    if code.name == "assume":
        condition_assumed = code.children[0].to_z3_bool()
        return z3.Or(post_cond, z3.Not(condition_assumed)), post_line_no

    if code.name == "while":
        while_cond, while_inv, while_body = code.children
        
        if while_inv is None:
            print("WARNING: loop without inv")
            side_effects.append((post_cond, post_line_no))
            return z3.BoolVal(True), -1
        
        while_inv_line = while_inv.value.lineno
        while_inv = while_inv.children[0].to_z3_bool()
        while_cond = while_cond.to_z3_bool()    

        side_effects.append(
            (z3.Implies(z3.And(while_inv, z3.Not(while_cond)), post_cond), post_line_no),
        )

        wlp_inv, lines_derived = weakest_liberal_pre(
            while_body, while_inv, {while_inv_line}, side_effects
        )

        side_effects.append(
            (
                z3.Implies(z3.And(while_cond, while_inv), wlp_inv), 
                lines_derived
            )
        )

        return while_inv, {while_inv_line}

    else:
        raise ValueError(f"Error: command {code.name} not yet supported.")



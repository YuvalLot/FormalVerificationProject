
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


# verify that if pre_cond is true (==1), and code is executed,
# then post_cond is true
# if successful, return (0, list[(VC, line)])
# else, return (1, error_msg)
def verification_condition(pre_cond: z3.BoolRef, code: ParserNode, 
                           post_cond: z3.BoolRef, 
                           line_number_of_post):
    assert not code.is_expression

    # print(f"Trying to verify: {{ {pre_cond} }} {code} {{ {post_cond} }}")

    if code.name == "assign":
        
        variable = code.children[0].to_z3_int()
        expression = code.children[1].to_z3_int()
        updated_post = z3.substitute(
            post_cond, 
            (variable, expression)
            )

        # print(f"post_before: {post_cond}, post_after: {updated_post}")

        return [(z3.Implies(
            pre_cond,
            updated_post
        ), line_number_of_post)]
    
    if code.name in ["skip", "print"]:
        return [(z3.Implies(
            pre_cond,
            post_cond,
        ), line_number_of_post)]
    
    if code.name == "if":
        if_cond, then_code, else_code = code.children
        vc_positive = verification_condition(
            z3.And(pre_cond, if_cond.to_z3_bool()), 
            then_code, 
            post_cond, 
            line_number_of_post
        )

        vc_negative = verification_condition(
            z3.And(pre_cond, z3.Not(if_cond.to_z3_bool())), 
            else_code, 
            post_cond,
            line_number_of_post
        ) 

        return vc_positive + vc_negative

    if code.name == "seq":

        working_condition : z3.BoolRef = pre_cond
        vc_s = []
        index = 0

        while index < len(code.children):
            child = code.children[index]
            index += 1
            
            if child.name == "assert":
                child = ParserNode("skip", None, [])
                index -= 1

            if child.name in ALLOWED_COMMANDS:

                # collecting the post condition
                current_post_conditions = []
                while index < len(code.children) and \
                      code.children[index].name == "assert":
                    current_post_conditions.append((
                          code.children[index].children[0].to_z3_bool(),
                          code.children[index].value.lineno
                    ))
                    index += 1

                if index == len(code.children):
                    current_post_conditions.append(
                        (post_cond, line_number_of_post)
                    )

                for (condition, line_number) in current_post_conditions:
                    vc_s += verification_condition(
                        working_condition, 
                        child, 
                        condition,
                        line_number
                    )

                working_condition = z3.And(
                    *([pair[0] for pair in current_post_conditions])
                )

        if len(code.children) == 0:
            vc_s.append((z3.Implies(pre_cond, post_cond), line_number_of_post))

        return vc_s

    if code.name == "assert":
        condition_asserted = code.children[0].to_z3_bool()
        return [(z3.Implies(pre_cond, condition_asserted), code.value.lineno),
                (z3.Implies(condition_asserted, post_cond), line_number_of_post)]
    
    if code.name == "assume":
        condition_assumed = code.children[0].to_z3_bool()
        return [(z3.Implies(condition_assumed, post_cond), line_number_of_post)]
    
    if code.name == "while":
        while_cond, while_inv, while_body = code.children
        print(while_cond, while_inv, while_cond)
        if while_inv is None:
            return [(post_cond, line_number_of_post)]
        
        while_inv_line = while_inv.value.lineno
        while_inv = while_inv.children[0].to_z3_bool()
        while_cond = while_cond.to_z3_bool()
        
        return [(z3.Implies(pre_cond, while_inv), while_inv_line), 
                (z3.Implies(z3.And(while_inv, z3.Not(while_cond)), post_cond), 
                 line_number_of_post)
                ] + \
                verification_condition(
                    z3.And(while_inv, while_cond),
                    while_body,
                    while_inv, 
                    while_inv_line
                )

    else:
        raise ValueError(f"Error: command {code.name} not yet supported.")

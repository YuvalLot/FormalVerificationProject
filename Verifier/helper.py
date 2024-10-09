
import z3


def get_free_vars(exp):
    if z3.is_int(exp) and exp.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        return [exp.decl().name()]
    
    ret = []
    for child in exp.children():
        ret += get_free_vars(child)

    return ret


def join_conditions(conds):
    return " ; ".join(f"{{{cond[0]}}}" for cond in conds)


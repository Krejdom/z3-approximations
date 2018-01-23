import sys
from enum import Enum
from z3 import *


class Quantification(Enum):
    UNIVERSAL = 0
    EXISTENTIAL = 1


# example: "../BV_benchmarky/2017-Preiner/psyco/001.smt2"
formula_file = sys.argv[1]

formula = z3.parse_smt2_file(formula_file)


def aproximate(formula):
    number = 0
    formula = formula.__rand__(number)
    return formula


def rec_go_q(formula, var_list):

    if formula.is_forall():
        quantification = Quantification.UNIVERSAL
    else:
        quantification = Quantification.EXISTENTIAL

    for i in range(formula.num_vars()):
        var_list.append((formula.var_name(i), quantification))

    body = rec_go(formula.body(), var_list)
    q_vars = []

    for i in range(formula.num_vars()):
        name = formula.var_name(i)
        # Type BV
        if z3.is_bv_sort(formula.var_sort(i)):
            size = formula.var_sort(i).size()
            q_vars.append(BitVec(name, size))
        # Type Bool
        elif formula.var_sort(i).is_bool():
            q_vars.append(Bool(name))
        else:            
            print("Wrong type!")
            print(formula.var_sort(i))

    formula = ForAll(q_vars, body)
    return formula


def rec_go_f(formula, var_list):
    # constant
    if z3.is_const(formula):
        pass

    # variables
    elif z3.is_var(formula):
        order = len(var_list) - z3.get_var_index(formula) - 1
        if type(formula) == BitVecRef:
            formula = aproximate(formula)

    # complex formula
    else:
        new_children = []
        for i in range(len(formula.children())):
            new_children.append(rec_go(formula.children()[i], var_list))
        
        if formula.decl().name() == "and":
            formula = And(*new_children)
        elif formula.decl().name() == "or":
            formula = Or(*new_children)
        else:
            formula = formula.decl().__call__(*new_children)

    return formula


def rec_go(formula, var_list):
    if type(formula) == QuantifierRef:
        formula = rec_go_q(formula, var_list)
    else:
        formula = rec_go_f(formula, var_list)
    return formula


z3.solve(formula)
print()
z3.solve(rec_go(formula, []))


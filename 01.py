import sys
from enum import Enum
from z3 import *


class Quantification(Enum):
    UNIVERSAL = 0
    EXISTENTIAL = 1


formula_file = sys.argv[1]    # example: "../BV_benchmarky/2017-Preiner/psyco/001.smt2"

formula = z3.parse_smt2_file(formula_file)


#z3.solve(formula)
print("0.", formula)


def aproximate(formula):
        number = 0
        #print(formula.__rand__(number))
        formula = formula.__rand__(number)
        print("5.", formula)
        return formula


def rec_go_q(formula, var_list):

    if formula.is_forall():
        quantification = Quantification.UNIVERSAL
        #print("ForAll")
    else:
        quantification = Quantification.EXISTENTIAL
        #print("Exists")

    for i in range(formula.num_vars()):
        var_list.append((formula.var_name(i), quantification))
    #print(var_list)
    
    print("2.", formula)

    body = rec_go(formula.body(), var_list)
    q_vars = []
    
    for i in range(formula.num_vars()):
        if z3.is_bv_sort(formula.var_sort(i)):
            print("Type BV", formula.var_sort(i))
            q_vars.append(BitVec(formula.var_name(i), formula.var_sort(i).size()))
        else:
            # TODO
            print("Different type.")
            print(type(formula), formula)
        
    formula = ForAll(q_vars, body)
    
    print("OK.", formula)
    return formula


def rec_go_f(formula, var_list):

    # constant
    if z3.is_const(formula):
        pass
        #print(formula, "(CONST)")
    
    # variables
    elif z3.is_var(formula):
        print("4.", formula)
        order = len(var_list) - z3.get_var_index(formula) - 1
        #print(formula, var_list[order])
        
        if type(formula) == BitVecRef:
            formula = aproximate(formula)

    # complex formula
    else:
        print("3.", formula)
        
        new_children = []
        for i in range(len(formula.children())):
            print(i)
            new_children.append(rec_go(formula.children()[i], var_list))

        formula = formula.decl().__call__(*new_children)
       
    print("5a.", formula)
    return formula


def rec_go(formula, var_list):      
    if type(formula) == QuantifierRef:
        print("1.", formula)
        formula = rec_go_q(formula, var_list)    
    else:
        print("3a.", formula)
        formula = rec_go_f(formula, var_list)
        print("6.", formula)
    return formula

print()
print(rec_go(formula, []))
#z3.solve(formula)


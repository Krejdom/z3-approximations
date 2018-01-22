import sys
from enum import Enum
from z3 import *


class Quantification(Enum):
    UNIVERSAL = 0
    EXISTENCIONAL = 1


formula_file = sys.argv[1]    # example: "../BV_benchmarky/2017-Preiner/psyco/001.smt2"

formula = z3.parse_smt2_file(formula_file)


#z3.solve(formula)
# print(formula)


def aproximate(formula):
        number = 0b11
        return formula.__rand__(number)


def rec_go_q(formula, var_list):
    if formula.is_forall():
        quantification = Quantification.UNIVERSAL
        #print("ForAll")
    else:
        quantification = Quantification.EXISTENCIONAL
        #print("Exists")

    for i in range(formula.num_vars()):
        var_list.append((formula.var_name(i), quantification))
        #print(formula.var_name(i), end=" ")
    #print()
    
    rec_go(formula.body(), var_list)


def rec_go_f(formula, var_list):

    # constant
    if z3.is_const(formula):
        pass
        #print(formula, "(CONST)")
    
    # variables
    elif z3.is_var(formula):
        order = len(var_list) - z3.get_var_index(formula) - 1
        #print(formula, var_list[order])
        
        if type(formula) == BitVecRef:
            formula = aproximate(formula)

    # complex formula
    else:
        for child in formula.children():
            #print(formula.decl())

            rec_go(child, var_list) 


def rec_go(formula, var_list):      
    if type(formula) == QuantifierRef:
        rec_go_q(formula, var_list)
    else:
        rec_go_f(formula, var_list)
        

rec_go(formula, [])


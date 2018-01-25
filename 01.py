#!/usr/bin/python3

import sys
from enum import Enum
from z3 import *


class Quantification(Enum):
    UNIVERSAL = 0
    EXISTENTIAL = 1


class Polarity(Enum):
    POSITIVE = 0
    NEGATIVE = 1


max_bit_width = 1


def approximate(formula, var_list, approx_type, bit_places):
    """Approximate given formula.

    Arguments:
        formula     formula to approximate
        var_list    list of quantified variables
        approx_type approximation type (0, 1, 2)
        bit_places  new bit width
    """
    # Zero-extension (set the rest of bits to 0)
    if approx_type == 0:
        complement = BitVecVal(0, formula.size() - bit_places)

    # One-extension (set the rest of bits to 1)
    elif approx_type == 1:
        complement = BitVecVal(0, formula.size() - bit_places) - 1

    # Sign-extension (set the rest of bits to the value of the sign bit)
    elif approx_type == 2:
        sign_bit = Extract(bit_places - 1, bit_places - 1, formula)
        complement = sign_bit
        for _ in range(formula.size() - bit_places - 1):
            complement = Concat(sign_bit, complement)
    # TODO: right zero-extension, right one-extension, right sign-extension

    # Unknown type of approximation
    else:
        raise ValueError("Select approximation type (0, 1 or 2).")
    formula = Concat(complement, (Extract(bit_places - 1, 0, formula)))
    return formula


def q_var_list(formula):
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
            raise ValueError("Unknown type of variable:", formula.var_sort(i))

    return q_vars


def qform_process(formula, var_list, approx_type, q_type, bit_places, polarity):
    """Create new quantified formula with modified body.
    """

    # Identification of quantification type
    if ((formula.is_forall() and (polarity == Polarity.POSITIVE)) or
       ((not formula.is_forall()) and (polarity == Polarity.NEGATIVE))):
        quantification = Quantification.UNIVERSAL
    else:
        quantification = Quantification.EXISTENTIAL

    # Add quantified variables to the var_list
    for i in range(formula.num_vars()):
        var_list.append((formula.var_name(i), quantification))

    # Recursively process the body of the formula
    body = rec_go(formula.body(),
                  var_list,
                  approx_type,
                  q_type,
                  bit_places,
                  polarity)

    # Recreate the list of quantified variables
    q_vars = q_var_list(formula)

    # Create new quantified formula with modified body
    formula = ForAll(q_vars, body)

    return formula


def complexform_process(formula, var_list, approx_type, q_type, bit_places, polarity):
    new_children = []

    # Process implication with polarity switching
    if formula.decl().name() == "=>":
        # Switch polarity for the left part of implication
        if polarity == Polarity.POSITIVE:
            polarity2 = Polarity.NEGATIVE
        else:
            polarity2 = Polarity.POSITIVE

        new_children.append(rec_go(formula.children()[i],
                                   var_list,
                                   approx_type,
                                   q_type,
                                   bit_places,
                                   polarity2))
        new_children.append(rec_go(formula.children()[i],
                                   var_list,
                                   approx_type,
                                   q_type,
                                   bit_places,
                                   polarity))
        return Implies(*new_children)

    # Recursively process children of formula
    for i in range(len(formula.children())):
        new_children.append(rec_go(formula.children()[i],
                                   var_list,
                                   approx_type,
                                   q_type,
                                   bit_places,
                                   polarity))

    # Recreate trouble making operands with arity greater then 2
    if formula.decl().name() == "and":
        formula = And(*new_children)

    elif formula.decl().name() == "or":
        formula = Or(*new_children)

    elif formula.decl().name() == "bvadd":
        formula = new_children[0]
        for ch in new_children[1::]:
            formula = formula + ch

    elif (formula.decl().name() == "bvmul") and (len(new_children) > 2):
        raise ValueError("Fix needed (TODO: bvmul)")

    # TODO: bvmul
    # problems with Distinct() or multiplication may arrise
    # print(formula.decl().name())

    # Recreate problem-free operands
    else:
        formula = formula.decl().__call__(*new_children)

    return formula


def rec_go_f(formula, var_list, approx_type, q_type, bit_places, polarity):
    # Constant
    if z3.is_const(formula):
        pass

    # Variable
    elif z3.is_var(formula):
        order = len(var_list) - z3.get_var_index(formula) - 1

        # Approximate if var is bit-vecotr and is quantified in the right way
        if (type(formula) == BitVecRef) and (var_list[order][1] == q_type):

            # Update max bit-vector width
            global max_bit_width
            if max_bit_width < formula.size():
                max_bit_width = formula.size()

            formula = approximate(formula, var_list, approx_type, bit_places)

    # Complex formula
    else:
        formula = complexform_process(formula,
                                      var_list,
                                      approx_type,
                                      q_type,
                                      bit_places,
                                      polarity)

    return formula


def rec_go(formula, var_list, approx_type, q_type, bit_places, polarity):
    """Recursively go through the formula and aply approximations.
    """
    # Handle the quantifiers
    if type(formula) == QuantifierRef:
        formula = qform_process(formula,
                                var_list,
                                approx_type,
                                q_type,
                                bit_places,
                                polarity)

    # Ordinary formula
    else:
        formula = rec_go_f(formula,
                           var_list,
                           approx_type,
                           q_type,
                           bit_places,
                           polarity)

    return formula


def solve_with_approximations(formula, approx_type, q_type, bit_places, polarity):
    s = z3.Solver()
    approximated_formula = rec_go(formula,
                                  [],
                                  approx_type,
                                  q_type,
                                  bit_places,
                                  polarity)

    s.add(approximated_formula)
    result = s.check()

    if q_type == Quantification.UNIVERSAL:
        if result == CheckSatResult(Z3_L_TRUE):
            print("Over-approximation of the formula is satisfiable.")
            if bit_places < (max_bit_width - 1):
                print("Continue with bit-vecotr width", bit_places,
                  "(max "+ str(max_bit_width - 1) + ")") # debug only
                result = solve_with_approximations(formula,
                                          approx_type,
                                          q_type,
                                          (bit_places + 2),
                                          polarity)
            else:
                print("Cannot use approxamation. :(\n")
                print("Continue with original formula...")
                result = solve_without_approximations(formula)
        elif result == CheckSatResult(Z3_L_FALSE):
            print("Over-approximation of the formula is unsatisfiable.")
            print("Formula is unsatisfiable. :)\n")
        else:
            print("The result is unknown.")
    else:
        if result == CheckSatResult(Z3_L_TRUE):
            print("Under-approximation of the formula is satisfiable.")
            print("Formula is satisfiable. :)\n")
            print("The model follows:\n")
            z3.solve(formula)
        elif result == CheckSatResult(Z3_L_FALSE):
            print("Under-approximation of the formula is unsatisfiable.")
            if bit_places < (max_bit_width - 1):
                print("Continue with bit-vecotr width", bit_places,
                  "(max "+ str(max_bit_width - 1) + ")") # debug only
                solve_with_approximations(formula,
                                          approx_type,
                                          q_type,
                                          (bit_places + 2),
                                          polarity)
            else:
                print("Cannot use approxamation. :(\n")
                print("Continue with original formula...")
                result = solve_without_approximations(formula)

        else:
            print("The result is unknown.")

    return result


def solve_without_approximations(formula):
    s = z3.Solver()
    s.add(formula)
    # print("The result without approximations is:", s.check(), "\n")
    return s.check()


def main():
    # Load the file with formula.
    # example: "../BV_benchmarky/2017-Preiner/psyco/001.smt2"
    formula_file = sys.argv[1]

    # Parse SMT2 file.
    formula = z3.parse_smt2_file(formula_file)

    # Determine the type of approximation.
    # 0 ... zero-extension (set the rest of bits to 0)
    # 1 ... one-extension (set the rest of bits to 1)
    # 2 ... sign-extension (set the rest of bits to the value of the sign bit)
    approx_type = 0

    # Determine which variables (universaly or existentialy quantified) will be
    # approxamated.
    # Quantification.UNIVERSAL ... over-approximation
    # Quantification.EXISTENTIAL ... under-approximation
    q_type = Quantification.UNIVERSAL

    """
    args = sys.argv[1:]
    for formula_file in args:
        formula = z3.parse_smt2_file(formula_file)
        #print(formula)

        # Solve original formula (debug only)
        solve_original = solve_without_approximations(formula)

        # Solve formula and use approximations
        solve_approximated = solve_with_approximations(formula,
                                                       approx_type,
                                                       q_type,
                                                       bit_places=1,
                                                       polarity)
        print(solve_approximated)

        if solve_approximated == solve_original:
            print("OK")
        else:
            print("NOK", formula_file)
            break
    """

    # Solve original formula (debug only)
    print("Solved without approximations: ", end="")
    print(solve_without_approximations(formula))
    print()

    # Solve formula and use approximations
    print("Solved with approximations: ", end="")
    print(solve_with_approximations(formula,
                                    approx_type,
                                    q_type,
                                    bit_places=1,
                                    polarity=Polarity.POSITIVE))

if __name__ == "__main__":
    main()


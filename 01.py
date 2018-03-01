#!/usr/bin/python3

import sys
import multiprocessing
import time
from enum import Enum
from z3 import *


class Quantification(Enum):
    """Determine which variables (universaly or existentialy quantified)
    will be approxamated.
    """
    UNIVERSAL = 0       # over-approximation
    EXISTENTIAL = 1     # under-approximation


class Polarity(Enum):
    POSITIVE = 0
    NEGATIVE = 1


class ReductionType(Enum):
    ZERO_EXTENSION = 3
    ONE_EXTENSION = 1
    SIGN_EXTENSION = 2
    RIGHT_ZERO_EXTENSION = -3
    RIGHT_ONE_EXTENSION = -1
    RIGHT_SIGN_EXTENSION = -2


max_bit_width = 1


def zero_extension(formula, bit_places):
    """Set the rest of bits on the left to 0.
    """
    complement = BitVecVal(0, formula.size() - bit_places)
    formula = Concat(complement, (Extract(bit_places - 1, 0, formula)))

    return formula


def one_extension(formula, bit_places):
    """Set the rest of bits on the left to 1.
    """
    complement = BitVecVal(0, formula.size() - bit_places) - 1
    formula = Concat(complement, (Extract(bit_places - 1, 0, formula)))

    return formula


def sign_extension(formula, bit_places):
    """Set the rest of bits on the left to the value of the sign bit.
    """
    sign_bit = Extract(bit_places - 1, bit_places - 1, formula)

    complement = sign_bit
    for _ in range(formula.size() - bit_places - 1):
        complement = Concat(sign_bit, complement)

    formula = Concat(complement, (Extract(bit_places - 1, 0, formula)))

    return formula


def right_zero_extension(formula, bit_places):
    """Set the rest of bits on the right to 0.
    """
    complement = BitVecVal(0, formula.size() - bit_places)
    formula = Concat(Extract(formula.size() - 1,
                             formula.size() - bit_places,
                             formula),
                     complement)

    return formula


def right_one_extension(formula, bit_places):
    """Set the rest of bits on the right to 1.
    """
    complement = BitVecVal(0, formula.size() - bit_places) - 1
    formula = Concat(Extract(formula.size() - 1,
                             formula.size() - bit_places,
                             formula),
                     complement)

    return formula


def right_sign_extension(formula, bit_places):
    """Set the rest of bits on the right to the value of the sign bit.
    """
    sign_bit_position = formula.size() - bit_places
    sign_bit = Extract(sign_bit_position, sign_bit_position, formula)

    complement = sign_bit
    for _ in range(sign_bit_position - 1):
        complement = Concat(sign_bit, complement)

    formula = Concat(Extract(formula.size() - 1,
                             sign_bit_position,
                             formula),
                     complement)

    return formula


def approximate(formula, approx_type, bit_places):
    """Approximate given formula.

    Arguments:
        formula     formula to approximate
        approx_type approximation type (0, 1, 2)
        bit_places  new bit width
    """

    # Zero-extension
    if approx_type == ReductionType.ZERO_EXTENSION:
        return zero_extension(formula, bit_places)

    # One-extension
    elif approx_type == ReductionType.ONE_EXTENSION:
        return one_extension(formula, bit_places)

    # Sign-extension
    elif approx_type == ReductionType.SIGN_EXTENSION:
        return sign_extension(formula, bit_places)

    # Right-zero-extension
    elif approx_type == ReductionType.RIGHT_ZERO_EXTENSION:
        return right_zero_extension(formula, bit_places)

    # Right-one-extension
    elif approx_type == ReductionType.RIGHT_ONE_EXTENSION:
        return right_one_extension(formula, bit_places)

    # Right-sign-extension
    elif approx_type == ReductionType.RIGHT_SIGN_EXTENSION:
        return right_sign_extension(formula, bit_places)

    # Unknown type of approximation
    else:
        raise ValueError("Select approximation type.")


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


def qform_process(formula, var_list, approx_type,
                  q_type, bit_places, polarity):
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
    if formula.is_forall():
        formula = ForAll(q_vars, body)
    else:
        formula = Exists(q_vars, body)

    return formula


def complexform_process(formula, var_list, approx_type,
                        q_type, bit_places, polarity):
    new_children = []

    # Process implication with polarity switching
    if formula.decl().name() == "=>":
        # Switch polarity for the left part of implication
        if polarity == Polarity.POSITIVE:
            polarity2 = Polarity.NEGATIVE
        else:
            polarity2 = Polarity.POSITIVE
        new_children.append(rec_go(formula.children()[0],
                                   var_list,
                                   approx_type,
                                   q_type,
                                   bit_places,
                                   polarity2))
        new_children.append(rec_go(formula.children()[1],
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
            formula = approximate(formula, approx_type, bit_places)
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


def continue_with_approximation(formula, approx_type, q_type, bit_places,
                                polarity, result_queue):
    if bit_places < (max_bit_width - 2):
        # Swith left/right approximation
        if approx_type.value > 0:
            approx_type = ReductionType(- approx_type.value)
        else:
            approx_type = ReductionType(- approx_type.value)

            # Resize bit width
            if bit_places == 1:
                bit_places += 1
            else:
                bit_places += 2

        return solve_with_approximations(formula,
                                         approx_type,
                                         q_type,
                                         bit_places,
                                         polarity,
                                         result_queue)
    else:
        # print("Cannot use approxamation. :(\n")
        # print("Continue with original formula...")
        return solve_without_approximations(formula, result_queue)


def solve_with_approximations(formula, approx_type, q_type,
                              bit_places, polarity, result_queue):
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
        # Over-approximation of the formula is SAT. Approximation continues.
        if result == CheckSatResult(Z3_L_TRUE):
            result = continue_with_approximation(formula, approx_type, q_type,
                                                 bit_places, polarity,
                                                 result_queue)
        # Over-approximation of the formula is UNSAT. Original formula is UNSAT.
        elif result == CheckSatResult(Z3_L_FALSE):
            pass
        # The result is unknown.
        else:
            pass

    else:
        # Under-approximation of the formula is SAT. Original formula is SAT.
        if result == CheckSatResult(Z3_L_TRUE):
            pass
            # print("U: The model follows:")    # DEBUG
            z3.solve(approximated_formula)                 # DEBUG
            print(approximated_formula)
        # Under-approximation of the formula is UNSAT. Approximation continues.
        elif result == CheckSatResult(Z3_L_FALSE):
            result = continue_with_approximation(formula, approx_type, q_type,
                                                 bit_places, polarity,
                                                 result_queue)
        # The result is unknown.
        else:
            pass

    result_queue.put(result)
    return result


def solve_without_approximations(formula, result_queue):
    s = z3.Solver()
    s.add(formula)
    # print("The result without approximations is:", s.check(), "\n")
    result_queue.put(s.check())
    return s.check()


def run_paralell(formula, approx_type, final_result_queue):
    result_queue = multiprocessing.Queue()

    p1 = multiprocessing.Process(target=solve_with_approximations,
                                 args=(formula,
                                       approx_type,
                                       Quantification.UNIVERSAL,
                                       1,
                                       Polarity.POSITIVE,
                                       result_queue))

    p2 = multiprocessing.Process(target=solve_with_approximations,
                                 args=(formula,
                                       approx_type,
                                       Quantification.EXISTENTIAL,
                                       1,
                                       Polarity.POSITIVE,
                                       result_queue))
    p1.start()
    p2.start()

    result = result_queue.get()

    p1.terminate()
    p2.terminate()

    final_result_queue.put(result)


def main():
    # Load the file with formula.
    # example: "../BV_benchmarky/2017-Preiner/psyco/001.smt2"
    # formula_file = sys.argv[1]

    # Determine the type of approximation.
    approx_type = ReductionType.ONE_EXTENSION

    args = sys.argv[1:]
    for i in range(len(args)):
        formula_file = sys.argv[i+1]
        formula = z3.parse_smt2_file(formula_file)

        with multiprocessing.Manager() as manager:
            result_queue = multiprocessing.Queue()
            # return_dict = manager.dict() #OLD DELETE

            # ORIGINAL FORMULA
            p = multiprocessing.Process(target=solve_without_approximations,
                                        args=(formula, result_queue))
            p.start()
            # Wait for 10 seconds or until process finishes
            p.join(60)

            # If thread is still active
            if p.is_alive():
                print("TIME-OUT1", formula_file)
                p.terminate()
                p.join()
                continue

            solve_original = result_queue.get()

            # APPROXIMATED FORMULA
            p0 = multiprocessing.Process(target=run_paralell,
                                         args=(formula,
                                               approx_type,
                                               result_queue))
            p0.start()
            # Wait for 10 seconds or until process finishes
            p0.join(60)

            # If thread is still active
            if p0.is_alive():
                print("TIME-OUT2", formula_file)
                p0.terminate()
                p0.join()
                continue

            solve_approximated = result_queue.get()

            # Compare original and approximation result
            if solve_original == solve_approximated:
                print("OK       ", formula_file)
            else:
                print("NOK      ", formula_file)
                print("original:", solve_original)
                print("approximated:", solve_approximated)
                break

if __name__ == "__main__":
    main()


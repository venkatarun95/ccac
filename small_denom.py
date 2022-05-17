''' Produce solutions with small denominators '''

from fractions import Fraction
import logging
import math
from typing import Optional, Tuple
from z3 import If, Or, Real, CheckSatResult

from .binary_search import BinarySearch
from .cache import ModelDict, model_to_dict
from .my_solver import MySolver

logger = logging.getLogger('ccac')

def find_small_denom_soln(s: MySolver, max_denom: int) -> Tuple[CheckSatResult, Optional[ModelDict]]:
    '''Find a solution that tries to maximize the number of variables that have a
    demoninator smaller than `max_denom`
    '''

    orig_sat = s.check()
    if str(orig_sat) != "sat":
        return orig_sat, None

    m = model_to_dict(s.model())

    best_m = m
    best_obj = 0

    # Number of variables that newly have a small denominator
    objective = 0
    max_objective = 0
    old_obj = 0
    for vname in m:
        if type(m[vname]) is Fraction:
            val = m[vname]
            assert isinstance(val, Fraction)
            if val.denominator > max_denom:
                # Fractions just above and below the value
                num = math.ceil(Fraction(val.numerator * max_denom,
                                         val.denominator))
                hi = Fraction(num, max_denom)
                lo = Fraction(num - 1, max_denom)
                assert lo < val and val < hi, f"Error in computing hi={hi} and lo={lo} for {val}"

                s.add(Or(
                    Real(vname) == val, Real(vname) == lo, Real(vname) == hi))

                objective += If(Real(vname) == val, 0, 1)
                max_objective += 1
            else:
                s.add(Real(vname) == val)
                old_obj += 1


    search = BinarySearch(0, max_objective, 1)
    while True:
        pt = search.next_pt()
        if pt is None:
            break

        # Round to integer
        pt_int = round(pt)

        s.push()
        s.add(objective >= pt_int)
        sat = str(s.check())

        if sat == "sat":
            search.register_pt(pt, 1)
            if pt_int > best_obj:
                best_m = model_to_dict(s.model())
                best_obj = pt_int

        elif sat == "unknown":
            search.register_pt(pt, 2)
        else:
            assert sat == "unsat", f"Unknown value: {sat}"
            search.register_pt(pt, 3)

        s.pop()

    search.get_bounds()

    new_obj = 0
    for vname in best_m:
        if type(best_m[vname]) is Fraction:
            val = best_m[vname]
            assert isinstance(val, Fraction)
            if val.denominator <= max_denom:
                new_obj += 1
    logger.info(f"Improved number of small numbers from {old_obj} to {new_obj} out of a max of {old_obj + max_objective}")

    return orig_sat, best_m
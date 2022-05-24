''' Produce solutions with small denominators '''

from fractions import Fraction
import logging
import math
from typing import Set, Optional, Tuple
from z3 import CheckSatResult, If, Or, Real, ModelRef

from pyz3_utils.common import GlobalConfig

from .binary_search import BinarySearch
from .cache import ModelDict, model_to_dict
from .my_solver import MySolver

logger = logging.getLogger('pyz3_utils')
GlobalConfig().default_logger_setup(logger)

def find_small_denom_soln(s: MySolver,
                          max_denom: int,
                          target_vars: Optional[Set[str]] = None
                          ) -> Tuple[CheckSatResult, Optional[ModelDict], Optional[ModelRef]]:
    '''Find a solution that tries to maximize the number of variables that have a
    demoninator smaller than `max_denom`. If target_vars is not None, focusses
    only on making the given variables (specified by their name) have a small
    denominator.

    '''

    ctx = s.ctx
    orig_sat = s.check()
    if str(orig_sat) != "sat":
        return orig_sat, None, None

    m_model = s.model()
    m = model_to_dict(m_model)

    # Isolate the constraints this function adds from the outside.
    s.push()

    best_m_model = m_model
    best_m = m
    best_obj = 0

    # Number of variables that newly have a small denominator
    objective = 0
    max_objective = 0
    old_obj = 0
    for vname in m:
        if target_vars is not None and vname not in target_vars:
            continue
        if type(m[vname]) is Fraction:
            val = m[vname]
            assert isinstance(val, Fraction)

            # Fractions just above and below the value
            num = math.ceil(Fraction(val.numerator * max_denom,
                                     val.denominator))
            hi = Fraction(num, max_denom)
            lo = Fraction(num - 1, max_denom)
            assert lo <= val and val <= hi, f"Error in computing hi={hi} and lo={lo} for {val}"

            # Value is either the original or a value just above or below the
            # original
            s.add(Or(
                Real(vname, ctx) == val, Real(vname, ctx) == lo, Real(vname, ctx) == hi))

            if val.denominator > max_denom:
                objective += If(Real(vname, ctx) == val, 0, 1)
                max_objective += 1
            else:
                old_obj += 1
        else:
            if target_vars is not None:
                logger.warn(f"Warning: `{vname}` present in `target_vars`, but its type is `{type(m[vname])}`, not `Fraction`")


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
                best_m_model = s.model()
                best_m = model_to_dict(best_m_model)
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
        if (type(best_m[vname]) is Fraction and
            (target_vars is None or vname in target_vars)):
            val = best_m[vname]
            assert isinstance(val, Fraction)
            if val.denominator <= max_denom:
                new_obj += 1
    logger.info(f"Improved number of small numbers from {old_obj} to {new_obj} out of a max of {old_obj + max_objective}")

    # Remove all constraints we added
    s.pop()
    # s.check() This check might not return the best model... SO returning actual model also.
    return orig_sat, best_m, best_m_model

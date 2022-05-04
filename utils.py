from fractions import Fraction
from typing import Callable, Dict, Union
import z3

from config import ModelConfig
from pyz3_utils import BinarySearch, MySolver

ModelDict = Dict[str, Union[Fraction, bool]]


def model_to_dict(model: z3.ModelRef) -> ModelDict:
    ''' Utility function that takes a z3 model and extracts its variables to a
    dict'''
    decls = model.decls()
    res: Dict[str, Union[float, bool]] = {}
    for d in decls:
        val = model[d]
        if type(val) == z3.BoolRef:
            res[d.name()] = bool(val)
        elif type(val) == z3.IntNumRef:
            res[d.name()] = Fraction(val.as_long())
        else:
            # Assume it is numeric
            res[d.name()] = val.as_fraction()
    return res


def make_periodic(c, s, v, dur: int):
    '''A utility function that makes the solution periodic. A periodic solution
    means the same pattern can repeat indefinitely. If we don't make it
    periodic, CCAC might output examples where the cwnd is very low to begin
    with, and *therefore* the utilization is low. If we are looking for
    examples that hold in steady-state, then making things periodic is an easy
    way to do that.

    `dur` is the number of timesteps for which the cwnd of our CCA is
    arbitrary. They are arbitrary to ensure the solver can pick any initial
    conditions. For AIMD dur=1, for Copa dur=c.R+c.D, for BBR dur=2*c.R

    '''
    s.add(v.A[-1] - v.L[-1] - (c.C * (c.T - 1) - v.W[-1]) == v.A[0] - v.L[0] -
          (-v.W[0]))
    for n in range(c.N):
        s.add(v.A_f[n][-1] - v.L_f[n][-1] - v.S_f[n][-1] == v.A_f[n][0] -
              v.L_f[n][0] - v.S_f[n][0])
        s.add(v.L_f[n][-1] - v.Ld_f[n][-1] == v.L_f[n][0] - v.Ld_f[n][0])
        for dt in range(dur):
            s.add(v.c_f[n][c.T - 1 - dt] == v.c_f[n][dur - 1 - dt])
            s.add(v.r_f[n][c.T - 1 - dt] == v.r_f[n][dur - 1 - dt])


def find_bound(model_cons: Callable[[ModelConfig, float], MySolver],
               cfg: ModelConfig, search: BinarySearch, timeout: float):
    while True:
        thresh = search.next_pt()
        if thresh is None:
            break
        s = model_cons(cfg, thresh)

        print(f"Testing threshold = {thresh}")
        qres = cache.run_query(s, cfg, timeout=timeout)

        print(qres.satisfiable)
        search.register_pt(thresh, sat_to_val(qres.satisfiable))
    return search.get_bounds()

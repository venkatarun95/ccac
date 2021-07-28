from fractions import Fraction
from typing import Dict, Union
import z3

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
    for dt in range(dur):
        for n in range(c.N):
            a, b = dur - 1 - dt, c.T - 1 - dt

            s.add(v.c_f[n][b] == v.c_f[n][a])
            s.add(v.r_f[n][b] == v.r_f[n][a])

            # if dt > 0:
            #     continue
            s.add(v.A_f[n][b] - v.L_f[n][b] - v.S_f[n][b] == v.A_f[n][a] -
                  v.L_f[n][a] - v.S_f[n][a])
            s.add(v.L_f[n][b] - v.Ld_f[n][b] == v.L_f[n][a] - v.Ld_f[n][a])

        s.add(v.A[b] - v.L[b] - (c.C * b - v.W[b]) == v.A[a] - v.L[a] -
              (a - v.W[a]))

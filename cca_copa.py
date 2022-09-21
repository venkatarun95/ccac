from z3 import And, If, Implies, Not, Or

from config import ModelConfig
from pyz3_utils import MySolver
from variables import Variables


def cca_copa(c: ModelConfig, s: MySolver, v: Variables):
    for n in range(c.N):
        for t in range(c.T):
            # Basic constraints
            s.add(v.c_f[n][t] > 0)
            s.add(v.r_f[n][t] == v.c_f[n][t] / c.R)

            if t - c.R - c.D < 0:
                continue

            incr_alloweds, decr_alloweds = [], []
            for dt in range(t+1):
                # Whether we are allowd to increase/decrease
                incr_allowed = s.Bool("incr_allowed_%d,%d,%d" % (n, t, dt))
                decr_allowed = s.Bool("decr_allowed_%d,%d,%d" % (n, t, dt))
                # Warning: Adversary here is too powerful if D > 1. Add
                # a constraint for every point between t-1 and t-1-D
                assert(c.D == 1)
                s.add(incr_allowed
                      == And(
                          v.qdel[t-c.R][dt],
                          v.S[t-c.R] > v.S[t-c.R-1],
                          v.c_f[n][t-1] * max(0, dt-1)
                          <= v.alpha*(c.R+max(0, dt-1))))
                s.add(decr_allowed
                      == And(
                          v.qdel[t-c.R-c.D][dt],
                          v.S[t-c.R] > v.S[t-c.R-1],
                          v.c_f[n][t-1] * dt >= v.alpha * (c.R + dt)))
                incr_alloweds.append(incr_allowed)
                decr_alloweds.append(decr_allowed)
            # If inp is high at the beginning, qdel can be arbitrarily
            # large
            decr_alloweds.append(v.S[t-c.R] < v.A[0] - v.L[0])

            incr_allowed = Or(*incr_alloweds)
            decr_allowed = Or(*decr_alloweds)

            # Either increase or decrease cwnd
            incr = s.Bool("incr_%d,%d" % (n, t))
            decr = s.Bool("decr_%d,%d" % (n, t))
            s.add(Or(
                And(incr, Not(decr)),
                And(Not(incr), decr)))
            s.add(Implies(incr, incr_allowed))
            s.add(Implies(decr, decr_allowed))
            s.add(Implies(incr, v.c_f[n][t] == v.c_f[n][t-1]+v.alpha/c.R))
            sub = v.c_f[n][t-1] - v.alpha / c.R
            s.add(Implies(decr, v.c_f[n][t]
                          == If(sub < v.alpha, v.alpha, sub)))

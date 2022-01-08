''' A convergent CCA that we hope is starvation-free '''

import math
from z3 import And, Implies, Not, Or

from config import ModelConfig
from my_solver import MySolver
from variables import Variables


class ConvVariables:
    def __init__(self, c: ModelConfig, s: MySolver):
        self.max_rate = s.Real("conv_max_rate")


def cca_conv(c: ModelConfig, s: MySolver, v: Variables) -> ConvVariables:
    cv = ConvVariables(c, s)

    for n in range(c.N):
        qdel = []
        for t in range(c.T):
            # Set cwnd to infinity
            s.add(v.c_f[n][t] == 100)

            if t == 0:
                qdel.append([False] * c.T)
                continue

            qdel.append([])

            for dt in range(c.T):
                q = v.qdel[t][dt]
                if dt >= t:
                    q = False
                qdel[-1].append(q)

                if dt == 0:
                    s.add(Implies(q, v.r_f[n][t] == v.r_f[n][t-1] + v.alpha))
                    continue

                thresh = cv.max_rate / (2 ** (dt-1))
                s.add(Implies(And(q, v.r_f[n][t-1] > thresh),
                              v.r_f[n][t] == v.r_f[n][t-1] * 0.9))
                s.add(Implies(And(q, v.r_f[n][t-1] <= thresh),
                              v.r_f[n][t] == v.r_f[n][t-1] + v.alpha))

            thresh = cv.max_rate / (2 ** (t - 1))
            anyq = Or(*[qdel[t][dt] for dt in range(c.T)])
            s.add(Implies(And(Not(anyq), v.r_f[n][t-1] > thresh),
                          v.r_f[n][t] == v.r_f[n][t-1] * 0.9))
            # If r_f <= thresh, then both increase and decrease are allowed
            s.add(Implies(And(Not(anyq), v.r_f[n][t-1] <= thresh),
                          Or(v.r_f[n][t] == v.r_f[n][t-1] + v.alpha,
                             v.r_f[n][t] == v.r_f[n][t-1] * 0.9)))

    return cv


def prove_conv():
    from cache import run_query
    from model import make_solver
    from utils import make_periodic

    c = ModelConfig.default()
    c.cca = "conv"
    c.compose = True
    c.calculate_qdel = True
    c.unsat_core = False
    c.N = 2

    # This can be arbitrarily large (conjecture based on finite proofs), but
    # the larger this is, the larger T needs to be
    max_qdel = c.C * c.R
    t0 = math.ceil(max_qdel / c.C) + 1

    c.T = 10
    s, v = make_solver(c)
    s.add(v.L[0] == 0)
    s.add(v.cv.max_rate > 1)
    # s.add(v.A[0] <= 1)
    s.add(And(v.S[-1] - v.S[t0] < 1.0 * c.C * (c.T - t0 - 2),
              v.r_f[0][-1] + v.r_f[1][-1] <= v.r_f[0][t0] + v.r_f[1][t0]))
    s.add(v.alpha < 1 / 10)
    make_periodic(c, s, v, dur=1)
    print("Checking that if utilization is < 100%, rate will increase")
    qres = run_query(s, c, 600)
    print(qres.satisfiable)
    # from plot import plot_model
    # plot_model(qres.model, c)
    assert(qres.satisfiable == "unsat")

    c.T = 10
    s, v = make_solver(c)
    s.add(v.L[0] == 0)
    s.add(v.cv.max_rate > 1)
    s.add(v.A[0] - v.L[0] - v.S[0] < max_qdel)
    bad = []
    for ratios in [1, 2, 3, 4, 5, 6]:
        bad.append(And(
            v.r_f[0][-1] > ratios * v.r_f[1][-1],
            v.r_f[0][t0] == ratios * v.r_f[1][t0]))
    s.add(Or(*bad))
    s.add(v.alpha < 1 / 10)
    print("Checking whether the CCA can starve")
    qres = run_query(s, c, 60)
    print(qres.satisfiable)
    from plot import plot_model
    plot_model(qres.model, c)
    assert(qres.satisfiable == "unsat")


if __name__ == "__main__":
    prove_conv()

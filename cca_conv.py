''' A convergent CCA that we hope is starvation-free '''

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
                q = Or(And(
                    v.S_f[n][t] != v.S_f[n][t - 1],
                    And(v.A_f[n][t - dt - 1] - v.L_f[n][t - dt - 1] < v.S_f[n][t],
                        v.A_f[n][t - dt] - v.L_f[n][t - dt] >= v.S_f[n][t])),
                       And(v.S_f[n][t] == v.S_f[n][t - 1], qdel[t - 1][dt]))
                qdel[-1].append(q)

                if dt == 0:
                    s.add(Implies(q, v.r_f[n][t] == v.r_f[n][t-1] + v.alpha))
                    continue

                thresh = cv.max_rate / (2 ** (dt-1))
                s.add(Implies(And(q, v.r_f[n][t-1] > thresh),
                              v.r_f[n][t] == v.r_f[n][t-1] - v.alpha))
                s.add(Implies(And(q, v.r_f[n][t-1] <= thresh),
                              v.r_f[n][t] == v.r_f[n][t-1] + v.alpha))

            thresh = cv.max_rate / (2 ** (t - 1))
            anyq = Or(*[qdel[t][dt] for dt in range(c.T)])
            s.add(Implies(And(Not(anyq), v.r_f[n][t-1] > thresh),
                          v.r_f[n][t] == v.r_f[n][t-1] + v.alpha))
            # If r_f <= thresh, then both increase and decrease are allowed
            s.add(Implies(And(Not(anyq), v.r_f[n][t-1] <= thresh),
                          Or(v.r_f[n][t] == v.r_f[n][t-1] + v.alpha,
                             v.r_f[n][t] == v.r_f[n][t-1] - v.alpha)))

    return cv


def prove_conv():
    from cache import run_query
    from model import make_solver

    c = ModelConfig.default()
    c.cca = "conv"
    c.compose = True
    c.calculate_qdel = True
    c.unsat_core = False
    c.N = 2

    c.T = 10
    s, v = make_solver(c)
    s.add(v.L[0] == 0)
    s.add(v.cv.max_rate > 1)
    s.add(And(v.S[-1] - v.S[0] < 0.51 * c.C * (c.T - 2),
              v.r_f[0][-1] + v.r_f[1][-1] <= v.r_f[0][0] + v.r_f[1][0]))
    s.add(v.alpha < 1 / 10)
    print("Checking that if utilization is < 100%, rate will increase")
    qres = run_query(s, c, 60)
    print(qres.satisfiable)
    from plot import plot_model
    plot_model(qres.model, c)
    assert(qres.satisfiable == "unsat")


if __name__ == "__main__":
    prove_conv()

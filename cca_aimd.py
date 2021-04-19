from z3 import And, Implies, Not

from model_utils import ModelConfig, Variables
from my_solver import MySolver


def cca_aimd(c: ModelConfig, s: MySolver, v: Variables):
    # The last send sequence number at which loss was detected
    ll = [[s.Real(f"last_loss_{n},{t}") for t in range(c.T)]
          for n in range(c.N)]
    for n in range(c.N):
        s.add(ll[n][0] == v.S_f[n][0])
        for t in range(c.T):
            if c.pacing:
                s.add(v.r_f[n][t] == v.c_f[n][t] / c.R)
            else:
                s.add(v.r_f[n][t] == c.C * 100)

            if t > 0:
                # We compare last_loss to outs[t-1-R] (and not outs[t-R])
                # because otherwise it is possible to react to the same loss
                # twice
                if t > c.R+1:
                    decrease = And(
                        v.Ld_f[n][t] > v.Ld_f[n][t-1],
                        ll[n][t-1] <= v.S_f[n][t-c.R-1]
                    )
                else:
                    decrease = v.Ld_f[n][t] > v.Ld_f[n][t-1]

                s.add(Implies(
                    decrease,
                    And(ll[n][t] == v.A_f[n][t] - v.L_f[n][t] + v.dupacks,
                        v.c_f[n][t] == v.c_f[n][t-1] / 2)
                ))
                s.add(Implies(
                    Not(decrease),
                    And(ll[n][t] == ll[n][t-1],
                        v.c_f[n][t] == v.c_f[n][t-1] + v.alpha)
                ))

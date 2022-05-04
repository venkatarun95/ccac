''' A simplified version of BBR '''

from z3 import And, If, Implies, Not

from config import ModelConfig
from pyz3_utils import MySolver
from variables import Variables


class BBRSimpleVariables:
    def __init__(self, c: ModelConfig, s: MySolver):
        # State increments every RTT
        self.start_state_f =\
            [s.Int(f"bbr_start_state_{n}") for n in range(c.N)]


def cca_bbr(c: ModelConfig, s: MySolver, v: Variables):
    # The period over which we compute rates
    P = c.R
    # Number of RTTs over which we compute the max_cwnd (=10 in the spec)
    max_R = 4
    # The number of RTTs in the BBR cycle (=8 in the spec)
    cycle = 4
    # The state the flow starts in at t=0
    start_state_f = [s.Int(f"bbr_start_state_{n}") for n in range(c.N)]

    for n in range(c.N):
        s.add(start_state_f[n] >= 0)
        s.add(start_state_f[n] < cycle)
        for t in range(c.R + P, c.T):
            # Compute the max RTT over the last max_R RTTs
            max_rate = [s.Real(f"max_rate_{n},{t},{dt}")
                        for dt in range(min(t-c.R-P+1, max_R))]
            s.add(max_rate[0] == (v.S_f[n][t-c.R] - v.S_f[n][t-c.R-P]) / P)
            for dt in range(1, len(max_rate)):
                rate = (v.S_f[n][t-dt-c.R] - v.S_f[n][t-dt-c.R-P]) / P
                s.add(max_rate[dt] == If(rate > max_rate[dt-1],
                                         rate, max_rate[dt-1]))

            # Convenience variable for plotting
            s.add(s.Real(f"max_rate_{n},{t}") == max_rate[-1])

            s.add(v.c_f[n][t] == 2 * max_rate[-1] * P)
            s_0 = (start_state_f[n] == (0 - t / c.R) % cycle)
            s_1 = (start_state_f[n] == (1 - t / c.R) % cycle)
            s.add(Implies(s_0,
                          v.r_f[n][t] == 1.25 * max_rate[-1]))
            s.add(Implies(s_1,
                          v.r_f[n][t] == 0.8 * max_rate[-1]))
            s.add(Implies(And(Not(s_0), Not(s_1)),
                          v.r_f[n][t] == 1 * max_rate[-1]))

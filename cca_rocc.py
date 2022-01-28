from z3 import And, If, Implies, Not

from config import ModelConfig
from my_solver import MySolver
from variables import Variables


class RoCCVariables:
    def __init__(self, c: ModelConfig, s: MySolver):
        # Not quite a variable, but it is good to have an officially defined
        # `dur` for each cca
        self.dur = 2*c.R + 2*c.D

        # Current estimate of the min RTT. It is an integer that says that min
        # RTT is between c.R+minrtt_f and c.R+minrtt_f (in reality this is
        # really min queuing delay)
        self.minrtt_f = [[s.Int(f"rocc_min_rtt_{n},{t}") for t in range(c.T)]
                         for n in range(c.N)]
        # Queuing delay experienced at integer time t (the real algorithm will
        # measure the min delay over all packets, but if this "inferior"
        # algorithm works, then so does the perfect algorithm)
        self.qdel = [s.Int(f"rocc_qdel_{t}") for t in range(c.T)]
        # The timestep at which we do an RTT probe. Can be chosen
        # non-deterministically. It can also be statically set to -1 to create
        # traces where an RTT probe cannot happen
        self.probe = [s.Int(f"rocc_probe_time_{n}") for n in range(c.N)]


def cca_rocc(c: ModelConfig, s: MySolver, v: Variables) -> RoCCVariables:
    cv = RoCCVariables(c, s)
    # Length of time for which we take history in addition to queuing delay
    hist = c.D + 2*c.R

    for t in range(c.T):
        # qdel is always non-negative (make the solver's job easier)
        s.add(cv.qdel[t] >= 0)
        for n in range(c.N):
            s.add(cv.minrtt_f[n][t] >= 0)
            s.add(v.r_f[n][t] == 100 * c.C)

    for n in range(c.N):
        # Bound probe time to make the solver's job easier
        s.add(cv.probe[n] >= -1)
        s.add(cv.probe[n] < c.T)

        for t in range(1, c.T):
            # Update minrtt_f
            s.add(cv.minrtt_f[n][t] ==
                  If(cv.minrtt_f[n][t-1] < cv.qdel[t],
                     cv.minrtt_f[n][t-1], cv.qdel[t]))

            # Are we currently probing minrtt_f?
            probing = And(t >= cv.probe[n],
                          t <= cv.probe[n] + cv.minrtt_f[n][t] + hist + 1 + c.D,
                          cv.probe[n] >= 0)
            s.add(Implies(probing,
                          v.c_f[n][t] == 1e-5))

            for dt in range(0, c.T):
                if t-2*c.R-2*c.D-dt-1 < 0:
                    continue
                # Set the cwnd based on minrtt_f + D. Note, the actual min rtt
                # in the continuous may be anything in the range [minrtt_f,
                # minrtt_f+1]
                s.add(Implies(And(cv.minrtt_f[n][t] == dt, Not(probing)),
                              And(v.c_f[n][t] >=
                                  v.S[t-c.R]-v.S[t-c.R-hist-dt]+v.alpha,
                                  v.c_f[n][t] <=
                                  v.S[t-c.R]-v.S[t-c.R-hist-dt-1]+v.alpha)))

            # If the min rtt is larger than anything we have history for,
            # cwnd has only a lower bound
            s.add(Implies(And(cv.minrtt_f[n][t]+c.R+hist >= t,
                              Not(probing)),
                          v.c_f[n][t] >= v.S[t-c.R] - v.S[0] + v.alpha))

    for t in range(c.R, c.T):
        # Calculate the current queuing delay
        for dt in range(c.T):
            s.add(Implies(v.qdel[t-c.R][dt], cv.qdel[t] == dt))
        # If queuing delay is so large it extends past t=0, let z3 pick it
        # non-deterministically
        s.add(Implies(v.S[t-c.R] < v.A[0] - v.L[0], cv.qdel[t] > t-c.R))

    return cv

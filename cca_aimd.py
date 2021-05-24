from z3 import And, Implies, Not, Or

from config import ModelConfig
from my_solver import MySolver
from variables import Variables


class AIMDVariables:
    def __init__(self, c: ModelConfig, s: MySolver):
        # Whether or not cwnd can increase at this point
        self.incr_f = [[s.Bool(f"aimd_incr_{n},{t}") for t in range(c.T)]
                       for n in range(c.N)]


def can_incr(
        c: ModelConfig,
        s: MySolver,
        v: Variables,
        cv: AIMDVariables):
    # Always increase
    if c.aimd_incr_irrespective:
        for n in range(c.N):
            for t in range(c.T):
                s.add(cv.incr_f[n][t])
        return

    for n in range(c.N):
        for t in range(1, c.T):
            # Increase cwnd only if we have got enough acks
            incr = []
            for dt in range(1, t):
                # Note, it is possible that v.c_f[n][t-dt] == v.c_f[n][t]
                # even though the cwnd changed in between. Hence this SMT
                # encoding is more relaxed than reality, which is per our
                # policy of capturing a super-set of behaviors. We could of
                # course add appropriate checks, but that is
                # unnecessary. This is simpler and possibly more efficient.
                incr.append(And(
                    And([v.c_f[n][t-ddt] == v.c_f[n][t]
                         for ddt in range(1, dt+1)]),
                    v.c_f[n][t-dt-1] != v.c_f[n][t-dt],
                    v.S_f[n][t] - v.S_f[n][t-dt] >= v.c_f[n][t]))
            incr.append(And(
                And([v.c_f[n][t-ddt] == v.c_f[n][t]
                     for ddt in range(1, t+1)]),
                v.S_f[n][t] - v.S_f[n][0] >= v.c_f[n][t]))
            incr.append(And(
                v.S_f[n][t] - v.S_f[n][t-1] >= v.c_f[n][t]))
            s.add(cv.incr_f[n][t] == Or(*incr))


def cca_aimd(c: ModelConfig, s: MySolver, v: Variables) -> AIMDVariables:
    cv = AIMDVariables(c, s)
    can_incr(c, s, v, cv)

    # The last send sequence number at which loss was detected
    ll = [[s.Real(f"last_loss_{n},{t}") for t in range(c.T)]
          for n in range(c.N)]
    s.add(v.dupacks == 3 * v.alpha)
    for n in range(c.N):
        # TODO: make this non-deterministic?
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
                    And(decrease, Not(v.timeout_f[n][t])),
                    And(ll[n][t] == v.A_f[n][t] - v.L_f[n][t] + v.dupacks,
                        v.c_f[n][t] == v.c_f[n][t-1] / 2)
                ))
                s.add(Implies(
                    And(Not(decrease), Not(v.timeout_f[n][t])),
                    ll[n][t] == ll[n][t-1]))

                s.add(Implies(
                    And(Not(decrease), Not(v.timeout_f[n][t]),
                        cv.incr_f[n][t-1]),
                    v.c_f[n][t] == v.c_f[n][t-1] + v.alpha))
                s.add(Implies(
                    And(Not(decrease), Not(v.timeout_f[n][t]),
                        Not(cv.incr_f[n][t-1])),
                    v.c_f[n][t] == v.c_f[n][t-1]))

                # Timeout
                s.add(Implies(v.timeout_f[n][t],
                              And(v.c_f[n][t] == v.alpha,
                                  ll[n][t] == v.A_f[n][t] - v.L_f[n][t]
                                  + v.dupacks)))
    return cv

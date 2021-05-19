from z3 import And, Implies, Not, Or

from config import ModelConfig
from my_solver import MySolver
from variables import Variables


def cca_aimd(c: ModelConfig, s: MySolver, v: Variables):
    # The last send sequence number at which loss was detected
    ll = [[s.Real(f"last_loss_{n},{t}") for t in range(c.T)]
          for n in range(c.N)]
    s.add(v.dupacks == 3 * v.alpha)
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
                    And(decrease, Not(v.timeout_f[n][t])),
                    And(ll[n][t] == v.A_f[n][t] - v.L_f[n][t] + v.dupacks,
                        v.c_f[n][t] == v.c_f[n][t-1] / 2)
                ))
                s.add(Implies(
                    And(Not(decrease), Not(v.timeout_f[n][t])),
                    ll[n][t] == ll[n][t-1]))

                # Increase cwnd only if we have got enough acks
                incr = []
                for dt in range(1, t + 1):
                    if dt == t:
                        incr.append(And(
                            v.c_f[n][t-dt] == v.c_f[n][t],
                            v.S_f[n][t] - v.S_f[n][t-dt] >= v.c_f[n][t-dt]))
                        continue

                    # Note, it is possible that v.c_f[n][t-dt] == v.c_f[n][t]
                    # even though the cwnd changed in between. Hence this SMT
                    # encoding is more relaxed than reality, which is per our
                    # policy of capturing a super-set of behaviors. We could of
                    # course add appropriate checks, but that is
                    # unnecessary. This is simpler and possibly more efficient.
                    incr.append(And(
                        v.c_f[n][t-dt] == v.c_f[n][t],
                        v.c_f[n][t-dt-1] != v.c_f[n][t-dt],
                        v.S_f[n][t] - v.S_f[n][t-dt] >= v.c_f[n][t-dt]))
                incr = Or(*incr)

                # Ignore above and always increase
                if c.aimd_incr_irrespective:
                    incr = True

                s.add(Implies(
                    And(Not(decrease), Not(v.timeout_f[n][t]), incr),
                    v.c_f[n][t] == v.c_f[n][t-1] + v.alpha))
                s.add(Implies(
                    And(Not(decrease), Not(v.timeout_f[n][t]), Not(incr)),
                    v.c_f[n][t] == v.c_f[n][t-1]))

                # Timeout
                s.add(Implies(v.timeout_f[n][t],
                              v.c_f[n][t] == v.alpha))

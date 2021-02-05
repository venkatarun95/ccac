from z3 import Bool, Real, Int, Sum, Implies, Not, And, Or, If

from model_utils import ModelConfig
from my_solver import MySolver


class Variables:
    ''' Some variables that everybody uses '''

    def __init__(self, c: ModelConfig, s: MySolver):
        T = c.T

        # Af denotes per-flow A
        self.A_f = [[s.Real(f"arrival_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        self.A = [s.Real(f"tot_arrival_{t}") for t in range(T)]
        self.c_f = [[s.Real(f"cwnd_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        self.r_f = [[s.Real(f"rate_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        # Total number of losses detected
        self.Ld_f = [[s.Real(f"loss_detected_{n},{t}")
                      for t in range(T)]
                     for n in range(c.N)]
        self.S_f = [[s.Real(f"service_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        self.S = [s.Real(f"tot_service_{t}") for t in range(T)]
        self.L_f = [[s.Real(f"losts_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        self.L = [s.Real(f"tot_lost_{t}") for t in range(T)]
        self.W = [s.Real(f"wasted_{t}") for t in range(T)]

        if not c.compose:
            self.epsilon = s.Real("epsilon")

        if c.dupacks is None:
            self.dupacks = s.Real('dupacks')
            s.add(self.dupacks >= 0)
        else:
            self.dupacks = c.dupacks

        if c.alpha is None:
            self.alpha = s.Real('alpha')
            s.add(self.alpha > 0)
        else:
            self.alpha = c.alpha


def monotone(c: ModelConfig, s: MySolver, v: Variables):
    for t in range(1, c.T):
        for n in range(c.N):
            s.add(v.A_f[n][t] >= v.A_f[n][t-1])
            s.add(v.c_f[n][t] >= v.c_f[n][t-1])
            s.add(v.r_f[n][t] >= v.r_f[n][t-1])
            s.add(v.Ld_f[n][t] >= v.Ld_f[n][t-1])
            s.add(v.S_f[n][t] >= v.S_f[n][t-1])
            s.add(v.L_f[n][t] >= v.L_f[n][t-1])

            s.add(v.A_f[n][t] - v.L_f[n][t] >= v.A_f[n][t-1] - v.L_f[n][t-1])
        s.add(v.W[t] >= v.W[t-1])


def initial(c: ModelConfig, s: MySolver, v: Variables):
    for n in range(c.N):
        # Making these positive actually matters. What the hell is negative
        # rate or loss?
        s.add(v.c_f[n][0] > 0)
        s.add(v.r_f[n][0] > 0)
        s.add(v.L_f[n][0] >= 0)
        s.add(v.Ld_f[n][0] >= 0)

        # These are invariant to y-shift. However, it does make the results
        # easier to interpret if they start from 0
        s.add(v.S_f[n][0] == 0)


def relate_tot(c: ModelConfig, s: MySolver, v: Variables):
    ''' Relate total values to per-flow values '''
    for t in range(c.T):
        s.add(v.A[t] == sum([v.A_f[n][t] for n in range(c.N)]))
        s.add(v.L[t] == sum([v.L_f[n][t] for n in range(c.N)]))
        s.add(v.S[t] == sum([v.S_f[n][t] for n in range(c.N)]))


def network(c: ModelConfig, s: MySolver, v: Variables):
    for t in range(c.T):
        s.add(v.S[t] <= v.A[t] - v.L[t])

        s.add(v.S[t] <= c.C*t - v.W[t])
        if t >= c.D:
            s.add(c.C*(t-c.D) - v.W[t-c.D] <= v.S[t])
        else:
            # The constraint is the most slack when black line is steepest. So
            # we'll say there was no wastage when t < 0
            s.add(c.C*(t-c.D) - v.W[0] <= v.S[t])

        if c.compose:
            if t > 0:
                s.add(Implies(
                    v.W[t] > v.W[t-1],
                    v.A[t] - v.L[t] <= c.C * t - v.W[t]
                ))
        else:
            if t > 0:
                s.add(Implies(
                    v.W[t] > v.W[t-1],
                    v.A[t] - v.L[t] <= v.S[t] + v.epsilon
                ))

        if c.buf_min is not None:
            if t > 0:
                r = sum([v.r_f[n][t] for n in range(c.N)])
                s.add(Implies(
                    v.L[t] > v.L[t-1],
                    v.A[t] - v.L[t] >= c.C*t - v.W[t] + c.buf_min
                    # And(v.A[t] - v.L[t] >= c.C*(t-1) - v.W[t-1] + c.buf_min,
                    #     r > c.C,
                    #     c.C*(t-1) - v.W[t-1] + c.buf_min
                    #     - (v.A[t-1] - v.L[t-1]) < r - c.C
                    #     )
                ))
        else:
            s.add(v.L[t] == v.L[0])

        # Enforce buf_max if given
        if c.buf_max is not None:
            s.add(v.A[t] - v.L[t] <= c.C*t - v.W[t] + c.buf_max)


def loss_detected(c: ModelConfig, s: MySolver, v: Variables):
    for n in range(c.N):
        for t in range(c.T):
            for dt in range(c.T):
                if t - c.R - dt < 0:
                    continue
                detectable = v.A_f[n][t-c.R-dt] - v.L_f[n][t-c.R-dt]\
                    + v. dupacks <= v.S_f[n][t-c.R]

                s.add(Implies(
                    detectable,
                    v.Ld_f[n][t] >= v.L_f[n][t-c.R-dt]
                ))
                s.add(Implies(
                    Not(detectable),
                    v.Ld_f[n][t] <= v.L_f[n][t-c.R-dt]
                ))
            s.add(v.Ld_f[n][t] <= v.L_f[n][t-c.R])


def epsilon_alpha(c: ModelConfig, s: MySolver, v: Variables):
    if not c.compose:
        if c.epsilon == "zero":
            s.add(v.epsilon == 0)
        elif c.epsilon == "lt_alpha":
            s.add(v.epsilon < v.alpha)
        elif c.epsilon == "lt_half_alpha":
            s.add(v.epsilon < v.alpha * 0.5)
        elif c.epsilon == "gt_alpha":
            s.add(v.epsilon > v.alpha)
        else:
            assert(False)


def cwnd_rate_arrival(c: ModelConfig, s: MySolver, v: Variables):
    for n in range(c.N):
        for t in range(c.T):
            if t >= c.R:
                assert(c.R >= 1)
                # Arrival due to cwnd
                A_w = v.S_f[n][t-c.R] + v.Ld_f[n][t] + v.c_f[n][t]
                A_w = If(A_w >= v.A_f[n][t-1], A_w, v.A_f[n][t-1])
                # Arrival due to rate
                A_r = v.A_f[n][t-1] + v.r_f[n][t]
                # Net arrival
                s.add(v.A_f[n][t] == If(A_w >= A_r, A_r, A_w))
            else:
                # NOTE: This is different in this new version. Here anything can
                # happen. No restrictions
                pass


def cca_const(c: ModelConfig, s: MySolver, v: Variables):
    for n in range(c.N):
        for t in range(c.T):
            s.add(v.c_f[n][t] == v.alpha)
            if c.pacing:
                s.add(v.r_f[n][t] == v.alpha / c.R)
            else:
                s.add(v.r_f[n][t] >= c.C * 100)


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
                s.add(v.r_f[n][t] >= c.C * 100)

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


def make_solver(c: ModelConfig) -> (MySolver, Variables):
    s = MySolver()
    v = Variables(c, s)

    monotone(c, s, v)
    initial(c, s, v)
    relate_tot(c, s, v)
    network(c, s, v)
    loss_detected(c, s, v)
    epsilon_alpha(c, s, v)
    cwnd_rate_arrival(c, s, v)

    if c.cca == "const":
        cca_const(c, s, v)
    if c.cca == "aimd":
        cca_aimd(c, s, v)
    else:
        assert(False)

    return (s, v)

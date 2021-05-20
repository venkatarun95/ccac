from z3 import And, Sum, Implies, Or, Not, If

from cca_aimd import cca_aimd
from cca_bbr import cca_bbr
from cca_copa import cca_copa
from config import ModelConfig
from my_solver import MySolver
from variables import Variables


def monotone(c: ModelConfig, s: MySolver, v: Variables):
    for t in range(1, c.T):
        for n in range(c.N):
            s.add(v.A_f[n][t] >= v.A_f[n][t-1])
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
        s.add(v.A[t] == Sum([v.A_f[n][t] for n in range(c.N)]))
        s.add(v.L[t] == Sum([v.L_f[n][t] for n in range(c.N)]))
        s.add(v.S[t] == Sum([v.S_f[n][t] for n in range(c.N)]))


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
                    v.A[t] - v.L[t] >= c.C*(t-1) - v.W[t-1] + c.buf_min
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
                # Loss is detectable through dupacks
                detectable = v.A_f[n][t-c.R-dt] - v.L_f[n][t-c.R-dt]\
                    + v.dupacks <= v.S_f[n][t-c.R]

                s.add(Implies(
                    And(Not(v.timeout_f[n][t]), detectable),
                    v.Ld_f[n][t] >= v.L_f[n][t-c.R-dt]
                ))
                s.add(Implies(
                    And(Not(v.timeout_f[n][t]), Not(detectable)),
                    v.Ld_f[n][t] <= v.L_f[n][t-c.R-dt]
                ))

            # We implement an RTO scheme that magically triggers when S(t) ==
            # A(t) - L(t). While this is not implementable in reality, it is
            # still realistic. First, if a CCAC version of the CCA times out,
            # then a real implementation will also timeout. The timeout may
            # occur a different duration than in the real world. The user
            # should be mindful of this and not take the timeout duration
            # literally. Nevertheless, this difference has no bearing on
            # subsequent behavior.

            # This is also the only *legitimate* case where we want our CCA to
            # timeout. A CCAC adversary can cause a real implementation to
            # timeout by keeping RTTVAR=0 and then suddenly delaying packets by
            # D seconds. This counter-example is uninteresting. Hence
            # we usually want to avoid getting such counter-examples in
            # CCAC. Our timeout strategy sidesteps this issue.

            if t < c.R:
                s.add(v.timeout_f[n][t] == False)
            else:
                s.add(v.timeout_f[n][t] == And(
                      v.S_f[n][t-c.R] < v.A_f[n][t-1],  # oustanding bytes
                      v.S_f[n][t-c.R] == v.A_f[n][t-c.R] - v.L_f[n][t-c.R]))
            s.add(Implies(v.timeout_f[n][t],
                          v.Ld_f[n][t] == v.L_f[n][t]))

            s.add(v.Ld_f[n][t] <= v.L_f[n][t-c.R])


def calculate_qdel(c: ModelConfig, s: MySolver, v: Variables):
    # Figure out the time when the bytes being output at time t were
    # first input
    for t in range(c.T):
        for dt in range(c.T):
            if dt > t:
                s.add(Not(v.qdel[t][dt]))
                continue
            s.add(v.qdel[t][dt] == Or(
                And(
                    v.S[t] != v.S[t-1],
                    And(v.A[t - dt - 1] - v.L[t - dt - 1]
                        < v.S[t],
                        v.A[t - dt] - v.L[t - dt] >= v.S[t])
                ),
                And(
                    v.S[t] == v.S[t-1],
                    v.qdel[t][dt] == v.qdel[t-1][dt])))

        # We don't know what happened at t < 0, so we'll let the solver pick
        # non-deterministically
        s.add(Implies(
            And(v.S[t] != v.S[t-1],
                v.A[0] - v.L[0] < v.S[t-1]),
            Not(v.qdel[t][t-1])))


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
                # NOTE: This is different in this new version. Here anything
                # can happen. No restrictions
                pass


def min_send_quantum(c: ModelConfig, s: MySolver, v: Variables):
    '''Every timestep, the sender must send either 0 bytes or > 1MSS bytes.
    While it is not recommended that we use these constraints everywhere, in
    AIMD it is possible to not trigger loss detection by sending tiny packets
    which sum up to less than beta. However this is not possible in the real
    world and should be ruled out.
    '''

    for n in range(c.N):
        for t in range(1, c.T):
            s.add(Or(
                v.S_f[n][t-1] == v.S_f[n][t],
                v.S_f[n][t-1] + v.alpha <= v.S_f[n][t]))


def cca_const(c: ModelConfig, s: MySolver, v: Variables):
    for n in range(c.N):
        for t in range(c.T):
            s.add(v.c_f[n][t] == v.alpha)
            if c.pacing:
                s.add(v.r_f[n][t] == v.alpha / c.R)
            else:
                s.add(v.r_f[n][t] >= c.C * 100)


def make_solver(c: ModelConfig) -> (MySolver, Variables):
    s = MySolver()
    v = Variables(c, s)

    if c.unsat_core:
        s.set(unsat_core=True)

    monotone(c, s, v)
    initial(c, s, v)
    relate_tot(c, s, v)
    network(c, s, v)
    loss_detected(c, s, v)
    epsilon_alpha(c, s, v)
    if c.calculate_qdel:
        calculate_qdel(c, s, v)
    cwnd_rate_arrival(c, s, v)

    if c.cca == "const":
        cca_const(c, s, v)
    elif c.cca == "aimd":
        cca_aimd(c, s, v)
    elif c.cca == "bbr":
        cca_bbr(c, s, v)
    elif c.cca == "copa":
        cca_copa(c, s, v)
    else:
        assert(False)

    return (s, v)


if __name__ == "__main__":
    from clean_output import simplify_solution
    from utils import model_to_dict
    from plot import plot_model

    c = ModelConfig(
        N=1,
        D=1,
        R=1,
        T=10,
        C=1,
        buf_min=None,
        buf_max=None,
        dupacks=None,
        cca="copa",
        compose=True,
        alpha=None,
        pacing=True,
        epsilon="zero",
        unsat_core=True,
        simplify=False
    )
    s, v = make_solver(c)

    s.add(v.A[0] == 0)
    s.add(v.L[0] == 0)
    s.add(v.S[c.T-1] - v.S[0] < 0.1 * c.C * (c.T - 1))

    sat = s.check()
    print(sat)
    if str(sat) == "sat":
        m = model_to_dict(s.model())
        if False:
            m = simplify_solution(c, m, s.assertions())
        plot_model(m, c)
    elif c.unsat_core:
        print(s.unsat_core())

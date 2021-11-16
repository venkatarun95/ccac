from z3 import And, Not, Or

from .cache import run_query
from .config import ModelConfig
from .model import make_solver
from .plot import plot_model
from .utils import make_periodic


def bbr_low_util(timeout=10):
    '''Finds an example trace where BBR has < 10% utilization. It can be made
    arbitrarily small, since BBR can get arbitrarily small throughput in our
    model.

    You can simplify the solution somewhat by setting simplify=True, but that
    can cause small numerical errors which makes the solution inconsistent. See
    README for details.

    '''
    c = ModelConfig.default()
    c.compose = True
    c.cca = "bbr"
    # Simplification isn't necessary, but makes the output a bit easier to
    # understand
    c.simplify = False
    s, v = make_solver(c)
    # Consider the no loss case for simplicity
    s.add(v.L[0] == 0)
    # Ask for < 10% utilization. Can be made arbitrarily small
    s.add(v.S[-1] - v.S[0] < 0.1 * c.C * c.T)
    make_periodic(c, s, v, 2 * c.R)
    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c)


def bbr_test(timeout=10):
    c = ModelConfig.default()
    c.compose = True
    c.cca = "bbr"
    c.buf_min = 0.5
    c.buf_max = 0.5
    c.T = 8
    # Simplification isn't necessary, but makes the output a bit easier to
    # understand
    c.simplify = False
    s, v = make_solver(c)
    # Consider the no loss case for simplicity
    s.add(v.L[0] == 0)
    # Ask for < 10% utilization. Can be made arbitrarily small
    #s.add(v.S[-1] - v.S[0] < 0.1 * c.C * c.T)
    s.add(v.L[-1] - v.L[0] >= 0.5 * (v.S[-1] - v.S[0]))
    s.add(v.A[0] == 0)
    s.add(v.r_f[0][0] < c.C)
    s.add(v.r_f[0][1] < c.C)
    s.add(v.r_f[0][2] < c.C)
    make_periodic(c, s, v, 2 * c.R)
    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c)


def copa_low_util_nocompose(timeout=10):
    copa_low_util(timeout, compose=False)


def copa_low_util(timeout=10, compose=True):
    '''Finds an example where Copa gets < 10% utilization. This is with the default
    model that composes. If c.compose = False, then CCAC cannot find an example
    where utilization is below 50%. copa_proofs.py proves bounds on Copa's
    performance in the non-composing model. When c.compose = True, Copa can get
    arbitrarily low throughput

    '''
    c = ModelConfig.default()
    c.unsat_core = True
    c.compose = compose
    c.cca = "copa"
    c.simplify = False
    c.calculate_qdel = True
    # c.S0 = -1000
    # c.L0 = 1000
    # c.W0 = -1000
    c.C = 3
    c.T = 5
    c.C0 = 1000
    s, v = make_solver(c)
    # Consider the no loss case for simplicity
    s.add(v.L[0] == v.L[-1])
    # 10% utilization. Can be made arbitrarily small
    s.add(v.S[-1] - v.S[0] < 0.1 * c.C * c.T)
    make_periodic(c, s, v, c.R + c.D)

    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        assert(qres.model is not None)
        plot_model(qres.model, c)


def copa_ack_burst(timeout=10, compose=False):
    '''Finds an example where with Copa CCA
    under ack burst in the no composition model.

    Purpose:
    This is used to generate a trace where Copa experiences
    ACK burst. Here box composition is not allowed.
    We then use this as an acceptable trace in incal.
    We also use the Copa low utilization trace as an unacceptable trace.
    The hope is that incal throws a constraint that disables model composition
    to allow this trace and deny low util trace.
    '''
    c = ModelConfig.default()
    c.compose = compose
    c.cca = "copa"
    c.simplify = False
    c.calculate_qdel = True
    c.T = 10
    s, v = make_solver(c)
    # Consider the no loss case for simplicity
    s.add(v.L[0] == 0)
    # 10% utilization. Can be made arbitrarily small
    s.add(v.S[-1] - v.S[0] >= 1)
    make_periodic(c, s, v, c.R + c.D)

    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c)


def aimd_premature_loss(timeout=60):
    '''Finds a case where AIMD bursts 2 BDP packets where buffer size = 2 BDP and
    cwnd <= 2 BDP. Here 1BDP is due to an ack burst and another BDP is because
    AIMD just detected 1BDP of loss. This analysis created the example
    discussed in section 6 of the paper. As a result, cwnd can reduce to 1 BDP
    even when buffer size is 2BDP, whereas in a fluid model it never goes below
    1.5 BDP.

    '''
    c = ModelConfig.default()
    c.cca = "aimd"
    c.R = 2
    c.buf_min = 5
    c.buf_max = 5
    c.simplify = False
    c.T = 10

    s, v = make_solver(c)

    # Start with zero loss and zero queue, so CCAC is forced to generate an
    # example trace *from scratch* showing how bad behavior can happen in a
    # network that was perfectly normal to begin with
    s.add(v.L[0] == 0)
    # s.add(v.W[0] >= 0)
    # Restrict alpha to small values, otherwise CCAC can output obvious and
    # uninteresting behavior
    s.add(v.alpha <= 0.1 * c.C * c.R)

    # Steady state conditions (added by 108anup)
    s.add(v.c_f[0][0] <= c.buf_max)
    s.add(v.L_f[0][0] == 0)

    # Restrict ACK burst to 1 unit (0.5 BDP).
    for t in range(0, c.T - 1):
        s.add(v.S[t+1] - v.S[t] <= 1)

    # Does there exist a time where loss happened while cwnd <= 1?
    conds = []
    for t in range(2, c.T - 1):
        # Premature loss only when queue is adversarial (allows drops as soon as q(t) > beta).
        conds.append(
            And(
                v.c_f[0][t] > c.buf_max,
                v.c_f[0][t] < 0.1 + c.buf_max,
                v.L_f[0][t + 1] > v.L_f[0][t],
                ))

        # 108anup: why loss detected? there is a bound to be a delay in loss detected.
        # Original condition in CCAC
        # conds.append(
        #     And(
        #         v.c_f[0][t] <= 2,
        #         v.L_f[0][t + 1] > v.L_f[0][t],
        #         v.Ld_f[0][t + 1] - v.Ld_f[0][t] >=
        #         1,  # Burst due to loss detection
        #         v.S[t + 1 - c.R] - v.S[t - c.R] >=
        #         c.C + 1,  # Burst of BDP acks
        #         v.A[t + 1] >=
        #         v.A[t] + 2 - 1e-3  # Sum of the two bursts (- epsilon)
        #     ))

        # (108anup) Condition to check as described in words in the paper
        # conds.append(
        #     And(
        #         v.c_f[0][t] <= 2 + 1e-6,
        #         v.L_f[0][t + 1] - v.L_f[0][t] >=
        #         1
        #     ))

        # (108anup) Same loss detected twice (change loop bound to C.T - 2)
        # conds.append(
        #     And(
        #         v.c_f[0][t] <= 2 + 1e-6,
        #         v.Ld_f[0][t + 2] - v.Ld_f[0][t + 1] >=
        #         1
        #     ))

    # (108anup) Remove too high cwnd at t0
    # s.add(v.c_f[0][0] <= 4)

    # We don't want an example with timeouts
    for t in range(c.T):
        s.add(Not(v.timeout_f[0][t]))

    # (108anup) Require a timeout
    # s.add(v.timeout_f[0][3])

    import pprint
    pprint.pprint(Or(*conds))
    s.add(Or(*conds))

    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c)


if __name__ == "__main__":
    import sys

    funcs = {
        "aimd_premature_loss": aimd_premature_loss,
        "bbr_low_util": bbr_low_util,
        "copa_low_util": copa_low_util,
        "copa_low_util_nocompose": copa_low_util_nocompose,
        "copa_ack_burst": copa_ack_burst
    }
    usage = f"Usage: python3 example_queries.py <{'|'.join(funcs.keys())}>"

    if len(sys.argv) != 2:
        print("Expected exactly one command")
        print(usage)
        exit(1)
    cmd = sys.argv[1]
    if cmd in funcs:
        funcs[cmd]()
    else:
        print("Command not recognized")
        print(usage)

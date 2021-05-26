from z3 import And, Not, Or

from cache import run_query
from config import ModelConfig
from model import make_solver
from my_solver import MySolver
from plot import plot_model
from variables import Variables


def make_periodic(c: ModelConfig, s: MySolver, v: Variables, dur: int):
    '''A utility function that makes the solution periodic. A periodic solution
    means the same pattern can repeat indefinitely. If we don't make it
    periodic, CCAC might output examples where the cwnd is very low to begin
    with, and *therefore* the utilization is low. If we are looking for
    examples that hold in steady-state, then making things periodic is an easy
    way to do that.

    `dur` is the number of timesteps for which the cwnd of our CCA is
    arbitrary. They are arbitrary to ensure the solver can pick any initial
    conditions. For AIMD dur=1, for Copa dur=c.R+c.D, for BBR dur=2*c.R

    '''
    for n in range(c.N):
        s.add(v.A_f[n][-1] - v.L_f[n][-1] - v.S_f[n][-1]
              == v.A_f[n][0] - v.L_f[n][0] - v.S_f[n][0])
        s.add(v.L_f[n][-1] - v.Ld_f[n][-1] == v.L_f[n][0] - v.Ld_f[n][0])
        s.add(v.A_f[n][-1] - (c.C*(c.T-1) - v.W[-1])
              == v.A_f[n][0] - (-v.W[0]))
        for dt in range(dur):
            s.add(v.c_f[0][c.T-1-dt] == v.c_f[0][dur-1-dt])
            s.add(v.r_f[0][c.T-1-dt] == v.r_f[0][dur-1-dt])


def bbr_low_util(timeout=10):
    '''Finds an example trace where BBR has < 10% utilization (can be made
    arbitrarily small)'''
    c = ModelConfig.default()
    c.compose = True
    c.cca = "bbr"
    # Simplification isn't necessary, but makes the output a bit easier to
    # understand
    c.simplify = True
    s, v = make_solver(c)
    # Consider the no loss case for simplicity
    s.add(v.L[0] == 0)
    # Ask for < 10% utilization. Can be made arbitrarily small
    s.add(v.S[-1] - v.S[0] < 0.1 * c.C * c.T)
    make_periodic(c, s, v, 2*c.R)
    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c)


def copa_low_util(timeout=10):
    '''Finds an example where Copa gets < 10% utilization. This is with the default
    model that composes. If c.compose = False, then CCAC cannot find an example
    where utilization is below 50%. Copa is proven to work in the non-composing
    model

    '''
    c = ModelConfig.default()
    c.compose = True
    c.cca = "copa"
    c.simplify = True
    c.calculate_qdel = True
    s, v = make_solver(c)
    # Consider the no loss case for simplicity
    s.add(v.L[0] == 0)
    # 10% utilization. Can be made arbitrarily small
    s.add(v.S[-1] - v.S[0] < 0.1 * c.C * c.T)
    make_periodic(c, s, v, c.R+c.D)

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
    c.buf_min = 2
    c.buf_max = 2
    c.simplify = False
    c.T = 5

    s, v = make_solver(c)

    # Start with zero loss and zero queue, so CCAC is forced to generate an
    # example trace *from scratch* showing how bad behavior can happen in a
    # network that was perfectly normal to begin with
    s.add(v.L[0] == 0)
    # Restrict alpha to small values, otherwise CCAC can output obvious and
    # uninteresting behavior
    s.add(v.alpha <= 0.1 * c.C * c.R)

    # Does there exist a time where loss happened while cwnd <= 1?
    conds = []
    for t in range(2, c.T-1):
        conds.append(And(
            v.c_f[0][t] <= 2,
            v.Ld_f[0][t+1] - v.Ld_f[0][t] >= 1,  # Burst due to loss detection
            v.S[t+1-c.R] - v.S[t-c.R] >= c.C + 1,  # Burst of BDP acks
            v.A[t+1] >= v.A[t] + 2 - 1e-6  # Sum of the two bursts (- epsilon)
        ))

    # We don't want an example with timeouts
    for t in range(c.T):
        s.add(Not(v.timeout_f[0][t]))

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
        "copa_low_util": copa_low_util
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

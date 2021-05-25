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
    c = ModelConfig.default()
    c.compose = True
    c.cca = "bbr"
    c.simplify = True
    s, v = make_solver(c)
    # Consider the no loss case for simplicity
    s.add(v.L[0] == 0)
    s.add(v.S[-1] - v.S[0] <= 0.1 * c.C * c.T)
    make_periodic(c, s, v, 2*c.R)
    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c)


def copa_low_util(timeout=10):
    c = ModelConfig.default()
    c.compose = True
    c.cca = "copa"
    c.simplify = True
    c.calculate_qdel = True
    s, v = make_solver(c)
    # Consider the no loss case for simplicity
    s.add(v.L[0] == 0)
    s.add(v.S[-1] - v.S[0] <= 0.01 * c.C * c.T)
    make_periodic(c, s, v, c.R+c.D)

    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c)


def aimd_premature_loss(timeout=60):
    c = ModelConfig.default()
    c.cca = "aimd"
    c.buf_min = 1.99
    c.buf_max = 1.99
    c.T = 10
    c.pacing = False
    c.simplify = False
    c.aimd_incr_irrespective = False
    c.unsat_core = True

    s, v = make_solver(c)
    # make_periodic(c, s, v, 1)
    # s.add(v.c_f[0][0] == v.c_f[0][-1])
    s.add(v.c_f[0][0] <= 4.1)

    # Start with zero loss and zero queue, so CCAC is forced to generate an
    # example trace *from scratch* showing how bad behavior can happen in a
    # network that was perfectly normal to begin with
    s.add(v.L[0] == 0)
    # s.add(v.L[-1] == 0)
    # s.add(v.A[0] - v.S[0] == 0)
    # Restrict alpha to small values, otherwise CCAC can output obvious and
    # uninteresting behavior
    s.add(v.alpha <= 0.1 * c.C * c.R)

    # Initial conditions that we proved
    # s.add(v.c_f[0][0] <= c.C*(c.R + c.D) + c.buf_min + v.alpha)
    # s.add(v.L_f[0][0] - v.Ld_f[0][0] <= c.C*(c.R + c.D) + v.alpha)

    # Does there exist a time where loss happened while cwnd <= 1?
    conds = []
    # s.add(v.c_f[0][0] <= 2.5)
    for t in range(c.T-1):
        conds.append(And(
            v.Ld_f[0][t+1] > v.Ld_f[0][t],  # Loss happened
            v.c_f[0][t+1] < 1.1))
        # conds.append(v.c_f[0][t] > 2.5)
        # conds.append(And(
        #     v.A[t] + 2.19 <= v.A[t+1]))

    # We don't want an example with timeouts
    for t in range(c.T):
        s.add(Not(v.timeout_f[0][t]))

    s.add(Or(*conds))

    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c)


def aimd_premature_loss_bkp2(timeout=60):
    c = ModelConfig.default()
    c.cca = "aimd"
    c.buf_min = 1.9
    c.buf_max = 1.9
    c.T = 15
    c.pacing = False
    c.simplify = False
    c.aimd_incr_irrespective = False
    c.unsat_core = True

    s, v = make_solver(c)
    # make_periodic(c, s, v, 1)
    # s.add(v.c_f[0][0] == v.c_f[0][-1])
    s.add(v.c_f[0][0] == 3.85)

    # Start with zero loss and zero queue, so CCAC is forced to generate an
    # example trace *from scratch* showing how bad behavior can happen in a
    # network that was perfectly normal to begin with
    # s.add(v.L[0] == 0)
    # s.add(v.L[-1] == 0)
    # s.add(v.A[0] - v.S[0] == 0)
    # Restrict alpha to small values, otherwise CCAC can output obvious and
    # uninteresting behavior
    s.add(v.alpha <= 0.1 * c.C * c.R)

    # Initial conditions that we proved
    # s.add(v.c_f[0][0] <= c.C*(c.R + c.D) + c.buf_min + v.alpha)
    # s.add(v.L_f[0][0] - v.Ld_f[0][0] <= c.C*(c.R + c.D) + v.alpha)

    # Does there exist a time where loss happened while cwnd <= 1?
    conds = []
    # s.add(v.c_f[0][0] <= 2.5)
    for t in range(c.T-1):
        conds.append(And(
            v.L[t+1] > v.L[t],  # Loss happened
            v.c_f[0][t] < 2.1))
        # conds.append(v.c_f[0][t] > 2.5)
        # conds.append(And(
        #     v.A[t] + 2.19 <= v.A[t+1]))

        # We don't want timeouts
        s.add(Not(v.timeout_f[0][t]))
    s.add(Or(*conds))

    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c)


def aimd_premature_loss_bkp(timeout=60):
    # cached/d359df6497d6b232.cached
    c = ModelConfig.default()
    c.cca = "aimd"
    c.buf_min = 2
    c.buf_max = 2
    c.T = 20
    c.pacing = False
    c.aimd_incr_irrespective = True
    s, v = make_solver(c)
    # Start with zero loss and zero queue, so CCAC is forced to generate an
    # example trace *from scratch* showing how bad behavior can happen in a
    # network that was perfectly normal to begin with
    s.add(v.L[0] == 0)
    # s.add(v.A[0] - v.S[0] == 0)

    # Does there exist a time where loss happened while cwnd <= 1?
    conds = []
    for t in range(c.T-1):
        conds.append(And(
            v.L[t+1] > v.L[t],  # Loss happened
            v.c_f[0][t] <= 1.1))
    s.add(Or(*conds))

    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c)


if __name__ == "__main__":
    aimd_premature_loss()
    # bbr_low_util()

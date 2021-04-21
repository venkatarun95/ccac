import argparse
from z3 import And, If, Or

from binary_search import BinarySearch
from cache import run_query
from model import Variables, make_solver, min_send_quantum
from model_utils import ModelConfig, find_bound


def min_cwnd(c: ModelConfig, err: float, timeout: float):
    assert(c.N == 1)
    assert(c.buf_max is not None)
    max_cwnd = c.C * c.R + c.buf_max

    def gap(c: ModelConfig, v: Variables, t: int):
        return v.A[t] - v.L[t] - (c.C * t - v.W[t])

    def cthresh(c: ModelConfig, v: Variables, t: int):
        diff = v.c_f[0][t] - c.C*c.R
        return If(diff < 0, 0, diff)

    if c.pacing:
        s, v = make_solver(c)
        s.add(gap(c, v, c.T-1) > cthresh(c, v, c.T-1))
        qres = run_query(s, c, timeout)
        print("Queue makes more sense: ", qres.satisfiable)
        assert(str(qres.satisfiable) == "unsat")

    def min_cwnd_when_loss(c: ModelConfig, thresh: float):
        assert(c.N == 1)
        s, v = make_solver(c)
        conds = []
        for t in range(1, c.T):
            conds.append(And(v.L[t] > v.L[t-1],
                             v.c_f[0][t] <= thresh))
        s.add(Or(*conds))
        s.add(v.L[0] == 0)
        if c.pacing:
            s.add(gap(c, v, 0) <= cthresh(c, v, 0))
        return s

    bounds = find_bound(
        min_cwnd_when_loss, c, BinarySearch(0, max_cwnd, err), timeout)
    print(bounds)


def prove_loss_bounds(c: ModelConfig, timeout: float):
    '''Prove loss bounds for a particular buffer length. Need to sweep buffer
    sizes to get confidence that the bounds hold.

    '''
    assert(c.N == 1)
    assert(c.buf_min is not None and c.buf_min == c.buf_max)

    max_cwnd = c.C*(c.R + c.D) + c.buf_min
    def max_undet(v: Variables):
        ''' We'll prove that the number of undetected losses will be below this
        at equilibrium

        '''
        return c.C*(c.R + c.D) + v.alpha

    # If cwnd > max_cwnd, it will fall by at least alpha
    c.T = 10
    s, v = make_solver(c)
    s.add(v.c_f[0][0] > max_cwnd)
    s.add(v.L[0] == v.L[-1])
    s.add(v.L_f[0][0] - v.Ld_f[0][0] < max_undet(v))
    s.add(v.alpha < 0.188 * c.C * c.R)

    qres = run_query(s, c, timeout)
    print(qres.satisfiable)
    assert(qres.satisfiable == "unsat")


def high_loss_example(c: ModelConfig, err: float, timeout: float):
    # Note, the threshold seems to depend on T. Pick a large one
    assert(c.N == 1)
    assert(c.buf_min is not None and c.buf_min == c.buf_max)

    max_cwnd = c.C*(c.R + c.D) + c.buf_min

    # If cwnd > max_cwnd, it will fall by at least alpha
    def example(c: ModelConfig, thresh: float):
        s, v = make_solver(c)
        s.add(v.c_f[0][0] > max_cwnd)
        s.add(v.alpha <= thresh * c.C * c.R)

        s.add(v.Ld_f[0][0] == 0)

        # Periodicity
        s.add(v.L_f[0][0] - v.Ld_f[0][0] == v.L_f[0][-1] - v.Ld_f[0][-1])
        s.add(v.A_f[0][0] - v.L_f[0][0] - v.S_f[0][0]
              == v.A_f[0][-1] - v.L_f[0][-1] - v.S_f[0][-1])
        s.add(v.c_f[0][0] == v.c_f[0][-1])

        # Have to send either zero packets or >= 1 alpha every
        # timestep. Otherwise we get an unrealistic case
        min_send_quantum(c, s, v)

        # There is at-least some input
        s.add(v.A_f[0][0] < v.A_f[0][-1])
        return s

    bounds = find_bound(
        example, c, BinarySearch(0, max_cwnd, err), timeout)
    print(bounds)


if __name__ == "__main__":
    cfg_args = ModelConfig.get_argparse()
    common_args = argparse.ArgumentParser(add_help=False)
    common_args.add_argument("--err", type=float, default=0.05)
    common_args.add_argument("--timeout", type=float, default=10)
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(title="subcommand", dest="subcommand")

    subparsers.add_parser("min_cwnd", parents=[cfg_args, common_args])
    subparsers.add_parser("prove_loss_bounds", parents=[cfg_args, common_args])
    subparsers.add_parser("high_loss_example", parents=[cfg_args, common_args])

    args = parser.parse_args()
    c = ModelConfig.from_argparse(args)

    if args.subcommand == "min_cwnd":
        min_cwnd(c, args.err, args.timeout)
    elif args.subcommand == "prove_loss_bounds":
        prove_loss_bounds(c, args.timeout)
    elif args.subcommand == "high_loss_example":
        high_loss_example(c, args.err, args.timeout)
    else:
        assert(False)

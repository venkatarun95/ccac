import argparse
from z3 import And, If, Or

from binary_search import BinarySearch
from cache import run_query
from model import Variables, make_solver
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

    s, v = make_solver(c)
    s.add(gap(c, v, c.T-1) > cthresh(c, v, c.T-1))
    qres = run_query(s, c, timeout)
    print("Queue makes more sense: ", qres.satisfiable)
    assert(str(qres.satisfiable) == "unsat")


    def min_cwnd_when_loss(c: ModelConfig, thresh: float):
        s, v = make_solver(c)
        conds = []
        for t in range(1, c.T):
            conds.append(And(v.L[t] > v.L[t-1],
                         v.c_f[0][t] < thresh))
        s.add(Or(*conds))
        s.add(gap(c, v, 0) <= cthresh(c, v, 0))
        return s

    bounds = find_bound(
        min_cwnd_when_loss, c, BinarySearch(0, max_cwnd, err), timeout)
    print(bounds)


if __name__ == "__main__":
    cfg_args = ModelConfig.get_argparse()
    common_args = argparse.ArgumentParser(add_help=False)
    common_args.add_argument("--err", type=float, default=0.05)
    common_args.add_argument("--timeout", type=float, default=10)
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(title="subcommand", dest="subcommand")

    subparsers.add_parser("min_cwnd", parents=[cfg_args, common_args])

    args = parser.parse_args()
    c = ModelConfig.from_argparse(args)

    if args.subcommand == "min_cwnd":
        min_cwnd(c, args.err, args.timeout)
    else:
        assert(False)

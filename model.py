import argparse
import pickle as pkl
from typing import Optional, Tuple
from z3 import Real

from binary_search import BinarySearch
from cache import QueryResult, run_query
from multi_flow import ModelConfig, make_solver, plot_model


def find_lower_tpt_bound(
    cfg: ModelConfig, err: float, timeout: float, epsilon: str
) -> Tuple[float, Optional[Tuple[float, float]], float]:
    ''' Finds a bound in terms of percentage used '''
    search = BinarySearch(0.0, 1.0, err)
    while True:
        pt = search.next_pt()
        if pt is None:
            break

        s = make_solver(cfg)

        # The amount of time for which the cc can pick any cwnd
        freedom_duration = 1
        if cfg.cca == "copa":
            freedom_duration = cfg.R + cfg.D

        # If cwnd decreased in the duration, we are sort of in equilibrium
        for t in range(freedom_duration):
            s.add(Real("cwnd_0,%d" % t) >= Real("cwnd_0,%d" % (cfg.T-1)))

        s.add(Real("tot_out_%d" % (cfg.T - 1)) < cfg.C * cfg.T * pt)

        if epsilon == "zero":
            s.add(Real("epsilon") == 0)
        elif epsilon == "lt_alpha":
            s.add(Real("epsilon") < Real("alpha"))
        elif epsilon == "gt_alpha":
            s.add(Real("epsilon") > Real("alpha"))
        else:
            assert(False)

        print(f"Testing {pt * 100}% utilization")
        qres = run_query(s, cfg, timeout=timeout)

        print(qres.satisfiable)
        if qres.satisfiable == "sat":
            print("tot_out", qres.model["tot_out_%d" % (cfg.T - 1)])
            for t in range(cfg.T):
                print("wasted", qres.model[f"wasted_{t}"])
            val = 3
        elif qres.satisfiable == "unknown":
            val = 2
        elif qres.satisfiable == "unsat":
            val = 1
        else:
            print(qres)
            assert(False)
        search.register_pt(pt, val)
    return search.get_bounds()


if __name__ == "__main__":
    cfg_args = ModelConfig.get_argparse()
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(title="subcommand", dest="subcommand")

    tpt_bound_args = subparsers.add_parser("tpt_bound", parents=[cfg_args])
    tpt_bound_args.add_argument("--err", type=float, default=0.05)
    tpt_bound_args.add_argument("--timeout", type=float, default=10)
    tpt_bound_args.add_argument("--epsilon", type=str, default="zero",
                                choices=["zero", "lt_alpha", "gt_alpha"])

    plot_args = subparsers.add_parser("plot")
    plot_args.add_argument("cache_file_name")

    args = parser.parse_args()
    print(args)

    if args.subcommand == "tpt_bound":
        cfg = ModelConfig.from_argparse(args)

        bounds = find_lower_tpt_bound(
            cfg, args.err, args.timeout, args.epsilon)
        print(bounds)
    elif args.subcommand == "plot":
        try:
            f = open(args.cache_file_name, 'rb')
            qres: QueryResult = pkl.load(f)
        except Exception as e:
            print("Exception while loacing cached file")
            print(e)
        print(qres.satisfiable)
        if qres.satisfiable == "sat":
            plot_model(qres.model, qres.cfg)

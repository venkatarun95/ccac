import argparse
from typing import Tuple
from z3 import Real

from binary_search import BinarySearch
from cache import run_query
from multi_flow import ModelConfig, make_solver


def find_lower_tpt_bound(
    cfg: ModelConfig, err: float, timeout: float
) -> Tuple[float, float]:
    ''' Finds a bound in terms of percentage used '''
    search = BinarySearch(0.0, 1.0, err)
    while True:
        pt = search.next_pt()
        if pt is None:
            break

        s = make_solver(cfg)
        # If cwnd decreased in the duration, we are sort of in equilibrium
        for t in range(cfg.R + cfg.D):
            s.add(Real("cwnd_0,%d" % t) >= Real("cwnd_0,%d" % (cfg.T-1)))

        s.add(Real("tot_out_%d" % (cfg.T - 1)) < cfg.C * cfg.T * pt)

        print(f"Testing {pt * 100}% utilization")
        qres = run_query(s, timeout=timeout)
        print(qres.satisfiable)
        if qres.satisfiable == "sat":
            val = 3
        elif qres.satisfiable == "unknown":
            val = 2
        elif qres.satisfiable == "unsat":
            val = 1
        else:
            assert(False)
        search.register_pt(pt, val)
    return search.get_bounds()


if __name__ == "__main__":
    cfg_args = ModelConfig.get_argparse()
    parser = argparse.ArgumentParser(parents=[cfg_args])
    parser.add_argument("--err", type=float, default=0.05)
    parser.add_argument("--timeout", type=float, default=10)
    args = parser.parse_args()
    print(args)
    cfg = ModelConfig.from_argparse(args)

    lo, hi = find_lower_tpt_bound(cfg, args.err, args.timeout)
    print(lo, hi)

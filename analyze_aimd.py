import argparse
import matplotlib.pyplot as plt
import numpy as np
from z3 import Real, Or

from cache import run_query
from model import find_cwnd_incr_bound, find_cwnd_stay_bound,\
    find_const_cwnd_util_lbound
from multi_flow import ModelConfig, make_solver, freedom_duration


def single_flow_util(
    cfg: ModelConfig, err: float, timeout: float
):
    ''' Find a steady-state such that if it enters steady state, it will remain
    there '''

    # Plot as a function of buffer size (droptail)
    buf_sizes = np.linspace(0, 5, 10)[1:]
    cwnd_bounds = []
    util_bounds = []

    for buf_size in buf_sizes:
        cfg.buf_min = buf_size
        cfg.buf_max = buf_size
        incr_bound = find_cwnd_incr_bound(cfg, None, err, timeout)
        print(f"For buffer size {buf_size} incr_bound={incr_bound}")

        # Same as find_cwnd_stay_bound
        s = make_solver(cfg)
        conds = []
        dur = freedom_duration(cfg)
        for n in range(cfg.N):
            for t in range(dur):
                s.add(Real(f"cwnd_{n},{t}") >= incr_bound[0])
                # We need all the last freedom_duration(cfg) timesteps to be
                # large so we can apply induction to extend theorem to infinity
                conds.append(Real(f"cwnd_{n},{cfg.T-1-t}") < incr_bound[0])
        s.add(Or(*conds))
        print(f"Testing init cwnd for stay = {incr_bound[0]} BDP")
        qres = run_query(s, cfg, timeout=timeout)
        print(qres.satisfiable)

        if qres.satisfiable != "unsat":
            print("Could not prove bound. Will search for a new stay bound")
            stay_bound = find_cwnd_stay_bound(cfg, None, err, timeout)
            if stay_bound[0] > incr_bound[0]:
                print("Failed to prove any bounds: ", stay_bound)
                return
            bound = stay_bound[0]
        else:
            # This is the definitive bound
            bound = incr_bound[0]

        # This is a definitive bound
        cwnd_thresh = bound
        util_bound = find_const_cwnd_util_lbound(
            cfg, cwnd_thresh, err, timeout)
        print(f"For buffer size {buf_size} util_bound={util_bound}")

        cwnd_bounds.append(cwnd_thresh)
        util_bounds.append(util_bound[0] * 100)

    print([x for x in zip(buf_sizes, cwnd_bounds, util_bounds)])

    fig, (ax1, ax2) = plt.subplots(2, 1, sharex=True)
    ax1.plot(buf_sizes, cwnd_bounds)
    ax2.plot(buf_sizes, util_bounds)
    ax1.set_ylabel("Steady state cwnd (in BDP)")
    ax2.set_ylabel("Minimum utilization %")
    ax2.set_xlabel("Buffer size (in BDP)")
    plt.show()
    plt.savefig("/tmp/single_flow_util.svg")
    print(buf_sizes, cwnd_bounds, util_bounds)


if __name__ == "__main__":
    cfg_args = ModelConfig.get_argparse()
    common_args = argparse.ArgumentParser(add_help=False)
    common_args.add_argument("--err", type=float, default=0.05)
    common_args.add_argument("--timeout", type=float, default=10)

    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(title="subcommand", dest="subcommand")

    tpt_bound_args = subparsers.add_parser(
        "single_flow_util", parents=[cfg_args, common_args])
    args = parser.parse_args()
    cfg = ModelConfig.from_argparse(args)

    if args.subcommand == "single_flow_util":
        single_flow_util(cfg, args.err, args.timeout)

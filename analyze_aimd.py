import argparse
import matplotlib.pyplot as plt
import numpy as np
from z3 import If, Real, Or, Solver

from binary_search import BinarySearch
from cache import run_query
from model import find_bound, find_cwnd_incr_bound,\
    find_const_cwnd_util_lbound, find_periodic_low_cwnd
from multi_flow import ModelConfig, make_solver, freedom_duration


# buf_sizes = [0.1, 0.3, 0.4, 0.6, 0.7, 0.8, 0.9]
# buf_sizes = list(np.linspace(0.1, 1.1, 5)) + list(np.linspace(1.1, 3.1, 10))
buf_sizes = [1.6]


def single_flow_util(
    cfg: ModelConfig, err: float, timeout: float
):
    ''' Find a steady-state such that if it enters steady state, it will remain
    there '''
    global buf_sizes

    def cwnd_stay_bound(cfg: ModelConfig, thresh: float) -> Solver:
        s = make_solver(cfg)
        conds = []
        dur = freedom_duration(cfg)
        for n in range(cfg.N):
            for t in range(dur):
                s.add(Real(f"cwnd_{n},{t}") >= thresh)
            for t in range(dur, cfg.T):
                # We need all the last freedom_duration(cfg) timesteps to be
                # large so we can apply induction to extend theorem to infinity
                conds.append(Real(f"cwnd_{n},{t}") < thresh)
        s.add(Or(*conds))
        assert(cfg.N == 1)
        s.add(Real("tot_inp_0") - Real("tot_lost_0") - (0-Real("wasted_0"))
              <= Real("cwnd_0,0") - cfg.C*cfg.R)
        return s

    # Plot as a function of buffer size (droptail)
    cwnd_bounds = []
    util_bounds = []
    T = cfg.T

    for buf_size in np.asarray(buf_sizes) * cfg.C * cfg.R:
        cfg.buf_min = buf_size
        cfg.buf_max = buf_size

        # Queue size will eventually match cwnd. We use this in
        # cwnd_stay_bound to make it tighter
        assert(cfg.N == 1)
        s = make_solver(cfg)
        s.add(Real("cwnd_0,0") < cfg.C * cfg.R + buf_size)
        q_bound = Real(f"cwnd_0,{T-1}") - cfg.C*cfg.R
        q_bound = If(q_bound >= 0, q_bound, 0)
        s.add(Real(f"tot_inp_{T-1}") - Real(f"tot_lost_{T-1}")
              - (cfg.C*(T-1) - Real(f"wasted_{T-1}"))
              > q_bound)
        # Loss did not happen recently
        s.add(Real(f"cwnd_0,{T-1}") > Real(f"cwnd_0,{T-2}"))
        qres = run_query(s, cfg, timeout=timeout)
        print("Queue will eventually be cwnd limited", qres.satisfiable)
        assert(qres.satisfiable == "unsat")

        incr_bound = find_cwnd_incr_bound(cfg, None, err, timeout)
        print(f"For buffer size {buf_size} incr_bound={incr_bound}")

        max_cwnd = cfg.C * cfg.R + cfg.buf_max

        # Same as find_cwnd_stay_bound
        print(f"Testing init cwnd for stay = {incr_bound[0]} BDP")
        s = cwnd_stay_bound(cfg, incr_bound[0])
        qres = run_query(s, cfg, timeout=timeout)
        print(qres.satisfiable)

        if qres.satisfiable != "unsat":
            print("Could not prove bound. Will search for a new stay bound")
            stay_bound = find_bound(cwnd_stay_bound, cfg,
                                    BinarySearch(0, max_cwnd, err), timeout)
            if stay_bound[0] > incr_bound[0]:
                print("Failed to prove any bounds: ", stay_bound)
                return
            bound = stay_bound[0]
        else:
            # This is the definitive bound
            bound = incr_bound[0]

        # This is a definitive bound
        cwnd_thresh = bound
        #util_bound = find_const_cwnd_util_lbound(
        #    cfg, cwnd_thresh, err, timeout)
        util_bound = [0]
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


def plot_periodic_low_cwnd(
    cfg: ModelConfig, err: float, timeout: float
):
    global buf_sizes

    cwnd_bounds = []
    for buf_size in buf_sizes:
        cfg.buf_min = buf_size
        cfg.buf_max = buf_size

        bound = find_periodic_low_cwnd(cfg, True, err, timeout)
        print(bound)
        bound = bound[2]
        cwnd_bounds.append(bound)

    print([x for x in zip(buf_sizes, cwnd_bounds)])
    fig, ax = plt.subplots(1, 1)
    ax.plot(buf_sizes, cwnd_bounds)
    ax.set_ylabel("Steady state cwnd (in BDP)")
    ax.set_xlabel("Buffer size (in BDP)")
    plt.show()


if __name__ == "__main__":
    cfg_args = ModelConfig.get_argparse()
    common_args = argparse.ArgumentParser(add_help=False)
    common_args.add_argument("--err", type=float, default=0.05)
    common_args.add_argument("--timeout", type=float, default=10)

    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(title="subcommand", dest="subcommand")

    tpt_bound_args = subparsers.add_parser(
        "single_flow_util", parents=[cfg_args, common_args])

    tpt_bound_args = subparsers.add_parser(
        "plot_periodic_low_cwnd", parents=[cfg_args, common_args])

    args = parser.parse_args()
    cfg = ModelConfig.from_argparse(args)

    if args.subcommand == "single_flow_util":
        single_flow_util(cfg, args.err, args.timeout)
    elif args.subcommand == "plot_periodic_low_cwnd":
        plot_periodic_low_cwnd(cfg, args.err, args.timeout)
    else:
        print(f"Unrecognized command '{args.subcommand}'")

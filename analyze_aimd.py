import argparse
import matplotlib.pyplot as plt
import numpy as np

from model import find_cwnd_incr_bound, find_cwnd_stay_bound,\
    find_const_cwnd_util_lbound
from multi_flow import ModelConfig


def single_flow_util(
    cfg: ModelConfig, err: float, timeout: float
):
    ''' Find a steady-state such that if it enters steady state, it will remain
    there '''

    # Plot as a function of buffer size (droptail)
    buf_sizes = np.linspace(0, 5, 10)
    cwnd_bounds = []
    util_bounds = []

    for buf_size in buf_sizes:
        cfg.buf_min = buf_size
        cfg.buf_max = buf_size
        incr_bound = find_cwnd_incr_bound(cfg, None, err, timeout)
        print(f"For buffer size {buf_size} incr_bound={incr_bound}")
        stay_bound = find_cwnd_stay_bound(cfg, None, err, timeout)
        print(f"For buffer size {buf_size} stay_bound={stay_bound}")

        # This is a definitive bound
        bound = min(incr_bound[0], stay_bound[0])
        cwnd_thresh = bound * cfg.C * cfg.R
        util_bound = find_const_cwnd_util_lbound(
            cfg, cwnd_thresh, err, timeout)
        print(f"For buffer size {buf_size} util_bound={util_bound}")

        cwnd_bounds.append(cwnd_thresh)
        util_bounds.append(util_bound[0] * 100)

    fig, (ax1, ax2) = plt.subplots(2, 1, sharex=True)
    ax1.plot(buf_sizes, cwnd_bounds)
    ax2.plot(buf_sizes, util_bounds)
    ax1.set_ylabel("Steady state cwnd (in BDP)")
    ax2.set_ylabel("Minimum utilization %")
    ax2.set_xlabel("Buffer size (in BDP)")
    plt.show()
    plt.savefig("/tmp/single_flow_util.svg")


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

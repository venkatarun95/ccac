import argparse
from z3 import Real, And

from cache import run_query
from multi_flow import ModelConfig, freedom_duration, make_solver


def fixed_d_util(cfg: ModelConfig, timeout: float):
    dur = freedom_duration(cfg)

    cwnd_thresh = 0.1 # cfg.C * (cfg.R + cfg.D)
    mult_incr = (cfg.R + cfg.D) / cfg.R

    cfg.T = 2 * dur - 1

    # How much does it increase
    s = make_solver(cfg)
    for t in range(dur):
        s.add(Real(f"cwnd_0,{t}") <= cwnd_thresh)
    s.add(And(
        Real(f"cwnd_0,{cfg.T-1}") < cwnd_thresh,
        Real(f"cwnd_0,{dur-1}") * mult_incr > Real(f"cwnd_0,{cfg.T-1}")))
    qres = run_query(s, cfg, timeout=timeout)
    print("Does it increase reliably?", qres.satisfiable)

    s = make_solver(cfg)
    for t in range(dur):
        s.add(Real(f"cwnd_0,{t}") > cwnd_thresh)
    s.add(Real(f"wasted_{cfg.T-1}") > Real(f"wasted_{cfg.T-2}"))
    qres = run_query(s, cfg, timeout=timeout)
    print("Once we cross the threshold, do we ever waste?", qres.satisfiable)


if __name__ == "__main__":
    cfg_args = ModelConfig.get_argparse()
    common_args = argparse.ArgumentParser(add_help=False)
    # common_args.add_argument("--err", type=float, default=0.05)
    common_args.add_argument("--timeout", type=float, default=10)

    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(title="subcommand", dest="subcommand")

    tpt_bound_args = subparsers.add_parser(
        "util", parents=[cfg_args, common_args])

    args = parser.parse_args()
    cfg = ModelConfig.from_argparse(args)

    if args.cca != "fixed_d":
        print("Warning: this analysis really only applies to fixed_d")

    if args.subcommand == "util":
        fixed_d_util(cfg, args.timeout)

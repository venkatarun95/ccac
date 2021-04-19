import argparse
from fractions import Fraction
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
from typing import Callable, Dict, List, Optional, Tuple, Union
import z3

from binary_search import BinarySearch, sat_to_val
import cache
from my_solver import MySolver

ModelDict = Dict[str, Union[Fraction, bool]]


def model_to_dict(model: z3.ModelRef) -> ModelDict:
    ''' Utility function that takes a z3 model and extracts its variables to a
    dict'''
    decls = model.decls()
    res: Dict[str, Union[float, bool]] = {}
    for d in decls:
        val = model[d]
        if type(val) == z3.BoolRef:
            res[d.name()] = bool(val)
        elif type(val) == z3.IntNumRef:
            res[d.name()] = Fraction(val.as_long())
        else:
            # Assume it is numeric
            res[d.name()] = val.as_fraction()
    return res


class ModelConfig:
    # Number of flows
    N: int
    # Jitter parameter (in timesteps)
    D: int
    # RTT (in timesteps)
    R: int
    # Number of timesteps
    T: int
    # Link rate
    C: float
    # Packets cannot be dropped below this threshold
    buf_min: Optional[float]
    # Packets have to be dropped above this threshold
    buf_max: Optional[float]
    # Number of dupacks before sender declares loss
    dupacks: Optional[float]
    # Congestion control algorithm
    cca: str
    # If false, we'll use a model is more restrictive but does not compose
    compose: bool
    # Additive increase parameter used by various CCAs
    alpha: Union[float, z3.ArithRef] = 1.0
    # Whether or not to use pacing in various CCA
    pacing: bool
    # If compose is false, wastage can only happen if queue length < epsilon
    epsilon: str
    # Whether to turn on unsat_core for all variables
    unsat_core: bool
    # Whether to simplify output before plotting/saving
    simplify: bool

    def __init__(
        self,
        N: int,
        D: int,
        R: int,
        T: int,
        C: float,
        buf_min: Optional[float],
        buf_max: Optional[float],
        dupacks: Optional[float],
        cca: str,
        compose: bool,
        alpha: Optional[float],
        pacing: bool,
        epsilon: str,
        unsat_core: bool,
        simplify: bool
    ):
        self.__dict__ = locals()

    @staticmethod
    def get_argparse() -> argparse.ArgumentParser:
        parser = argparse.ArgumentParser(add_help=False)
        parser.add_argument("-N", "--num-flows", type=int, default=1)
        parser.add_argument("-D", type=int, default=1)
        parser.add_argument("-R", "--rtt", type=int, default=1)
        parser.add_argument("-T", "--time", type=int, default=10)
        parser.add_argument("-C", "--rate", type=float, default=1)
        parser.add_argument("--buf-min", type=float, default=None)
        parser.add_argument("--buf-max", type=float, default=None)
        parser.add_argument("--dupacks", type=float, default=None)
        parser.add_argument("--cca", type=str, default="const",
                            choices=["const", "aimd", "copa", "bbr",
                                     "fixed_d"])
        parser.add_argument("--no-compose", action="store_true")
        parser.add_argument("--alpha", type=float, default=None)
        parser.add_argument("--pacing", action="store_const", const=True,
                            default=False)
        parser.add_argument("--epsilon", type=str, default="zero",
                            choices=["zero", "lt_alpha", "lt_half_alpha",
                                     "gt_alpha"])
        parser.add_argument("--unsat-core", action="store_true")
        parser.add_argument("--simplify", action="store_true")

        return parser

    @classmethod
    def from_argparse(cls, args: argparse.Namespace):
        return cls(
            args.num_flows,
            args.D,
            args.rtt,
            args.time,
            args.rate,
            args.buf_min,
            args.buf_max,
            args.dupacks,
            args.cca,
            not args.no_compose,
            args.alpha,
            args.pacing,
            args.epsilon,
            args.unsat_core,
            args.simplify)

    @classmethod
    def default(cls):
        return cls.from_argparse(cls.get_argparse().parse_args(args=[]))


class Variables:
    ''' Some variables that everybody uses '''

    def __init__(self, c: ModelConfig, s: MySolver):
        T = c.T

        # Af denotes per-flow A
        self.A_f = [[s.Real(f"arrival_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        self.A = [s.Real(f"tot_arrival_{t}") for t in range(T)]
        self.c_f = [[s.Real(f"cwnd_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        self.r_f = [[s.Real(f"rate_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        # Total number of losses detected
        self.Ld_f = [[s.Real(f"loss_detected_{n},{t}")
                      for t in range(T)]
                     for n in range(c.N)]
        self.S_f = [[s.Real(f"service_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        self.S = [s.Real(f"tot_service_{t}") for t in range(T)]
        self.L_f = [[s.Real(f"losts_{n},{t}") for t in range(T)]
                    for n in range(c.N)]
        self.L = [s.Real(f"tot_lost_{t}") for t in range(T)]
        self.W = [s.Real(f"wasted_{t}") for t in range(T)]

        if not c.compose:
            self.epsilon = s.Real("epsilon")

        if c.dupacks is None:
            self.dupacks = s.Real('dupacks')
            s.add(self.dupacks >= 0)
        else:
            self.dupacks = c.dupacks

        if c.alpha is None:
            self.alpha = s.Real('alpha')
            s.add(self.alpha > 0)
        else:
            self.alpha = c.alpha


def freedom_duration(cfg: ModelConfig) -> int:
    ''' The amount of time for which the cc can pick any cwnd '''
    if cfg.cca == "const":
        return 0
    elif cfg.cca == "aimd":
        return 1
    elif cfg.cca == "fixed_d":
        return 3 * cfg.R + 2 * cfg.D + 1
    elif cfg.cca == "copa":
        return cfg.R + cfg.D
    elif cfg.cca == "bbr":
        return cfg.R + 1
    else:
        assert(False)


def find_bound(model_cons: Callable[[ModelConfig, float], MySolver],
               cfg: ModelConfig, search: BinarySearch, timeout: float):
    while True:
        thresh = search.next_pt()
        if thresh is None:
            break
        s = model_cons(cfg, thresh)

        print(f"Testing threshold = {thresh}")
        qres = cache.run_query(s, cfg, timeout=timeout)

        print(qres.satisfiable)
        search.register_pt(thresh, sat_to_val(qres.satisfiable))
    return search.get_bounds()


def plot_model(m: ModelDict, cfg: ModelConfig):
    def to_arr(name: str, n: Optional[int] = None) -> np.array:
        if n is None:
            names = [f"{name}_{t}" for t in range(cfg.T)]
        else:
            names = [f"{name}_{n},{t}" for t in range(cfg.T)]
        res = []
        for n in names:
            if n in m:
                res.append(m[n])
            else:
                res.append(-1)
        return np.array(res)

    # Print the constants we picked
    if cfg.dupacks is None:
        print("dupacks = ", m["dupacks"])
    if cfg.cca in ["aimd", "fixed_d", "copa"] and cfg.alpha is None:
        print("alpha = ", m["alpha"])
    if not cfg.compose:
        print("epsilon = ", m["epsilon"])
    for n in range(cfg.N):
        print(f"Init cwnd for flow {n}: ",
              to_arr("cwnd", n)[:freedom_duration(cfg)])

    # Configure the plotting
    fig, (ax1, ax2) = plt.subplots(2, 1, sharex=True)
    fig.set_size_inches(18.5, 10.5)
    ax1.grid(True)
    ax2.grid(True)
    ax2.set_xticks(range(0, cfg.T))
    ax2.yaxis.set_major_locator(matplotlib.ticker.MaxNLocator(integer=True))

    # Create 3 y-axes in the second plot
    ax2_rtt = ax2.twinx()
    ax2_rate = ax2.twinx()
    ax2.set_ylabel("Cwnd")
    ax2_rtt.set_ylabel("RTT")
    ax2_rate.set_ylabel("Rate")
    ax2_rate.spines["right"].set_position(("axes", 1.05))
    ax2_rate.spines["right"].set_visible(True)

    linestyles = ['--', ':', '-.', '-']
    adj = 0  # np.asarray([C * t for t in range(T)])
    times = [t for t in range(cfg.T)]
    ct = np.asarray([cfg.C * t for t in range(cfg.T)])

    ax1.plot(times, ct - to_arr("wasted"),
             color='black', marker='o', label='Bound', linewidth=3)
    ax1.plot(times[cfg.D:], (ct - to_arr("wasted"))[:-cfg.D],
             color='black', marker='o', linewidth=3)
    ax1.plot(times, to_arr("tot_service"),
             color='red', marker='o', label='Total Egress')
    ax1.plot(times, to_arr("tot_arrival"),
             color='blue', marker='o', label='Total Ingress')
    ax1.plot(times, to_arr("tot_arrival") - to_arr("tot_lost"),
             color='lightblue', marker='o', label='Total Ingress Accepted')

    # Print incr/decr allowed
    if cfg.cca == "copa":
        print("Copa queueing delay calculation. Format [incr/decr/qdel]")
        for n in range(cfg.N):
            print(f"Flow {n}")
            for t in range(cfg.T):
                print("{:<3}".format(t), end=": ")
                for dt in range(cfg.T):
                    iname = f"incr_allowed_{n},{t},{dt}"
                    dname = f"decr_allowed_{n},{t},{dt}"
                    qname = f"qdel_{t},{dt}"
                    if iname not in m:
                        print(f" - /{int(m[qname])}", end=" ")
                    else:
                        print(
                            f"{int(m[iname])}/{int(m[dname])}/{int(m[qname])}",
                            end=" ")
                print("")

    col_names: List[str] = ["wasted", "tot_service", "tot_arrival", "tot_lost"]
    per_flow: List[str] = ["loss_detected", "last_loss", "cwnd", "rate"]
    if cfg.cca == "bbr":
        per_flow.extend(["new_rates", "states"])

    cols: List[Tuple[str, Optional[int]]] = [(x, None) for x in col_names]
    for n in range(cfg.N):
        for x in per_flow:
            if x == "last_loss" and cfg.cca != "aimd":
                continue
            cols.append((x, n))
            col_names.append(f"{x}_{n}")

    print("\n", "=" * 30, "\n")
    print(("t  " + "{:<15}" * len(col_names)).format(*col_names))
    for t, vals in enumerate(zip(*[list(to_arr(*c)) for c in cols])):
        v = ["%.10f" % v for v in vals]
        print(f"{t: <2}", ("{:<15}" * len(v)).format(*v))

    for n in range(cfg.N):
        args = {'marker': 'o', 'linestyle': linestyles[n]}

        ax1.plot(times, to_arr("service", n) - adj,
                 color='red', label='Egress %d' % n, **args)
        ax1.plot(times, to_arr("arrival", n) - adj,
                 color='blue', label='Ingress %d' % n, **args)

        ax1.plot(times, to_arr("losts", n) - adj,
                 color='orange', label='Num lost %d' % n, **args)
        ax1.plot(times, to_arr("loss_detected", n)-adj,
                 color='yellow', label='Num lost detected %d' % n, **args)

        ax2.plot(times, to_arr("cwnd", n),
                 color='black', label='Cwnd %d' % n, **args)
        ax2_rate.plot(times, to_arr("rate", n),
                      color='orange', label='Rate %d' % n, **args)

    ax1.legend()
    ax2.legend()
    ax2_rtt.legend()
    ax2_rate.legend()
    plt.savefig('multi_flow_plot.svg')
    plt.show()

import argparse
from typing import Optional, Union
import z3


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
    # If false, we'll use a model that is more restrictive but does not compose
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
    # Whether AIMD can additively increase irrespective of losses. If true, the
    # the algorithm is more like cubic and has interesting failure modes
    aimd_incr_irrespective: bool

    # These config variables are calculated automatically
    calculate_qdel: bool

    # # Initial conditions (for shifting X and Y axes)
    # L0: float = 0 # free mathematically (non negative losses physical interpretation)
    # S0: float = 0 # free mathematically (free service sequence number)
    # W0: float = 0 # free mathematically (non negative waste physical interpretation)

    # @property
    # def A0(self) -> float: # derived
    #     return self.S0 + self.L0

    # @property
    # def C0(self) -> float: # derived
    #     return self.S0 + self.W0

    C0: float = 0 # free mathematically (solver will choose S[0] and W[0] such that C0 is valid)

    def __init__(self,
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
                 simplify: bool,
                 aimd_incr_irrespective: bool = False):
        self.__dict__ = locals()
        self.calculate_qdel = cca in ["copa"] or N > 1

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
        parser.add_argument(
            "--cca",
            type=str,
            default="const",
            choices=["const", "aimd", "copa", "bbr", "fixed_d"])
        parser.add_argument("--no-compose", action="store_true")
        parser.add_argument("--alpha", type=float, default=None)
        parser.add_argument("--pacing",
                            action="store_const",
                            const=True,
                            default=False)
        parser.add_argument(
            "--epsilon",
            type=str,
            default="zero",
            choices=["zero", "lt_alpha", "lt_half_alpha", "gt_alpha"])
        parser.add_argument("--unsat-core", action="store_true")
        parser.add_argument("--simplify", action="store_true")
        parser.add_argument("--aimd-incr-irrespective", action="store_true")

        return parser

    @classmethod
    def from_argparse(cls, args: argparse.Namespace):
        return cls(args.num_flows, args.D, args.rtt, args.time, args.rate,
                   args.buf_min, args.buf_max, args.dupacks, args.cca,
                   not args.no_compose, args.alpha, args.pacing, args.epsilon,
                   args.unsat_core, args.simplify, args.aimd_incr_irrespective)

    @classmethod
    def default(cls):
        return cls.from_argparse(cls.get_argparse().parse_args(args=[]))

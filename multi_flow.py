import argparse
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
from typing import Dict, List, Optional, Union
from z3 import Solver, Bool, Real, Sum, Implies, Not, And, Or, If
import z3


z3.set_param('parallel.enable', True)
z3.set_param('parallel.threads.max', 8)


def model_to_dict(model: z3.ModelRef) -> Dict[str, Union[float, bool]]:
    ''' Utility function that takes a z3 model and extracts its variables to a
    dict'''
    decls = model.decls()
    res: Dict[str, Union[float, bool]] = {}
    for d in decls:
        val = model[d]
        if type(val) == z3.BoolRef:
            res[d.name()] = bool(val)
        else:
            # Assume it is numeric
            decimal = val.as_decimal(100)
            if decimal[-1] == '?':
                decimal = decimal[:-1]
            res[d.name()] = float(decimal)
    return res


class Link:
    def __init__(
        self,
        inps: List[List[Real]],
        s: Solver,
        C: float,
        D: int,
        buf_min: Optional[float],
        compose: bool = True,
        name: str = ''
    ):
        ''' Creates a link given `inps` and return (`out`, `lost`). `inps` is
        a list of `inp`, one for each sender. If buf_min is None, there won't
        be any losses. If compose is False, a weaker model that doesn't compose
        is used '''

        assert(len(inps) > 0)
        N = len(inps)
        T = len(inps[0])

        tot_inp = [Real('tot_inp%s_%d' % (name, t)) for t in range(T)]
        outs = [[Real('out%s_%d,%d' % (name, n, t)) for t in range(T)]
                for n in range(N)]
        tot_out = [Real('tot_out%s_%d' % (name, t)) for t in range(T)]
        losts = [[Real('losts%s_%d,%d' % (name, n, t)) for t in range(T)]
                 for n in range(N)]
        tot_lost = [Real('tot_lost%s_%d' % (name, t)) for t in range(T)]
        wasted = [Real('wasted%s_%d' % (name, t)) for t in range(T)]

        if not compose:
            epsilon = Real('epsilon%s' % name)
            s.add(epsilon >= 0)

        max_dt = T
        # If qdel[t][dt] is true, it means that the bytes exiting at t were
        # input at time t - dt. If out[t] == out[t-1], then qdel[t][dt] ==
        # false forall dt. Else, exactly qdel[t][dt] == true for exactly one dt
        # If qdel[t][dt] == true then inp[t - dt - 1] < out[t] <= inp[t - dt]
        qdel = [[Bool('qdel%s_%d,%d' % (name, t, dt)) for dt in range(max_dt)]
                for t in range(T)]

        for t in range(0, T):
            # Things are monotonic
            if t > 0:
                s.add(tot_out[t] >= tot_out[t-1])
                s.add(wasted[t] >= wasted[t-1])
                # Derived from black lines are monotonic
                s.add(wasted[t] <= wasted[t-1] + C)
                s.add(tot_lost[t] >= tot_lost[t-1])
                s.add(tot_inp[t] - tot_lost[t] >= tot_inp[t-1] - tot_lost[t-1])
                for n in range(N):
                    s.add(outs[n][t] >= outs[n][t-1])
                    s.add(losts[n][t] >= losts[n][t-1])

            # Add up the totals
            s.add(tot_inp[t] == Sum(*[x[t] for x in inps]))
            s.add(tot_out[t] == Sum(*[x[t] for x in outs]))
            s.add(tot_lost[t] == Sum(*[x[t] for x in losts]))

            # Constrain out using tot_inp and the black lines
            s.add(tot_out[t] <= tot_inp[t] - tot_lost[t])
            s.add(tot_out[t] <= C * t - wasted[t])
            if t >= D:
                s.add(tot_out[t] >= C * (t - D) - wasted[t - D])
            else:
                s.add(tot_out[t] >= 0)

            # Condition when wasted is allowed to increase
            if t > 0:
                if compose:
                    s.add(Implies(
                        wasted[t] > wasted[t-1],
                        C * t - wasted[t] >= tot_inp[t] - tot_lost[t]
                    ))
                else:
                    s.add(Implies(
                        wasted[t] > wasted[t-1],
                        tot_inp[t] - tot_lost[t] <= tot_out[t] + epsilon
                    ))

            # Maximum buffer constraint
            # s.add(tot_inp[t] - tot_lost[t] - tot_out[t] <= buf_max)

            if buf_min is not None:
                # When can loss happen?
                if t > 0:
                    s.add(Implies(
                          tot_lost[t] > tot_lost[t-1],
                          tot_inp[t] - tot_lost[t] >= C*t - wasted[t] + buf_min
                          ))
                else:
                    s.add(tot_lost[t] == 0)
            else:
                s.add(tot_lost[t] == 0)

            # Figure out the time when the bytes being output at time t were
            # first input
            for dt in range(max_dt):
                if t - dt - 1 < 0:
                    s.add(qdel[t][dt] == False)
                    continue

                s.add(qdel[t][dt] == Or(
                    And(
                        tot_out[t] != tot_out[t-1],
                        And(tot_inp[t - dt - 1] - tot_lost[t - dt - 1]
                            < tot_out[t],
                            tot_inp[t - dt] - tot_lost[t - dt] >= tot_out[t])
                    ),
                    And(
                       tot_out[t] == tot_out[t-1],
                       qdel[t-1][dt]
                    )))

            # Figure out how many packets were output from each flow. Ensure
            # that out[n][t] > inp[n][t-dt-1], but leave the rest free for the
            # adversary to choose
            for n in range(N):
                for dt in range(max_dt):
                    if t - dt - 1 < 0:
                        continue
                    s.add(Implies(qdel[t][dt], outs[n][t] > inps[n][t-dt-1]))

        # Initial conditions
        s.add(wasted[0] == 0)
        s.add(tot_out[0] == 0)
        s.add(tot_lost[0] == 0)
        for n in range(N):
            s.add(outs[n][0] == 0)
            s.add(losts[n][0] == 0)

        self.tot_inp = tot_inp
        self.inps = inps
        self.outs = outs
        self.tot_out = tot_out
        self.losts = losts
        self.tot_lost = tot_lost
        self.wasted = wasted
        self.max_dt = max_dt
        self.qdel = qdel


class ModelConfig:
    N: int
    D: int
    R: int
    T: int
    C: float
    buf_min: Optional[float]
    dupacks: Optional[float]
    cca: str
    compose: bool
    alpha: Union[float, z3.ArithRef] = 1.0

    def __init__(
        self,
        N: int,
        D: int,
        R: int,
        T: int,
        C: float,
        buf_min: Optional[float],
        dupacks: Optional[float],
        cca: str,
        compose: bool,
        alpha: Optional[float] = None
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
        parser.add_argument("--dupacks", type=float, default=None)
        parser.add_argument("--cca", type=str, default="const",
                            choices=["const", "aimd", "copa", "fixed_d"])
        parser.add_argument("--no-compose", action="store_true")
        parser.add_argument("--alpha", type=float, default=None)
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
            args.dupacks,
            args.cca,
            not args.no_compose,
            args.alpha)


def make_solver(config: ModelConfig) -> z3.Solver:
    # Configuration
    N = config.N
    C = config.C
    D = config.D
    R = config.R
    T = config.T
    buf_min = config.buf_min
    dupacks = config.dupacks
    cca = config.cca
    compose = config.compose
    alpha = config.alpha

    inps = [[Real('inp_%d,%d' % (n, t)) for t in range(T)]
            for n in range(N)]
    cwnds = [[Real('cwnd_%d,%d' % (n, t)) for t in range(T)]
             for n in range(N)]
    rates = [[Real('rate_%d,%d' % (n, t)) for t in range(T)]
             for n in range(N)]
    # Number of bytes that have been detected as lost so far (per flow)
    loss_detected = [[Real('loss_detected_%d,%d' % (n, t)) for t in range(T)]
                     for n in range(N)]

    s = Solver()
    lnk = Link(inps, s, C, D, buf_min, compose=compose, name='')

    if dupacks is None:
        dupacks = Real('dupacks')
        s.add(dupacks >= 0)
    if alpha is None:
        alpha = Real('alpha')
        s.add(alpha > 0)

    # Figure out when we can detect losses
    max_loss_dt = T
    for n in range(N):
        for t in range(T):
            for dt in range(max_loss_dt):
                if t > 0:
                    s.add(loss_detected[n][t] >= loss_detected[n][t-1])
                if t - R - dt < 0:
                    continue
                detectable = lnk.inps[n][t-R-dt] + dupacks <= lnk.outs[n][t-R]
                s.add(Implies(
                    detectable,
                    loss_detected[n][t] >= lnk.losts[n][t - R - dt]
                ))
                s.add(Implies(
                    Not(detectable),
                    loss_detected[n][t] <= lnk.losts[n][t - R - dt]
                ))
            s.add(loss_detected[n][t] <= lnk.losts[n][t - R])
        for t in range(R):
            s.add(loss_detected[n][t] == 0)

    # Set inps based on cwnds and rates
    for t in range(T):
        for n in range(N):
            # Max value due to cwnd
            if t >= R:
                inp_w = lnk.outs[n][t - R] + loss_detected[n][t] + cwnds[n][t]
            else:
                inp_w = cwnds[n][t]
            if t > 0:
                inp_w = If(inp_w < inps[n][t-1], inps[n][t-1], inp_w)

            # Max value due to rate
            if t > 0:
                inp_r = inps[n][t-1] + rates[n][t]
            else:
                inp_r = 0

            # Max of the two values
            s.add(inps[n][t] == If(inp_w < inp_r, inp_w, inp_r))

    # Congestion control
    if cca == "const":
        for n in range(N):
            for t in range(T):
                s.add(cwnds[n][t] == C * (R + D))
                s.add(rates[n][t] == C * 10)
    elif cca == "aimd":
        # The last send sequence number at which a loss was detected
        last_loss = [[Real('last_loss_%d,%d' % (n, t)) for t in range(T)]
                     for n in range(N)]
        for n in range(N):
            s.add(cwnds[n][0] > 0)
            s.add(last_loss[n][0] == 0)
            for t in range(T):
                s.add(rates[n][t] == C * 10)
                if t > 0:
                    decrease = And(
                        loss_detected[n][t] > loss_detected[n][t-1],
                        last_loss[n][t-1] <= lnk.outs[n][t-R]
                    )
                    s.add(Implies(decrease,
                                  last_loss[n][t] == lnk.inps[n][t] + dupacks))
                    s.add(Implies(Not(decrease),
                                  last_loss[n][t] == last_loss[n][t-1]))

                    s.add(Implies(decrease, cwnds[n][t] == cwnds[n][t-1] / 2))
                    s.add(Implies(Not(decrease),
                                  cwnds[n][t] == cwnds[n][t-1] + alpha))
    elif cca == "fixed_d":
        # ack_rate = [[Real("ack_rate_%d,%d" % (n, t)) for t in range(T)]
        #             for n in range(N)]
        for n in range(N):
            for t in range(T):
                diff = R + 2 * D
                if t - R - diff < 0:
                    s.add(cwnds[n][t] <= 40.)
                    s.add(cwnds[n][t] >= 6.)
                    s.add(rates[n][t] == cwnds[n][t] / R)
                else:
                    # for dt in range(lnk.max_dt):
                    #     if t - dt - R - 1 >= 0:
                    #         s.add(Implies(lnk.qdel[t-1][dt], ack_rate[n][t]
                    #               == (1. / (dt + R))
                    #               * (lnk.outs[n][t-1] - lnk.outs[n][t-dt-R-1])))
                    # cwnd = ack_rate[n][t] * (R + D) + 1
                    cwnd = lnk.outs[n][t - R] - lnk.outs[n][t - R - diff] + 1
                    s.add(cwnds[n][t] == If(cwnd < 1., 1., cwnd))
                    s.add(rates[n][t] == cwnds[n][t] / R)
    elif cca == "copa":
        for n in range(N):
            for t in range(T):
                if t - R - D < 0:
                    s.add(cwnds[n][t] <= C * R * 2)
                    s.add(cwnds[n][t] > 0)
                else:
                    incr_alloweds, decr_alloweds = [], []
                    for dt in range(lnk.max_dt):
                        # Whether we are allowd to increase/decrease
                        incr_allowed = Bool("incr_allowed_%d,%d,%d" % (n, t, dt))
                        decr_allowed = Bool("decr_allowed_%d,%d,%d" % (n, t, dt))
                        # Warning: Adversary here is too powerful if D > 1. Add
                        # a constraint for every point between t-1 and t-1-D
                        assert(D == 1)
                        s.add(incr_allowed
                              == And(
                                  lnk.qdel[t-R][dt],
                                  cwnds[n][t] * max(0, dt-D) <= alpha*(R+dt)))
                        s.add(decr_allowed
                              == And(
                                  lnk.qdel[t-R-D][dt],
                                  cwnds[n][t] * dt >= alpha * (R + dt)))
                        incr_alloweds.append(incr_allowed)
                        decr_alloweds.append(decr_allowed)
                    incr_allowed = Or(*incr_alloweds)
                    decr_allowed = Or(*decr_alloweds)

                    # Either increase or decrease cwnd
                    incr = Bool("incr_%d,%d" % (n, t))
                    decr = Bool("decr_%d,%d" % (n, t))
                    s.add(Or(
                        And(incr, Not(decr)),
                        And(Not(incr), decr)))
                    s.add(Implies(incr, incr_allowed))
                    s.add(Implies(decr, decr_allowed))
                    s.add(Implies(incr, cwnds[n][t] == cwnds[n][t-1]+alpha/R))
                    sub = cwnds[n][t-1] - alpha / R
                    s.add(Implies(decr, cwnds[n][t] == If(sub < 0, 0, sub)))

                    # Basic constraints
                    s.add(cwnds[n][t] > 0)
                # Pacing
                # s.add(rates[n][t] == cwnds[n][t] / R)
                s.add(rates[n][t] == 50)
    else:
        print("Unrecognized cca")
        exit(1)
    return s


def plot_model(m: Dict[str, Union[float, bool]], cfg: ModelConfig):
    def to_arr(name: str, n: Optional[int] = None) -> np.array:
        if n is None:
            return np.asarray([m["%s_%d" % (name, t)] for t in range(cfg.T)])
        else:
            return np.asarray([m["%s_%d,%d" % (name, n, t)]
                               for t in range(cfg.T)])

    # Print the constants we picked
    if cfg.dupacks is None:
        print("dupacks = ", m["dupacks"])
    if cfg.cca == "copa" and cfg.alpha is None:
        print("alpha = ", m["alpha"])

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
             color='black', marker='o', label='Bound')
    ax1.plot(times[cfg.D:],
             (ct - to_arr("wasted"))[:-cfg.D], color='black', marker='o')
    ax1.plot(times, to_arr("tot_out"),
             color='red', marker='o', label='Total Egress')
    ax1.plot(times, to_arr("tot_inp"),
             color='blue', marker='o', label='Total Ingress')

    # Calculate RTT (misnomer. Really just qdel)
    rtts = []
    for t in range(cfg.T):
        rtt = None
        for dt in range(cfg.T):
            if m["qdel_%d,%d" % (t, dt)]:
                assert(rtt is None)
                rtt = dt
        rtts.append(rtt)
    ax2_rtt.plot(times, rtts,
                 color='blue', marker='o', label='RTT')

    for n in range(cfg.N):
        args = {'marker': 'o', 'linestyle': linestyles[n]}

        ax1.plot(times, to_arr("out", n) - adj,
                 color='red', label='Egress %d' % n, **args)
        ax1.plot(times, to_arr("inp", n) - adj,
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


if __name__ == "__main__":
    cfg = ModelConfig(
        N=1,
        D=1,
        R=2,
        T=20,
        C=5,
        buf_min=None,
        dupacks=0.125,
        cca="copa",
        compose=False,
        alpha=1.0)
    s = make_solver(cfg)

    # Query constraints

    # Cwnd too small
    s.add(Real("cwnds_0,%d" % (cfg.T-1)) <= cfg.C * cfg.R - cfg.C)

    s.add(Real("tot_lost_%d" % (cfg.T-1)) == 0)

    # Run the model
    satisfiable = s.check()
    print(satisfiable)
    if str(satisfiable) != 'sat':
        exit()
    m = s.model()
    m = model_to_dict(m)

    plot_model(m, cfg)

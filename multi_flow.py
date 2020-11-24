import matplotlib
import matplotlib.pyplot as plt
import numpy as np
from typing import List, Optional
from z3 import Solver, Bool, Real, Sum, Implies, Not, And, Or, If
import z3


z3.set_param('parallel.enable', True)
z3.set_param('parallel.threads.max', 8)


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
                        tot_inp[t] == tot_out[t]
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

            # Figure out the time when the bytes being output at time t were
            # first input
            for dt in range(max_dt):
                if t - dt - 1 < 0:
                    s.add(qdel[t][dt] == False)
                    continue

                # if dt == 0:
                #     s.add(qdel[t][0] == (tot_inp[t] == tot_out[t]))
                #     continue

                s.add(qdel[t][dt] == Or(
                    And(
                        tot_out[t] != tot_out[t-1],
                        And(tot_inp[t - dt - 1] < tot_out[t],
                            tot_inp[t - dt] >= tot_out[t])
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
        # s.add(qdel[0] == False)
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


# Configuration
N = 1
C = 5
D = 1
R = 2
T = 20
buf_min = None
dupacks = 0.125
cca = "copa"
compose = False
alpha = 1  # Real("alpha")

inps = [[Real('inp_%d,%d' % (n, t)) for t in range(T)]
        for n in range(N)]
cwnds = [[Real('cwnd%d,%d' % (n, t)) for t in range(T)]
         for n in range(N)]
rates = [[Real('rates%d,%d' % (n, t)) for t in range(T)]
         for n in range(N)]
# Number of bytes that have been detected as lost so far (per flow)
loss_detected = [[Real('loss_detected%d,%d' % (n, t)) for t in range(T)]
                 for n in range(N)]

s = Solver()
lnk = Link(inps, s, C, D, buf_min, '')

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
            s.add(cwnds[n][t] == C * R)
            s.add(rates[n][t] == C * 10)
elif cca == "aimd":
    # The last send sequence number at which a loss was detected
    last_loss = [[Real('last_loss_%d,%d' % (n, t)) for t in range(T)]
                 for n in range(N)]
    for n in range(N):
        s.add(cwnds[n][0] == 1)
        s.add(last_loss[n][0] == 0)
        for t in range(T):
            s.add(rates[n][t] == C * 10)
            if t > 0:
                decrease = And(
                    loss_detected[n][t] > loss_detected[n][t-1],
                    last_loss[n][t-1] <= lnk.outs[n][t-R]
                )
                s.add(Implies(decrease, last_loss[n][t] == lnk.inps[n][t]))
                s.add(Implies(Not(decrease),
                              last_loss[n][t] == last_loss[n][t-1]))

                s.add(Implies(decrease, cwnds[n][t] == cwnds[n][t-1] / 2))
                s.add(Implies(Not(decrease), cwnds[n][t] == cwnds[n][t-1] + 1))
elif cca == "fixed_d":
    ack_rate = [[Real("ack_rate_%d,%d" % (n, t)) for t in range(T)]
                for n in range(N)]
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
    alpha = 2 * C * D + 1
    q_standing = [[Real("q_standing_%d,%d" % (n, t)) for t in range(T)]
                  for n in range(N)]
    for n in range(N):
        for t in range(T):
            diff = D
            if t - R - diff < 0:
                s.add(cwnds[n][t] <= C * R * 2)
                s.add(cwnds[n][t] > 0)
            else:
                incr_alloweds, decr_alloweds = [], []
                for dt in range(lnk.max_dt):
                    # Whether we are allowd to increase/decrease
                    incr_allowed = Bool("incr_allowed_%d,%d,%d" % (n, t, dt))
                    decr_allowed = Bool("decr_allowed_%d,%d,%d" % (n, t, dt))
                    # Warning: Adversary here is too powerful. Add a constraint
                    # for every point between t-1 and t-1-diff
                    s.add(Implies(
                        And(lnk.qdel[t-1][dt],
                            cwnds[n][t] * max(0, dt-diff) <= alpha * (R + dt)),
                        incr_allowed))
                    s.add(Implies(
                        And(lnk.qdel[t-1-diff][dt],
                            cwnds[n][t] * dt >= alpha * (R + dt)),
                        decr_allowed))
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
                s.add(Implies(incr, cwnds[n][t] == cwnds[n][t-1] + alpha / R))
                sub = cwnds[n][t-1] - alpha / R
                s.add(Implies(decr, cwnds[n][t] == If(sub < 0, 0, sub)))

                # Basic constraints
                s.add(cwnds[n][t] > 0)
            # Pacing
            s.add(rates[n][t] == 3 * cwnds[n][t] / R)
            #s.add(rates[n][t] == 50)

else:
    print("Unrecognized cca")
    exit(1)

# Query constraints

# Cwnd too small
# s.add(cwnds[0][-1] < C * R / 2)

# Wastage possible
s.add(lnk.tot_inp[-1] < C * t - lnk.wasted[t] - 1)

# Lots of waste happening
# s.add(lnk.wasted[t] > 80)

# Find maximum burst size in 1 RTT. Useful for setting the bound on unfairness
# according to total bytes output
# s.add(inps[0][-1] - inps[0][-1-R] > 12)

# Too unfair according to total bytes output. Should be fair in the period that
# they can choose whatever cwnd they want
# s.add(lnk.outs[0][2*R + 2*D] == lnk.outs[1][2*R + 2*D])
# s.add(inps[0][2*R + 2*D] == inps[1][2*R + 2*D])
# s.add(lnk.outs[0][-1] <= lnk.outs[1][-1] / 2)

# Too unfair according to final cwnd
# s.add(cwnds[0][-1] - cwnds[1][-1] > 5)


s.add(lnk.tot_lost[-1] == 0)

# Run the model
satisfiable = s.check()
print(satisfiable)
if str(satisfiable) != 'sat':
    exit()
m = s.model()


def convert(vars: List[Real]) -> np.array:
    res = []
    for var in vars:
        decimal = m[var].as_decimal(100)
        if decimal[-1] == '?':
            decimal = decimal[:-1]
        res.append(float(decimal))
    return np.asarray(res)


# Configure the plotting
fig, (ax1, ax2) = plt.subplots(2, 1, sharex=True)
fig.set_size_inches(18.5, 10.5)
ax1.grid(True)
ax2.grid(True)
ax2.set_xticks(range(0, T))
ax2.yaxis.set_major_locator(matplotlib.ticker.MaxNLocator(integer=True))
linestyles = ['--', ':', '-.', '-']
adj = 0  # np.asarray([C * t for t in range(T)])
times = [t for t in range(T)]
ct = np.asarray([C * t for t in range(T)])

ax1.plot(times, ct - convert(lnk.wasted),
         color='black', marker='o', label='Bound')
ax1.plot(times[D:],
         (ct - convert(lnk.wasted))[:-D], color='black', marker='o')
ax1.plot(times, convert(lnk.tot_out),
         color='red', marker='o', label='Total Egress')
ax1.plot(times, convert(lnk.tot_inp),
         color='blue', marker='o', label='Total Ingress')

# Calculate RTT (misnomer. Really just qdel)
rtts = []
for t in range(T):
    rtt = None
    for dt in range(lnk.max_dt):
        if z3.is_true(m[lnk.qdel[t][dt]]):
            assert(rtt is None)
            rtt = dt
    rtts.append(rtt)
ax2.plot(times, rtts,
         color='blue', marker='o', label='RTT')

for n in range(N):
    args = {'marker': 'o', 'linestyle': linestyles[n]}

    ax1.plot(times, convert(lnk.outs[n]) - adj,
             color='red', label='Egress %d' % n, **args)
    ax1.plot(times, convert(inps[n]) - adj,
             color='blue', label='Ingress %d' % n, **args)

    ax1.plot(times, convert(lnk.losts[n]) - adj,
             color='orange', label='Num lost %d' % n, **args)
    ax1.plot(times, convert(loss_detected[n])-adj,
             color='yellow', label='Num lost detected %d' % n, **args)

    ax2.plot(times, convert(cwnds[n]),
             color='black', label='Cwnd %d' % n, **args)
    ax2.plot(times, convert(rates[n]),
             color='orange', label='Rate %d' % n, **args)

ax1.legend()
ax2.legend()
plt.savefig('multi_flow_plot.svg')
plt.show()

from config import ModelConfig
from my_solver import MySolver


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
        self.timeout_f = [[s.Bool(f"timeout_{n},{t}") for t in range(T)]
                          for n in range(c.N)]

        # If qdel[t][dt] is true, it means that the bytes exiting at t were
        # input at time t - dt. If out[t] == out[t-1], then qdel[t][dt] ==
        # qdel[t-1][dt], since qdel isn't really defined (since no packets were
        # output), so we default to saying we experience the RTT of the last
        # received packet.
        if c.calculate_qdel:
            self.qdel = [[s.Bool('qdel_%d,%d' % (t, dt)) for dt in range(T)]
                         for t in range(T)]

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

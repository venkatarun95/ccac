import unittest
from z3 import And, If, Implies, Not, Or

from model import Variables
from model_utils import ModelConfig
from my_solver import MySolver
from typing import Tuple


class BBRVariables:
    ''' Variables for BBR that are used globally '''

    def __init__(self, c: ModelConfig, s: MySolver):
        # BBR's state machine state at the beginning of the time slot
        self.state_f = [[s.Int(f"bbr_state_{n},{t}") for t in range(c.T)]
                        for n in range(c.N)]
        # Number of RTTs since the beginning
        self.nrtts_f = [[s.Int(f"nrtts_{n},{t}") for t in range(c.T)]
                      for n in range(c.N)]
        # Estimated ack arrival rate
        self.r_est_f = [[s.Real(f"bbr_rate_est_{n},{t}") for t in range(c.T)]
                        for n in range(c.N)]
        # The maximum ack rate estimate over the last 10 RTTs
        self.r_max_f = [[s.Real(f"bbr_max_rate_est_{n},{t}") for t in range(c.T)]
                        for n in range(c.N)]
        # A(t) at the last RTT switch (notice, time is continuous)
        self.last_A_f = [[s.Real(f"bbr_last_arrival_{n},{t}") for t in range(c.T)]
                         for n in range(c.N)]
        # S(t-R) at the last switch
        self.last_S_f = [[s.Real(f"bbr_last_service_{n},{t}") for t in range(c.T)]
                         for n in range(c.N)]


def cca_bbr_state(b: BBRVariables, c: ModelConfig, s: MySolver, v: Variables):
    ''' Figure out when RTTs end and update BBR's state '''
    for n in range(c.N):
        # Initial state is unconstrained

        # This is guaranteed to be greater than S_f at 0, because if it
        # weren't, the RTT would already be over
        s.add(b.last_A_f[n][0] >= v.S_f[n][0])
        # It certainly cannot be greater than the packet we sent just now!
        s.add(b.last_A_f[n][0] <= v.A_f[n][0])

        # S_f is monotonic
        s.add(b.last_S_f[n][0] <= v.S_f[n][0])
        # Lower bound on S_f at t < 0 cannot increase faster than rate C
        s.add(b.last_S_f[n][0] <= -c.C * c.T - v.W[0])

        s.add(b.nrtts_f[n][0] == 0)
        for t in range(1, c.T):
            # Let us say that the RTT always starts within 1 queuing delay of
            # time 0, so it never terminates before t = R
            if t < c.R:
                ended = False
            else:
                assert(c.R > 0)
                ended = v.S_f[n][t-c.R] >= b.last_A_f[n][t-1]
            s.add(Implies(
                ended,
                And(b.last_A_f[n][t] > v.A_f[n][t-1],
                    b.last_A_f[n][t] <= v.A_f[n][t],
                    b.state_f[n][t] == If(b.state_f[n][t-1] == 3,
                                          0,
                                          b.state_f[n][t-1] + 1),
                    b.nrtts_f[n][t] == b.nrtts_f[n][t-1] + 1)))
            s.add(Implies(
                Not(ended),
                And(b.last_A_f[n][t] == b.last_A_f[n][t-1],
                    b.state_f[n][t] == b.state_f[n][t-1],
                    b.nrtts_f[n][t] == b.nrtts_f[n][t-1],
                    b.last_S_f[n][t] == b.last_S_f[n][t-1])))

            if t > c.R:
                s.add(Implies(
                    ended,
                    And(
                        b.last_S_f[n][t] > v.S_f[n][t-c.R-1],
                        b.last_S_f[n][t] <= v.S_f[n][t-c.R])))
            else:
                assert(t == c.R)
                s.add(Implies(
                    ended,
                    And(
                        b.last_S_f[n][t] > v.S_f[n][0] - c.C,
                        b.last_S_f[n][t] <= v.S_f[n][t-c.R])))



def cca_bbr_rate_est(b: BBRVariables, c: ModelConfig, s: MySolver, v: Variables):
    ''' Estimate the ack arrival rate '''
    for n in range(c.N):
        # Initial rate estimate is unconstrained
        for t1 in range(1, c.T):
            for t0 in range(1, t1):
                # If [t0, t1) is 1 RTT, then estimate rate for this period
                is_rtt = And(
                    b.last_A_f[n][t0] == b.last_A_f[n][t1-1],
                    b.last_A_f[n][t0] != b.last_A_f[n][t0-1],
                    b.last_A_f[n][t1] != b.last_A_f[n][t1-1])
                s.add(Implies(
                    is_rtt,
                    And(b.r_est_f[n][t1] >= (v.A_f[n][t1-1] - v.A_f[n][t0]) / max(c.R, t1 - t0 - 1),
                        b.r_est_f[n][t1] <= (v.A_f[n][t1] - v.A_f[n][t0-1]) / (t1 - t0 + 1))))

            # If this was not an end of an RTT, then maintain the same rate
            # estimate as before
            s.add(Implies(
                b.last_A_f[n][t1] == b.last_A_f[n][t1-1],
                b.r_est_f[n][t1] == b.r_est_f[n][t1-1]
            ))


def cca_bbr_max_rate(b: BBRVariables, c: ModelConfig, s: MySolver, v: Variables):
    for n in range(c.N):
        s.add(b.r_max_f[n][0] >= b.r_est_f[n][0])
        for t in range(1, c.T):
            maxes = [s.Real(f"bbr_maxes_{n},{t},{dt}") for dt in range(0, t)]
            s.add(maxes[0] == b.r_est_f[n][t])
            for dt in range(1, t):
                win = b.nrtts_f[n][t] - b.nrtts_f[n][t-dt] < 10
                s.add(Implies(
                    win,
                    maxes[dt] == If(
                        maxes[dt-1] > b.r_est_f[n][t-dt],
                        maxes[dt-1],
                        b.r_est_f[n][t-dt])))
                s.add(Implies(Not(win), maxes[dt] == maxes[dt-1]))
            s.add(b.r_max_f[n][t] == maxes[-1])


def cca_bbr(c: ModelConfig, s: MySolver, v: Variables):
    b = BBRVariables(c, s)
    cca_bbr_state(b, c, s, v)
    cca_bbr_rate_est(b, c, s, v)
    cca_bbr_max_rate(b, c, s, v)

    for n in range(c.N):
        for t in range(c.T):
            pass


class TestBBR(unittest.TestCase):
    @staticmethod
    def util_net_without_cca(c: ModelConfig) -> Tuple[BBRVariables, MySolver, Variables]:
        from model import monotone, initial, relate_tot, network
        c.cca = "bbr"
        s = MySolver()
        v = Variables(c, s)
        b = BBRVariables(c, s)

        monotone(c, s, v)
        initial(c, s, v)
        relate_tot(c, s, v)
        network(c, s, v)
        return (b, s, v)

    def test_bbr_state_rtt_gt_R(self):
        for R in [2, 3]:
            c = ModelConfig.default()
            c.R = R
            b, s, v = TestBBR.util_net_without_cca(c)
            cca_bbr_state(b, c, s, v)

            # RTT cannot be shorter than R!
            conds = []
            for t in range(R, c.T):
                conds.append(And(
                    b.state_f[0][t] != b.state_f[0][t-1],
                    b.state_f[0][t-R+1] != b.state_f[0][t-R+1-1]))
                conds.append(And(
                    b.state_f[0][t] != b.state_f[0][t-1],
                    b.last_A_f[0][t] == b.last_A_f[0][t-1]))
            s.add(Or(*conds))

            sat = s.check()

            self.assertEqual(str(sat), "unsat")

    def test_bbr_state_large_init_rtt(self):
        c = ModelConfig.default()
        c.T = 10
        b, s, v = TestBBR.util_net_without_cca(c)
        cca_bbr_state(b, c, s, v)

        # We can have really large RTTs if the initial queuing delay is large
        s.add(b.last_A_f[0][0] == b.last_A_f[0][-1])
        sat = s.check()

        # from model_utils import model_to_dict, plot_model
        # m = model_to_dict(s.model())
        # for t in range(c.T):
        #     print(t, m[f"bbr_state_0,{t}"], m[f"bbr_last_arrival_0,{t}"])
        # plot_model(m, c)

        self.assertEqual(str(sat), "sat")

    def test_bbr_state_large_mid_rtt(self):
        c = ModelConfig.default()
        c.T = 10
        b, s, v = TestBBR.util_net_without_cca(c)
        cca_bbr_state(b, c, s, v)

        # The initial RTT may be small, but it grows bigger
        s.add(b.last_A_f[0][0] != b.last_A_f[0][3])
        s.add(b.last_A_f[0][3] == b.last_A_f[0][-1])
        sat = s.check()

        self.assertEqual(str(sat), "sat")

    def test_bbr_rate_est(self):
        c = ModelConfig.default()
        b, s, v = TestBBR.util_net_without_cca(c)
        cca_bbr_state(b, c, s, v)
        cca_bbr_rate_est(b, c, s, v)

        # There should be some rate estimate below and above the overall rate
        rate = (v.S_f[0][c.T-c.R] - v.S_f[0][0]) / (c.T - 1 - c.R)
        s.add(Or(
            And(*[
                b.r_est_f[0][t] < rate for t in range(c.T)
            ]),
            And(*[
                b.r_est_f[0][t] > rate for t in range(c.T)
            ])))

        sat = s.check()

        print(sat)
        from model_utils import model_to_dict, plot_model
        m = model_to_dict(s.model())
        for t in range(c.T):
            print(t, m[f"bbr_state_0,{t}"], m[f"bbr_last_arrival_0,{t}"], m[f"bbr_rate_est_0,{t}"])
        plot_model(m, c)

        self.assertEqual(str(sat), "unsat")


if __name__ == "__main__":
    unittest.main()

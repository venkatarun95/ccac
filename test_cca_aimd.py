import unittest
from z3 import And, Not, Or

from model import Variables, cwnd_rate_arrival, epsilon_alpha,\
    initial, loss_detected, monotone, network, relate_tot
from cca_aimd import AIMDVariables, can_incr, cca_aimd
from config import ModelConfig
from pyz3_utils import MySolver


class TestCCAAimd(unittest.TestCase):
    def test_can_incr(self):
        def create():
            c = ModelConfig.default()
            c.aimd_incr_irrespective = False
            c.simplify = True
            s = MySolver()
            v = Variables(c, s)

            monotone(c, s, v)
            initial(c, s, v)
            relate_tot(c, s, v)
            network(c, s, v)
            loss_detected(c, s, v)
            epsilon_alpha(c, s, v)
            cwnd_rate_arrival(c, s, v)
            return (c, s, v)

        # There exists a network trace where cwnd can increase
        c, s, v = create()
        cv = AIMDVariables(c, s)
        can_incr(c, s, v, cv)
        s.add(Or(*[cv.incr_f[0][t] for t in range(c.T)]))
        sat = s.check()
        self.assertEqual(str(sat), "sat")

        # If S increases enough, cwnd will always increase
        c, s, v = create()
        cv = cca_aimd(c, s, v)
        conds = []
        for t in range(4, 5):  # range(1, c.T):
            conds.append(And(
                v.S[t] - v.S[t-1] >= v.c_f[0][t],
                Not(cv.incr_f[0][t])))
        s.add(Or(*conds))
        sat = s.check()
        self.assertEqual(str(sat), "unsat")


if __name__ == '__main__':
    unittest.main()

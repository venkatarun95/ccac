import unittest
from z3 import And, Implies, Or

from config import ModelConfig
from model import Variables, calculate_qdel, initial, monotone, make_solver, \
    network, relate_tot
from pyz3_utils import MySolver


class TestModel(unittest.TestCase):
    def test_tot_inp_out(self):
        for N in [1, 2]:
            c = ModelConfig.default()
            c.N = N
            s = MySolver()
            v = Variables(c, s)
            monotone(c, s, v)
            relate_tot(c, s, v)

            conds = []
            for t in range(1, c.T):
                conds.append(v.A[t] < v.A[t-1])
                conds.append(v.L[t] < v.L[t-1])
                conds.append(v.S[t] < v.S[t-1])
                conds.append(v.A[t] - v.L[t]
                             < v.A[t-1] - v.L[t-1])
            s.add(Or(*conds))

            sat = s.check()
            self.assertEqual(str(sat), "unsat")

    def test_service_extreme(self):
        def csv():
            c = ModelConfig.default()
            s = MySolver()
            v = Variables(c, s)
            monotone(c, s, v)
            network(c, s, v)
            return (c, s, v)

        c, s, v = csv()
        s.add(v.S[c.T-1] - v.S[0] > c.C * c.T)
        sat = s.check()
        self.assertEqual(str(sat), "unsat")

        c, s, v = csv()
        s.add(v.S[c.T-1] - v.S[0] == c.C * c.T)
        sat = s.check()
        self.assertEqual(str(sat), "sat")

        c, s, v = csv()
        s.add(v.S[c.T-1] - v.S[0] < 0)
        sat = s.check()
        self.assertEqual(str(sat), "unsat")

        c, s, v = csv()
        s.add(v.S[c.T-1] - v.S[0] == 0)
        sat = s.check()
        self.assertEqual(str(sat), "sat")

    def test_cca_const(self):
        c = ModelConfig.default()
        c.cca = "const"
        for cwnd in [c.C * c.R / 2, c.C * c.R, 2 * c.C * c.R, 3 * c.C * c.R]:
            util_bound = max((c.T-1) * cwnd / (c.R + c.D), c.T*c.C)
            c.alpha = cwnd

            s, v = make_solver(c)
            s.add(v.S[c.T-1] - v.S[0] > util_bound)
            s.add(v.A[0] == v.S[0])
            sat = s.check()
            self.assertEqual(str(sat), "unsat")

            s, v = make_solver(c)
            s.add(v.S[c.T-1] - v.S[0] <= util_bound)
            s.add(v.A[0] == v.S[0])
            sat = s.check()
            self.assertEqual(str(sat), "sat")

    def test_qdel(self):
        c = ModelConfig.default()
        c.calculate_qdel = True
        s = MySolver()
        v = Variables(c, s)

        monotone(c, s, v)
        initial(c, s, v)
        relate_tot(c, s, v)
        network(c, s, v)
        calculate_qdel(c, s, v)

        # The only case where two dt s can be true at the same time is when we
        # don't get any fresh acks
        conds = []
        for t in range(c.T):
            for dt1 in range(c.T):
                for dt2 in range(c.T):
                    if dt1 == dt2:
                        continue
                    conds.append(And(v.qdel[t][dt1], v.qdel[t][dt2]))
                    # s.add(Implies(
                    #     And(v.qdel[t][dt1], v.qdel[t][dt2]),
                    #     v.S[t]))
        s.add(Or(*conds))
        sat = s.check()

        self.assertEqual(str(sat), "unsat")


if __name__ == '__main__':
    unittest.main()

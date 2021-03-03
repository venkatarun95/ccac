import unittest
from clean_output import LinearVars, eval_smt, anded_constraints, \
    get_linear_vars, substitute_if
from z3 import And, Bool, If, Implies, Or, Real, Solver


class TestCleanOutput(unittest.TestCase):
    def test_eval_smt(self):
        s = Solver()
        s.add(Real('a') < Real('b'))
        s.add(Implies(Bool('x'), Real('a') > Real('b')))
        s.add(Or(Bool('x'), Bool('y')))

        self.assertFalse(eval_smt({"a": 0, "b": 1, "x": False, "y": False},
                         s.assertions()))
        self.assertFalse(eval_smt({"a": 0, "b": 1, "x": True, "y": False},
                         s.assertions()))
        self.assertTrue(eval_smt({"a": 0, "b": 1, "x": False, "y": True},
                        s.assertions()))

    def test_anded_constraints(self):
        s = Solver()
        e1 = Real("a") < Real("b")
        e2 = Real("b") + Real("c") >= Real("a")
        e3 = Real("a") == 100
        e4 = Real("b") > 101
        e5 = Real("a") <= 1
        e6 = Real("a") + 2 > Real("b")
        s.add(And(e1, e2))
        s.add(Implies(e3, e4))
        s.add(Or(e5, e6))

        # self.assertEqual(
        #     set(anded_constraints({"a": 0, "b": 1, "c": -1},
        #                           s.assertions())),
        #     set([e1, e2, e5]))
        # self.assertEqual(
        #     set(anded_constraints({"a": 1, "b": 2, "c": 0},
        #                           s.assertions())),
        #     set([e1, e2, e5]))
        # self.assertEqual(
        #     set(anded_constraints({"a": 100, "b": 101.5, "c": -0.5},
        #                           s.assertions())),
        #     set([e1, e2, e3, e4, e6]))

    def test_get_linear_vars(self):
        self.assertEqual(
            get_linear_vars(Real("a") + 2 * Real("b") - 1),
            LinearVars({"a": 1.0, "b": 2.0}, -1.0)
        )

        self.assertEqual(
            get_linear_vars(Real("a") + 0.5 - (Real("c") + 2 * Real("b")) - 1),
            LinearVars({"a": 1, "b": -2, "c": -1}, -0.5)
        )

    def test_substitute_if(self):
        e = If(Real("a") < Real("b"), Real("a"), Real("b"))
        self.assertEqual(
            substitute_if({"a": 0, "b": 1}, e),
            (Real("a"), [Real("a") < Real("b")])
        )
        self.assertEqual(
            substitute_if({"a": 1, "b": 0}, e),
            (Real("b"), [Real("a") < Real("b")])
        )
        self.assertEqual(
            substitute_if({"a": 1, "b": 1}, Real("c") == e),
            (Real("c") == Real("b"), [Real("a") < Real("b")])
        )
        self.assertEqual(
            substitute_if({"a": 1, "b": 1}, Real("a") + Real("b") >= 0),
            (Real("a") + Real("b") >= 0, [])
        )


if __name__ == "__main__":
    unittest.main()

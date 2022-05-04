''' Take SMT output and clean it up, trying to remove the clutter and leave
behind only the essential details for why the counter-example works '''

from config import ModelConfig
from copy import copy, deepcopy
from fractions import Fraction
from functools import reduce
from pyz3_utils import ModelDict, extract_vars
import numpy as np
import operator
from scipy.optimize import LinearConstraint, minimize
from typing import Any, Dict, List, Set, Tuple, Union
from z3 import And, ArithRef, AstVector, BoolRef, IntNumRef, Not,\
    RatNumRef, substitute


Expr = Union[BoolRef, ArithRef]


def eval_smt(m: ModelDict, a: Expr) -> Union[Fraction, bool]:
    if type(a) is AstVector:
        a = And(a)

    decl = str(a.decl())
    children = [eval_smt(m, x) for x in a.children()]

    if len(children) == 0:
        if type(a) is ArithRef:
            return m[str(a)]
        elif type(a) is RatNumRef:
            return a.as_fraction()
        elif decl == "Int":
            return a.as_long()
        elif str(a.decl()) == "True":
            return True
        elif str(a.decl()) == "False":
            return False
        elif type(a) is BoolRef:
            return m[str(a)]

    if decl == "Not":
        assert(len(a.children()) == 1)
        return not children[0]
    if decl == "And":
        return all(children)
    if decl == "Or":
        return any(children)
    if decl == "Implies":
        assert(len(a.children()) == 2)
        if children[0] is True and children[1] is False:
            return False
        else:
            return True
    if decl == "If":
        assert(len(a.children()) == 3)
        if children[0] is True:
            return children[1]
        else:
            return children[2]
    if decl == "+":
        return sum(children, start=Fraction(0))
    if decl == "-":
        if len(a.children()) == 2:
            return children[0] - children[1]
        elif len(a.children()) == 1:
            return -children[0]
        else:
            assert(False)
    if decl == "*":
        return reduce(operator.mul, children, 1)
    if decl == "/":
        assert(len(children) == 2)
        return children[0] / children[1]
    if decl == "<":
        assert(len(a.children()) == 2)
        return children[0] < children[1]
    if decl == "<=":
        assert(len(a.children()) == 2)
        return children[0] <= children[1]
    if decl == ">":
        assert(len(a.children()) == 2)
        return children[0] > children[1]
    if decl == ">=":
        assert(len(a.children()) == 2)
        return children[0] >= children[1]
    if decl == "==":
        assert(len(a.children()) == 2)
        return children[0] == children[1]
    if decl == "Distinct":
        assert(len(a.children()) == 2)
        return children[0] != children[1]
    print(f"Unrecognized decl {decl} in {a}")
    exit(1)


def substitute_if(
        m: ModelDict,
        a: BoolRef) -> Tuple[BoolRef, List[BoolRef]]:
    ''' Substitute any 'If(c, t, f)' expressions with 't' if 'c' is true under
    'm' and with 'f' otherwise. Also returns a list of 'c's from all the 'If's,
    since they need to be asserted true as well '''

    # The set of 'c's for 'If's
    conds = []
    res = deepcopy(a)
    # BFS queue
    if type(res) == AstVector:
        res = And(res)
    queue = [res]
    while len(queue) > 0:
        cur = queue[0]
        queue = queue[1:]
        if str(cur.decl()) == "If":
            assert(len(cur.children()) == 3)
            c, t, f = cur.children()
            if eval_smt(m, c):
                res = substitute(res, (cur, t))
                queue.append(t)
                c, new_conds = substitute_if(m, c)
                conds.append(c)
                conds.extend(new_conds)
            else:
                res = substitute(res, (cur, f))
                queue.append(f)
                c, new_conds = substitute_if(m, Not(c))
                conds.append(c)
                conds.extend(new_conds)
        else:
            queue.extend(cur.children())
    return (res, conds)


def anded_constraints(m: ModelDict, a: Expr, truth=True, top_level=True)\
        -> List[Expr]:
    ''' We'll find a subset of linear inequalities that are satisfied in the
    solution. To simplify computation, we'll only search for "nice" solutions
    within this set. 'a' is an assertion. 'top_level' and 'truth' are internal
    variables and indicate what we expect the truth value of the sub-expression
    to be and whether we are in the top level of recursion respectively '''

    # No point searching for solutions if we are not given a satisfying
    # assignment to begin with
    if eval_smt(m, a) != truth:
        print(a, truth)
    assert(eval_smt(m, a) == truth)

    if type(a) is AstVector:
        a = And(a)

    decl = str(a.decl())
    if decl in ["<", "<=", ">", ">=", "==", "Distinct"]:
        assert(len(a.children()) == 2)
        x, y = a.children()

        if not truth:
            decl = {
                "<": ">=",
                "<=": ">",
                ">": "<=",
                ">=": "<",
                "==": "Distinct",
                "Distinct": "=="
            }[decl]
        if decl in ["==", "Distinct"]:
            if type(x) is BoolRef or type(y) is BoolRef:
                assert(type(x) is BoolRef and type(y) is BoolRef)
                # It should evaluate to what it evaluated in the original
                # assignment
                return (anded_constraints(m, x, eval_smt(m, x), False)
                        + anded_constraints(m, y, eval_smt(m, y), False))

        if decl == "Distinct":
            # Convert != to either < or >
            if eval_smt(m, x) < eval_smt(m, y):
                return [x < y]
            else:
                return [y < x]

        if not truth:
            if decl == "<":
                return [x < y]
            if decl == "<=":
                return [x <= y]
            if decl == ">":
                return [x > y]
            if decl == ">=":
                return [x >= y]
        return [a]
    # if decl == "If":
    #     assert(len(a.children()) == 3)
    #     c, t, f = a.children()
    #     if eval_smt(m, c):
    #         return children[0] + children[1]
    #     else:
    #         return children[0] + children[2]

    if decl == "Not":
        assert(len(a.children()) == 1)
        return anded_constraints(m, a.children()[0], (not truth), False)
    if decl == "And":
        if truth:
            return sum([anded_constraints(m, x, True, False)
                        for x in a.children()],
                       start=[])
        else:
            for x in a.children():
                if not eval_smt(m, x):
                    # Return just the first one (arbitrary choice). Returning
                    # more causes us to be unnecessarily restrictive
                    return anded_constraints(m, x, False, False)
    if decl == "Or":
        if truth:
            for x in a.children():
                if eval_smt(m, x):
                    # Return just the first one (arbitrary choice). Returning
                    # more causes us to be unnecessarily restrictive
                    return anded_constraints(m, x, True, False)
        else:
            return sum([anded_constraints(m, x, False, False)
                        for x in a.children()],
                       start=[])

    if decl == "Implies":
        assert(len(a.children()) == 2)
        assert(type(eval_smt(m, a.children()[0])) is bool)
        if truth:
            if eval_smt(m, a.children()[0]):
                return anded_constraints(m, a.children()[1], True, False)
            else:
                return anded_constraints(m, a.children()[0], False, False)
        else:
            return (anded_constraints(m, a.children()[0], True, False)
                    + anded_constraints(m, a.children()[1], False, False))
    if type(a) is BoolRef:
        # Must be a boolean variable. We needn't do anything here
        return []
    print(f"Unrecognized decl {decl} in {a}")
    assert(False)


class LinearVars:
    def __init__(self, vars: Dict[str, float] = {}, constant: float = 0):
        self.vars = vars
        self.constant = constant

    def __add__(self, other):
        vars, constant = copy(self.vars), copy(self.constant)
        for k in other.vars:
            if k in vars:
                vars[k] += other.vars[k]
            else:
                vars[k] = other.vars[k]
        constant += other.constant
        return LinearVars(vars, constant)

    def __mul__(self, factor: float):
        vars, constant = copy(self.vars), copy(self.constant)
        for k in vars:
            vars[k] *= factor
        constant *= factor
        return LinearVars(vars, constant)

    def __str__(self):
        return ' + '.join([f"{self.vars[k]} * {k}" for k in self.vars])\
               + f" + {self.constant}"

    def __eq__(self, other) -> bool:
        return self.vars == other.vars and self.constant == other.constant


def get_linear_vars(expr: Union[ArithRef, RatNumRef])\
        -> LinearVars:
    ''' Given a linear arithmetic expression, return its equivalent that takes
    the form res[1] + sum_i res[0][i][0] * res[0][i][1]'''

    decl = str(expr.decl())
    if decl == "+":
        return sum([get_linear_vars(x) for x in expr.children()],
                   start=LinearVars())
    if decl == "-":
        assert(len(expr.children()) in [1, 2])
        if len(expr.children()) == 2:
            a, b = map(get_linear_vars, expr.children())
            return a + (b * (-1.0))
        else:
            return get_linear_vars(expr.children()[0]) * -1.0
    if decl == "*":
        assert(len(expr.children()) == 2)
        a, b = expr.children()
        if type(a) == ArithRef and type(b) == RatNumRef:
            return get_linear_vars(a) * float(b.as_decimal(100))
        if type(a) == RatNumRef and type(b) == ArithRef:
            return get_linear_vars(b) * float(a.as_decimal(100))
        print(f"Only linear terms allowed. Found {str(expr)}")
        exit(1)
    if decl == "/":
        assert(len(expr.children()) == 2)
        a, b = expr.children()
        assert(type(b) == RatNumRef)
        return get_linear_vars(a) * (1. / float(b.as_decimal(100)))
    if type(expr) is ArithRef:
        # It is a single variable, since we have eliminated other cases
        return LinearVars({decl: 1})
    if type(expr) is RatNumRef:
        return LinearVars({}, float(expr.as_decimal(100)))
    if type(expr) is IntNumRef:
        return LinearVars({}, expr.as_long())
    print(f"Unrecognized expression {expr} {type(expr)}")
    exit(1)


def solver_constraints(constraints: List[Any])\
        -> Tuple[List[LinearConstraint], Dict[str, int]]:
    ''' Given a list of SMT constraints (e.g. those output by
    `anded_constraints`), return the corresponding LinearConstraint object and
    the names of the variables in the order used in LinearConstraint '''

    tol = 1e-9

    # First get all the variables
    varss: Set[str] = set().union(*[set(extract_vars(e)) for e in constraints])
    varsl: List[str] = list(varss)
    vars: Dict[str, int] = {k: i for (i, k) in enumerate(varsl)}

    # The number of equality and inequality constraints
    n_eq = sum([int(str(cons.decl()) == "==") for cons in constraints])
    n_ineq = len(constraints) - n_eq

    A_eq = np.zeros((n_eq, len(vars)))
    lb_eq = np.zeros(n_eq)
    ub_eq = np.zeros(n_eq)

    A_ineq = np.zeros((n_ineq, len(vars)))
    lb_ineq = np.zeros(n_ineq)
    ub_ineq = np.zeros(n_ineq)

    i_eq, i_ineq = 0, 0
    for cons in constraints:
        assert(len(cons.children()) == 2)
        a = get_linear_vars(cons.children()[0])
        b = get_linear_vars(cons.children()[1])

        # Construct the linear part h
        if str(cons.decl()) in [">=", ">", "=="]:
            lin = b + (a * -1.0)
        elif str(cons.decl()) in ["<=", "<"]:
            lin = a + (b * -1.0)
        else:
            print(str(cons.decl()))
            assert(False)

        if str(cons.decl()) in ["<", ">"]:
            lin.constant += 1e-6

        # Put it into the matrix
        for k in lin.vars:
            j = vars[k]
            if str(cons.decl()) == "==":
                A_eq[i_eq, j] = lin.vars[k]
            else:
                A_ineq[i_ineq, j] = lin.vars[k]

        # Make the bounds
        if str(cons.decl()) == "==":
            lb_eq[i_eq] = -lin.constant - tol
            ub_eq[i_eq] = -lin.constant + tol
            i_eq += 1
        else:
            lb_ineq[i_ineq] = -float("inf")
            ub_ineq[i_ineq] = -lin.constant + tol
            i_ineq += 1
    assert(i_eq == n_eq)
    assert(i_ineq == n_ineq)

    return ([LinearConstraint(A_eq, lb_eq, ub_eq, keep_feasible=False),
             LinearConstraint(A_ineq, lb_ineq, ub_ineq, keep_feasible=False)],
            vars)


def simplify_solution(c: ModelConfig,
                      m: ModelDict,
                      assertions: BoolRef) -> ModelDict:
    new_assertions, conds = substitute_if(m, assertions)
    anded = anded_constraints(m, And(new_assertions, And(conds)))
    constraints, vars = solver_constraints(anded)
    init_values = np.asarray([m[v] for v in vars])

    def constraint_fit(soln: np.ndarray, cons: List[LinearConstraint]) \
            -> float:
        ugap = np.concatenate((
            np.dot(cons[0].A, soln) - cons[0].ub,
            np.dot(cons[1].A, soln) - cons[1].ub))
        lgap = np.concatenate((
            cons[0].lb - np.dot(cons[0].A, soln),
            cons[1].lb - np.dot(cons[1].A, soln)))
        for i in range(ugap.shape[0]):
            if ugap[i] > 1e-5 or lgap[i] > 1e-5:
                print("Found an unsatisfied constraint")
                print(anded[i])
                v = extract_vars(anded[i])
                print([(x, float(m[x])) for x in v])
    constraint_fit(init_values, constraints)

    def score1(values: np.ndarray) -> float:
        res = 0
        for t in range(1, c.T):
            res += (values[vars[f"tot_inp_{t}"]]
                    - values[vars[f"tot_inp_{t-1}"]]) ** 2 / c.T
            res += (values[vars[f"tot_out_{t}"]]
                    - values[vars[f"tot_out_{t-1}"]]) ** 2 / c.T
            res += (values[vars[f"wasted_{t}"]]
                    - values[vars[f"wasted_{t-1}"]]) ** 2 / c.T
            for n in range(c.N):
                res += (values[vars[f"cwnd_{n},{t}"]]
                        - values[vars[f"cwnd_{n},{t-1}"]]) ** 2 / (c.T * c.N)
        return res

    # Score for the new implementation
    def score2(values: np.ndarray) -> float:
        res = 0
        for t in range(1, c.T):
            res += (values[vars[f"tot_arrival_{t}"]]
                    - values[vars[f"tot_arrival_{t-1}"]]) ** 2 / c.T
            res += (values[vars[f"tot_service_{t}"]]
                    - values[vars[f"tot_service_{t-1}"]]) ** 2 / c.T
            res += (values[vars[f"wasted_{t}"]]
                    - values[vars[f"wasted_{t-1}"]]) ** 2 / c.T
            for n in range(c.N):
                res += (values[vars[f"cwnd_{n},{t}"]]
                        - values[vars[f"cwnd_{n},{t-1}"]]) ** 2 / (c.T * c.N)
        return res

    # Methods that work are "SLSQP" and "trust-constr"
    soln = minimize(score2, init_values, constraints=constraints,
                    method="SLSQP")
    constraint_fit(soln.x, constraints)

    res = copy(m)
    for var in vars:
        res[var] = soln.x[vars[var]]

    print(f"Successful? {soln.success} Message: {soln.message}")
    print(f"The solution found is feasible: {eval_smt(res, assertions)}")

    # Some cleaning up to account for numerical errors. For loss, small errors
    # make a big semantic difference. So get rid of those
    tol = 1e-9
    for t in range(1, c.T):
        if res[f"tot_lost_{t}"] - res[f"tot_lost_{t-1}"] <= 4 * tol:
            res[f"tot_lost_{t}"] = res[f"tot_lost_{t-1}"]
        for n in range(c.N):
            if res[f"loss_detected_{n},{t}"] - res[f"loss_detected_{n},{t-1}"]\
               <= 4 * tol:
                res[f"loss_detected_{n},{t}"] = res[f"loss_detected_{n},{t-1}"]

    return res

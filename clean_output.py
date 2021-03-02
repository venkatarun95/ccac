''' Take SMT output and clean it up, trying to remove the clutter and leave
behind only the essential details for why the counter-example works '''

from functools import reduce
from model_utils import ModelDict
from my_solver import extract_vars
import numpy as np
import operator
from scipy.optimize import LinearConstraint
from typing import Any, List, Tuple, Union
from z3 import And, ArithRef, AstVector, BoolRef, RatNumRef


def eval_smt(m: ModelDict, a) -> Union[float, bool]:
    if type(a) is AstVector:
        a = And(a)

    decl = str(a.decl())
    children = [eval_smt(m, x) for x in a.children()]

    if len(children) == 0:
        if type(a) is ArithRef:
            return m[str(a)]
        elif type(a) is RatNumRef:
            return float(a.as_decimal(100))
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
    if decl == "+":
        return sum(children)
    if decl == "-":
        assert(len(a.children()) == 2)
        return children[0] - children[1]
    if decl == "*":
        return reduce(operator.mul, children, 1)
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


def anded_constraints(m: ModelDict, a, top_level=True) -> List[Any]:
    ''' We'll find a subset of linear inequalities that are satisfied in the
    solution. To simplify computation, we'll only search for "nice" solutions
    within this set. 'a' is an assertion. 'top_level' is an internal variable
    and indicates whether we are in the top level of recursion '''

    # No point searching for solutions if we are not given a satisfying
    # assignment to begin with
    if top_level:
        assert(eval_smt(m, a))

    if type(a) is AstVector:
        a = And(a)

    decl = str(a.decl())
    if decl in ["<", "<=", ">", ">=", "==", "Distinct"]:
        if decl in ["==", "Distinct"]:
            if type(a.children()[0]) is BoolRef\
              or type(a.children()[1]) is BoolRef:
                print("Equality/inequality between bools not implemented")
                assert(False)
        return [a]
    children = [anded_constraints(m, x, False) for x in a.children()]

    if decl == "Not":
        assert(len(children) == 1)
        return children[0]
    if decl == "And":
        return sum(children, start=[])
    if decl == "Or":
        for i in range(len(children)):
            if eval_smt(m, a.children()[i]):
                # Return just the first one (arbitrary choice). Returning more
                # causes us to be unnecessarily restrictive
                return children[i]
    if decl == "Implies":
        assert(len(children) == 2)
        assert(type(eval_smt(m, a.children()[0])) is bool)
        if eval_smt(m, a.children()[0]):
            return sum(children, start=[])
        return []
    assert(False)


def get_linear_vars(expr: Union[ArithRef, RatNumRef])\
        -> Tuple[List[Tuple[float, str]], float]:
    ''' Given a linear arithmetic expression, return its equivalent that takes
    the form res[1] + sum_i res[0][i][0] * res[0][i][1]'''

    decl = str(expr.decl())
    if decl == "+":
        children = [get_linear_vars(x) for x in expr.children()]
        return (sum([x[0] for x in children], start=[]),
                sum([x[1] for x in children]))
    if decl == "-":
        assert(len(expr.children()) == 2)
        a, b = expr.children()
        a, b = get_linear_vars(a), get_linear_vars(b)
        bneg = [(-x[0], x[1]) for x in b[0]]
        return (a[0] + bneg, a[1] - b[1])
    if decl == "*":
        assert(len(expr.children()) == 2)
        a, b = expr.children()
        if type(a) == ArithRef and type(b) == RatNumRef:
            return ([(float(b.as_decimal(100)), str(a))], 0)
        if type(a) == RatNumRef and type(b) == ArithRef:
            return ([(float(a.as_decimal(100)), str(b))], 0)
        else:
            print(f"Only linear terms allowed. Found {str(expr)}")
            assert(False)
    if type(expr) is ArithRef:
        return ([(1, str(expr))], 0)
    if type(expr) is RatNumRef:
        return ([], float(expr.as_decimal(100)))


def solver_constraints(constraints: List[Any]) -> Tuple[LinearConstraint, List[str]]:
    ''' Given a list of SMT constraints (e.g. those output by
    `anded_constraints`), return the corresponding LinearConstraint object and
    the names of the variables in the order used in LinearConstraint '''

    # First get all the variables
    vars = set().union([set(extract_vars(e)) for e in constraints])
    vars = list(vars)
    A = np.zeros((len(constraints), len(vars)))

    for cons in constraints:
        # Get the lhs and rhs from the equation
        lhs, rhs = []

        # First, normalize everything and produce (c_vars, c_fact, b) such that
        # the constraint is b[:,0] <= sum(c_fact * c_vars) <= b[:,1]. To convert
        # <= to < and >= to >, we use a small fixed positive constant
        c_vars, c_fact, b = [], [], []
        if cons.decl() == ">=":
            pass

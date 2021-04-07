use crate::context::{Context, Symbol};
use num_rational::Ratio;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DataType {
    Bool,
    Int,
    Real,
    Void,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Constant {
    Bool(bool),
    Int(i64),
    /// Assume all real constants are rational numbers representable
    /// in i64. This certainly makes sense for the linear real
    /// arithmetic theory
    Real(Ratio<i64>),
}

impl Constant {
    fn data_type(&self) -> DataType {
        match self {
            Self::Bool(_) => DataType::Bool,
            Self::Int(_) => DataType::Int,
            Self::Real { .. } => DataType::Real,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Cmp {
    Lt,
    Le,
    Eq,
}

#[derive(Clone, Debug)]
pub enum BoolOp {
    And(Vec<Node>),
    Or(Vec<Node>),
    Not(Box<Node>),
}

#[derive(Clone, Debug)]
pub enum Node {
    Constant {
        val: Constant,
    },
    /// Some variables are indexed. We store those indices in the AST
    Variable {
        name: String,
        indices: Vec<Box<Node>>,
    },
    Cmp {
        cmp: Cmp,
        left: Box<Node>,
        right: Box<Node>,
    },
    BoolOp {
        op: BoolOp,
    },
    Add {
        terms: Vec<Node>,
    },
    Mul {
        terms: Vec<Node>,
    },
    /// Represents a range of values. Useful to linearize by
    /// discretizing
    Range {
        lower: Box<Node>,
        upper: Box<Node>,
    },
    Stmts {
        stmts: Vec<Node>,
    },
    /// Loop over lo, lo+step, lo+2*step as long as the indices are <
    /// hi
    ForLoop {
        varname: String,
        lo: Box<Node>,
        hi: Box<Node>,
        step: Box<Node>,
        body: Box<Node>,
    },
    /// Pushes a new context for its children
    Context {
        child: Box<Node>,
    },
    /// Declare a new variable
    VarDecl {
        varname: String,
        sym: Symbol,
    },
}

impl Node {
    pub fn data_type(&self, ctx: &mut Context) -> DataType {
        match self {
            Self::Constant { val } => val.data_type(),
            Self::Variable { name, .. } => {
                if let Some(s) = ctx.get(name) {
                    s.data_type
                } else {
                    panic!("Undeclared variable '{}'", name);
                }
            }
            Self::Cmp { .. } => DataType::Bool,
            Self::BoolOp { .. } => DataType::Bool,
            Self::Add { terms, .. } => {
                assert!(terms.len() > 0);
                let res = terms[0].data_type(ctx);
                for x in &terms[1..] {
                    if x.data_type(ctx) != res {
                        panic!("Adding incompatible datatypes");
                    }
                }
                res
            }
            Self::Mul { terms, .. } => {
                assert!(terms.len() > 0);
                let res = terms[0].data_type(ctx);
                for x in &terms[1..] {
                    if x.data_type(ctx) != res {
                        panic!("Adding incompatible datatypes");
                    }
                }
                res
            }
            Self::Range { lower, upper } => {
                assert!(lower.data_type(ctx) == upper.data_type(ctx));
                lower.data_type(ctx)
            }
            Self::Stmts { stmts } => {
                // Perform checks
                for stmt in stmts {
                    let dt = stmt.data_type(ctx);
                    if dt != DataType::Bool && dt != DataType::Void {
                        panic!(
                            "Warning: Statement returns type {:?}, which does nothing.",
                            dt
                        );
                    }
                }
                DataType::Void
            }
            Self::ForLoop { lo, hi, step, .. } => {
                let dt = lo.data_type(ctx);
                // Perform some checks
                if dt != hi.data_type(ctx) || dt != step.data_type(ctx) {
                    panic!("All parts of the for loop must have the same datatype. We have lo={:?}, hi={:?}, step={:?}", dt, hi.data_type(ctx), step.data_type(ctx));
                }
                if dt != DataType::Int && dt != DataType::Real {
                    panic!("For loop indices cannot have type {:?}", lo.data_type(ctx));
                }
                DataType::Void
            }
            Self::Context { child, .. } => {
                ctx.push();
                let res = child.data_type(ctx);
                ctx.pop();
                res
            }
            Self::VarDecl { .. } => DataType::Void,
        }
    }

    pub fn is_constant(&self) -> bool {
        if let Self::Constant { .. } = self {
            true
        } else {
            false
        }
    }

    pub fn get_constant(&self) -> Option<Constant> {
        if let Self::Constant { val } = self {
            Some(*val)
        } else {
            None
        }
    }

    pub fn is_linear(&self) -> bool {
        match self {
            Self::Constant { .. } => true,
            Self::Variable { .. } => true,
            Self::Add { terms, .. } => terms.iter().all(|x| x.is_linear()),
            Self::Mul { terms, .. } => {
                terms
                    .iter()
                    .map(|x| if let Self::Constant { .. } = x { 0 } else { 1 })
                    .sum::<u64>()
                    <= 1
            }
            Self::Range { lower, upper } => lower.is_linear() && upper.is_linear(),
            _ => panic!("Called `is_linear` on {:?}", self),
        }
    }

    /// Recursively fold all constants and force to zero in
    /// multiplications
    pub fn fold_const(&mut self, ctx: &mut Context) -> bool {
        fn to_rational(v: &Constant) -> Ratio<i64> {
            match v {
                Constant::Bool(_) => panic!("Unexpected bool constant"),
                Constant::Int(v) => Ratio::new(*v, 1),
                Constant::Real(v) => *v,
            }
        }
        fn to_bool(x: &Constant) -> bool {
            if let Constant::Bool(x) = x {
                *x
            } else {
                panic!("Expected bool in boolean operation, found {:?}", x)
            }
        }

        // Delete constant values and return them in a separate vector. Also returns whether something changed
        fn fold_vec(v: &mut Vec<Node>, ctx: &mut Context) -> (Vec<Constant>, bool) {
            let mut consts = Vec::new();
            let mut changed = false;
            for t in v.iter_mut() {
                changed |= t.fold_const(ctx);
                if let Node::Constant { val, .. } = t {
                    consts.push(*val);
                }
            }
            if consts.len() > 1 {
                // Remove all constant terms and add only the one constant
                changed = true;
                v.retain(|x| {
                    if let Node::Constant { .. } = *x {
                        false
                    } else {
                        true
                    }
                });
                let data_type = v[0].data_type(ctx);
                for x in v[1..].iter() {
                    if x.data_type(ctx) != data_type {
                        panic!(
                            "All datatypes must be the same. Expected {:?} found {:?}",
                            data_type,
                            x.data_type(ctx)
                        );
                    }
                }
            }
            (consts, changed)
        }

        match self {
            Self::Constant { .. } => false,
            Self::Variable { name, indices } => {
                let mut change = false;
                for i in indices {
                    change |= i.fold_const(ctx);
                }
                change |= if let Some(sym) = ctx.get(name) {
                    if let Some(val) = sym.val {
                        *self = Self::Constant { val };
                        true
                    } else {
                        false
                    }
                } else {
                    panic!("Undeclared variable '{}'", name)
                };
                change
            }
            Self::Cmp { cmp, left, right } => {
                let changed = left.fold_const(ctx) | right.fold_const(ctx);
                if let Self::Constant { val: left } = **left {
                    if let Self::Constant { val: right } = **right {
                        let left = to_rational(&left);
                        let right = to_rational(&right);
                        let res = match cmp {
                            Cmp::Lt => left < right,
                            Cmp::Le => left <= right,
                            Cmp::Eq => left == right,
                        };
                        *self = Self::Constant {
                            val: Constant::Bool(res),
                        };
                        return true;
                    }
                }
                changed
            }
            Self::BoolOp { op } => {
                match op {
                    BoolOp::And(v) => {
                        let (consts, changed) = fold_vec(v, ctx);
                        if !consts.iter().all(to_bool) {
                            // The entire thing is false
                            *self = Node::Constant {
                                val: Constant::Bool(false),
                            };
                        }
                        changed
                    }
                    BoolOp::Or(v) => {
                        let (consts, changed) = fold_vec(v, ctx);
                        if consts.iter().any(to_bool) {
                            // The entire thing is false
                            *self = Node::Constant {
                                val: Constant::Bool(true),
                            };
                        }
                        changed
                    }
                    BoolOp::Not(x) => {
                        if let Node::Constant { val } = **x {
                            if let Constant::Bool(val) = val {
                                *self = Node::Constant {
                                    val: Constant::Bool(!val),
                                };
                            } else {
                                panic!(
                                    "Cannot compute NOT of value of non-bool type {:?}",
                                    val.data_type()
                                );
                            }
                            true
                        } else {
                            false
                        }
                    }
                }
            }
            Self::Add { terms } => {
                let (consts, changed) = fold_vec(terms, ctx);
                let c_term: Ratio<i64> = consts.iter().map(to_rational).sum();
                if consts.len() > 0 {
                    let val = match consts[0].data_type() {
                        DataType::Real => Constant::Real(c_term),
                        DataType::Int => {
                            assert_eq!(*c_term.denom(), 1);
                            Constant::Int(*c_term.numer())
                        }
                        _ => unreachable!(),
                    };
                    terms.push(Node::Constant { val });
                }

                changed
            }
            Self::Mul { terms } => {
                let (consts, changed) = fold_vec(terms, ctx);
                let c_term: Ratio<i64> = consts.iter().map(to_rational).product();
                if consts.len() > 0 {
                    let val = match consts[0].data_type() {
                        DataType::Real => Constant::Real(c_term),
                        DataType::Int => {
                            assert_eq!(*c_term.denom(), 1);
                            Constant::Int(*c_term.numer())
                        }
                        _ => unreachable!(),
                    };
                    // If multiplying by zero, the entire thing will be 0
                    if *c_term.numer() == 0 {
                        *self = Node::Constant { val };
                        return true;
                    }
                    terms.push(Node::Constant { val });
                }

                changed
            }
            Self::Range { lower, upper, .. } => lower.fold_const(ctx) | upper.fold_const(ctx),
            Self::Stmts { stmts, .. } => {
                let mut change = false;
                for stmt in stmts {
                    change |= stmt.fold_const(ctx);
                }
                change
            }
            Self::ForLoop {
                varname,
                lo,
                hi,
                step,
                body,
                ..
            } => {
                let change = lo.fold_const(ctx) || hi.fold_const(ctx) || step.fold_const(ctx);
                if lo.is_constant() && hi.is_constant() && step.is_constant() {
                    // Ensure the loop variable is declared and is not an array
                    let loop_var = if let Some(var) = ctx.get(varname) {
                        if var.data_type == DataType::Bool {
                            panic!("Cannot loop over bools");
                        }
                        if var.indices.len() > 0 {
                            panic!("Loop variables cannot be array elements");
                        }
                        var
                    } else {
                        panic!("Trying to use undeclared variable {} in loop", varname);
                    };
                    // Unroll the loop
                    let lo = lo.get_constant().unwrap();
                    let hi = hi.get_constant().unwrap();
                    let step = step.get_constant().unwrap();

                    // Generate the list of symbols generated by the for loop
                    let mut cur = to_rational(&lo);
                    let mut symbols = Vec::new();
                    while cur < to_rational(&hi) {
                        let sym = match loop_var.data_type {
                            DataType::Bool => panic!("For loop cannot operate over bools"),
                            DataType::Void => panic!("For loop cannot operate over voids"),
                            DataType::Int => {
                                if *cur.denom() != 1 {
                                    panic!("Tried to use non-integer value '{}' for an integer loop variable '{}'", cur, varname);
                                }
                                Symbol {
                                    data_type: DataType::Int,
                                    val: Some(Constant::Int(*cur.numer())),
                                    indices: vec![],
                                }
                            }
                            DataType::Real => Symbol {
                                data_type: DataType::Real,
                                val: Some(Constant::Real(cur)),
                                indices: vec![],
                            },
                        };
                        symbols.push(sym);
                        cur += to_rational(&step);
                    }

                    // Now unroll the loop for each of the generated symbols
                    // The new node we'll replace `self` by
                    let mut new_stmts = Vec::new();
                    for sym in symbols {
                        new_stmts.push(Self::Context {
                            child: Box::new(Self::Stmts {
                                stmts: vec![
                                    Node::VarDecl {
                                        varname: varname.clone(),
                                        sym,
                                    },
                                    *body.clone(),
                                ],
                            }),
                        });
                    }

                    return true;
                }
                change
            }
            Self::Context { child, .. } => {
                ctx.push();
                let res = child.fold_const(ctx);
                ctx.pop();
                res
            }
            Self::VarDecl { varname, sym } => {
                ctx.insert(varname.clone(), sym.clone());
                false
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const_fold() {
        let mut ast = Node::Add {
            terms: vec![
                Node::Constant {
                    val: Constant::Int(1),
                },
                Node::Variable {
                    name: "a".to_string(),
                    indices: vec![],
                },
                Node::Mul {
                    terms: vec![
                        Node::Variable {
                            name: "b".to_string(),
                            indices: vec![],
                        },
                        Node::Constant {
                            val: Constant::Int(0),
                        },
                    ],
                },
                Node::Variable {
                    name: "c".to_string(),
                    indices: vec![],
                },
            ],
        };
        let mut ctx = Context::new();

        ctx.insert(
            "a".to_string(),
            Symbol {
                data_type: DataType::Int,
                val: None,
                indices: vec![],
            },
        );
        ctx.insert(
            "b".to_string(),
            Symbol {
                data_type: DataType::Int,
                val: None,
                indices: vec![],
            },
        );
        ctx.insert(
            "c".to_string(),
            Symbol {
                data_type: DataType::Int,
                val: Some(Constant::Int(2)),
                indices: vec![],
            },
        );

        assert!(ast.fold_const(&ctx));

        let expected_ast = Node::Add {
            terms: vec![
                Node::Variable {
                    name: "a".to_string(),
                    indices: vec![],
                },
                Node::Constant {
                    val: Constant::Int(3),
                },
            ],
        };
        assert_eq!(format!("{:?}", ast), format!("{:?}", expected_ast));
    }
}

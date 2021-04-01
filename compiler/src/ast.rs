use crate::context::{Context, Symbol};
use num_rational::Ratio;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DataType {
    Bool,
    Int,
    Real,
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

#[derive(Debug)]
pub enum BoolOp {
    And(Vec<Node>),
    Or(Vec<Node>),
    Not(Vec<Node>),
}

#[derive(Debug)]
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
    /// Loop over lo, lo+step, lo+2*step as long as the indices are <
    /// hi
    ForLoop {
        lo: Box<Node>,
        hi: Box<Node>,
        step: Box<Node>,
    },
}

impl Node {
    pub fn data_type(&self, ctx: &Context) -> DataType {
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
            Self::ForLoop { lo, hi, step } => {
                if lo.data_type(ctx) != hi.data_type(ctx)
                    || lo.data_type(ctx) != step.data_type(ctx)
                {
                    panic!("All parts of the for loop must have the same datatype. We have lo={:?}, hi={:?}, step={:?}", lo, hi, step);
                }
                if lo.data_type(ctx) == DataType::Bool {
                    panic!("For loop indices cannot have type bool");
                }
                lo.data_type(ctx)
            }
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
    pub fn fold_const(&mut self, ctx: &Context) -> bool {
        fn to_rational(v: Constant) -> Ratio<i64> {
            match v {
                Constant::Bool(_) => panic!("Unexpected bool constant"),
                Constant::Int(v) => Ratio::new(v, 1),
                Constant::Real(v) => v,
            }
        }

        match self {
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
                        let left = to_rational(left);
                        let right = to_rational(right);
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
            Self::Add { terms } => {
                let mut changed = false;
                let mut c_term = Ratio::<i64>::new(0, 1);
                let mut num_const = 0;
                for t in terms.iter_mut() {
                    changed |= t.fold_const(ctx);
                    if let Self::Constant { val, .. } = t {
                        c_term += to_rational(*val);
                        num_const += 1;
                    }
                }

                if num_const > 1 {
                    // Remove all constant terms and add only the one constant
                    terms.retain(|x| {
                        if let Self::Constant { .. } = *x {
                            false
                        } else {
                            true
                        }
                    });
                    changed = true;
                    let data_type = terms[0].data_type(ctx);
                    terms.push(Self::Constant {
                        val: match data_type {
                            DataType::Bool => panic!("Error in the compiler. Cannot add bools"),
                            DataType::Int => {
                                if *c_term.denom() != 1 {
                                    panic!("Attempted to add Real to Int");
                                }
                                Constant::Int(*c_term.numer())
                            }
                            DataType::Real => Constant::Real(c_term),
                        },
                    });
                }

                changed
            }
            Self::Mul { terms } => {
                let mut changed = false;
                let mut c_term = Ratio::<i64>::new(1, 1);
                let mut num_const = 0;
                for t in terms.iter_mut() {
                    changed |= t.fold_const(ctx);
                    if let Self::Constant { val, .. } = t {
                        c_term *= to_rational(*val);
                        num_const += 1;
                    }
                }

                // Multiplication by zero. The entire thing is 0
                if c_term == Ratio::new(0, 1) && terms.len() > 1 {
                    *self = Self::Constant {
                        val: match self.data_type(ctx) {
                            DataType::Bool => panic!("Error in the compiler. Cannot add bools"),
                            DataType::Int => Constant::Int(0),
                            DataType::Real => Constant::Real(c_term),
                        },
                    };
                    return true;
                }

                if num_const > 1 {
                    // Remove all constant terms and add only the one constant
                    terms.retain(|x| {
                        if let Self::Constant { .. } = *x {
                            false
                        } else {
                            true
                        }
                    });
                    changed = true;
                    let data_type = terms[0].data_type(ctx);
                    terms.push(Self::Constant {
                        val: match data_type {
                            DataType::Bool => {
                                panic!("Error in the compiler. Cannot multiply bools")
                            }
                            DataType::Int => {
                                if *c_term.denom() != 1 {
                                    panic!("Attempted to add Real to Int");
                                }
                                Constant::Int(*c_term.numer())
                            }
                            DataType::Real => Constant::Real(c_term),
                        },
                    });
                }

                changed
            }
            Self::Range { lower, upper, .. } => lower.fold_const(ctx) | upper.fold_const(ctx),
            _ => false,
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

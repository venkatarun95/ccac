use num_rational::Ratio;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DataType {
    Bool,
    Int,
    Real,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Constant {
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
enum Cmp {
    Lt,
    Le,
    Eq,
}

#[derive(Debug)]
enum BoolOp {
    And(Vec<Node>),
    Or(Vec<Node>),
    Not(Vec<Node>),
}

#[derive(Debug)]
enum Node {
    Constant {
        val: Constant,
    },
    /// Variables can be derived from arrays with the supplied
    /// indices. Sometimes the indices are not yet known, in which
    /// case we specify `None`. Indices can be negative or non-zero
    /// indexed because Z3 doesn't care
    Variable {
        name: String,
        data_type: DataType,
        indices: Vec<Option<i64>>,
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
}

impl Node {
    fn data_type(&self) -> DataType {
        match self {
            Self::Constant { val } => val.data_type(),
            Self::Variable { data_type, .. } => *data_type,
            Self::Cmp { .. } => DataType::Bool,
            Self::BoolOp { .. } => DataType::Bool,
            Self::Add { terms, .. } => {
                assert!(terms.len() > 0);
                let res = terms[0].data_type();
                for x in &terms[1..] {
                    if x.data_type() != res {
                        panic!("Adding incompatible datatypes");
                    }
                }
                res
            }
            Self::Mul { terms, .. } => {
                assert!(terms.len() > 0);
                let res = terms[0].data_type();
                for x in &terms[1..] {
                    if x.data_type() != res {
                        panic!("Adding incompatible datatypes");
                    }
                }
                res
            }
            Self::Range { lower, upper } => {
                assert!(lower.data_type() == upper.data_type());
                lower.data_type()
            }
        }
    }

    fn is_linear(&self) -> bool {
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
    fn fold_const(&mut self) -> bool {
        fn to_rational(v: Constant) -> Ratio<i64> {
            match v {
                Constant::Bool(_) => panic!("Unexpected bool constant"),
                Constant::Int(v) => Ratio::new(v, 1),
                Constant::Real(v) => v,
            }
        }

        match self {
            Self::Cmp { cmp, left, right } => {
                let changed = left.fold_const() | right.fold_const();
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
                    changed |= t.fold_const();
                    if let Self::Constant { val, .. } = t {
                        c_term += to_rational(*val);
                        num_const += 1;
                    }
                }
                // Multiplication by zero. The entire thing is 0
                if c_term == Ratio::new(0, 1) && terms.len() > 1 {
                    *self = Self::Constant {
                        val: match self.data_type() {
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
                    let data_type = terms[0].data_type();
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
                    changed |= t.fold_const();
                    if let Self::Constant { val, .. } = t {
                        c_term *= to_rational(*val);
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
                    let data_type = terms[0].data_type();
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
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const_fold() {}
}

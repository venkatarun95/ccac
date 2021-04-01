use std::boxed::Box;
use std::iter::Iterator;
use std::string::String;

enum NodeIterator<'a> {
    Slice(std::slice::Iter<'a, Box<dyn Node + 'a>>),
    Empty,
}

impl<'a> Iterator for NodeIterator<'a> {
    type Item = &'a Box<dyn Node + 'a>;
    fn next(&mut self) -> Option<Self::Item> {
	match self {
	    Self::Slice(iter) => iter.next(),
	    Self::Empty => None,
	}
    }
}

enum NodeType {
    ArithExpr,
    BoolExpr,
}

trait Node {
    fn children(&self) -> NodeIterator;
    fn get_type(&self) -> NodeType;
    /// Whether it is composed entirely of linear terms
    fn is_linear(&self) -> bool;
}

struct RealConstant {
    /// In linear arithmetic, real is really just rational. Z3 supports
    /// arbitrary precision, but we probably won't need it
    val: (i64, i64),
}

struct IntConstant {
    val: i64,
}

struct BoolConstant {
    val: bool,
}

/// Variable that has a direct representation in Z3 constraints
enum Z3VariableType {
    Real, Int, Bool
}

/// Variables of all types
struct Z3Variable {
    name: String,
    var_type: Z3VariableType,
}

/// Variable that must be compiled down to a z3 variable
enum Variable {
    /// Some special variables that are time ranges. These can be
    /// converted to a constant if necessary, e.g. by unrolling
    /// something
    TimeRange,
    Real,
}

/// To represent '<='. '>=' is represented using '<=' and flipped order
struct Le {
    left: Box<dyn Node>,
    right: Box<dyn Node>,
}

/// To represent '<'. '>' is represented using '<' and flipped order
struct Lt {
    left: Box<dyn Node>,
    right: Box<dyn Node>,
}

struct Add {
    vals: Vec<Box<dyn Node>>,
}

impl Node for RealConstant {
    fn children(&self) -> NodeIterator {
	NodeIterator::Empty
    }

    fn get_type(&self) -> NodeType {
	NodeType::ArithExpr
    }

    fn is_linear(&self) -> bool {
	true
    }
}

impl Node for IntConstant {
    fn children(&self) -> NodeIterator {
	NodeIterator::Empty
    }

    fn get_type(&self) -> NodeType {
	NodeType::ArithExpr
    }

    fn is_linear(&self) -> bool {
	true
    }
}

impl Node for RealConstant {
    fn children(&self) -> NodeIterator {
	NodeIterator::Empty
    }

    fn get_type(&self) -> NodeType {
	NodeType::ArithExpr
    }

    fn is_linear(&self) -> bool {
	true
    }
}

impl Node for Add {
    fn children<'a>(&'a self) -> NodeIterator<'a> {
	NodeIterator::Slice(self.vals.iter())
    }

    fn get_type(&self) -> NodeType {
	NodeType::ArithExpr
    }

    fn is_linear(&self) -> bool {
	self.vals.iter().all(|x| x.is_linear())
    }
}

struct Mul {
    left: Vec<Box<dyn Node>>,
    right: Vec<Box<dyn Node>>,
}

fn fix_non_linearity(expr: &mut Node) {
}

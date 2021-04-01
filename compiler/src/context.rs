use crate::ast::{Constant, DataType};
use std::collections::HashMap;

pub struct Symbol {
    pub data_type: DataType,
    /// Populated if the value is known at compile time. Note, arrays
    /// cannot be constants
    pub val: Option<Constant>,
    /// If this is an array, then specify the ranges of the indices
    pub indices: Vec<usize>,
}

pub type Context = HashMap<String, Symbol>;

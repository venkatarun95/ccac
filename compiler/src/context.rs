use crate::ast::{Constant, DataType};
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Symbol {
    pub data_type: DataType,
    /// Populated if the value is known at compile time. Note, arrays
    /// cannot be constants
    pub val: Option<Constant>,
    /// If this is an array, then specify the ranges of the indices
    pub indices: Vec<usize>,
}

#[derive(Debug)]
pub struct Context {
    /// Stack of contexts. Guaranteed to have at least one context
    stack: Vec<HashMap<String, Symbol>>,
}

impl Context {
    pub fn new() -> Self {
        Self {
            stack: vec![HashMap::new()],
        }
    }

    pub fn insert(&mut self, name: String, sym: Symbol) {
        if self.get(&name).is_some() {
            panic!("Variable '{}' already declared", name);
        }
        self.stack.last_mut().as_mut().unwrap().insert(name, sym);
    }

    pub fn get<'a>(&'a self, name: &str) -> Option<&'a Symbol> {
        for i in 0..self.stack.len() {
            let i = self.stack.len() - 1 - i;
            if let Some(s) = self.stack[i].get(name) {
                return Some(s);
            }
        }
        return None;
    }

    /// Push a new context in
    pub fn push(&mut self) {
        self.stack.push(HashMap::new());
    }

    /// Remove the last context
    pub fn pop(&mut self) {
        self.stack.pop();
    }
}

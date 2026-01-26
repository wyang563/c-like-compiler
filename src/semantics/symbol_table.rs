use std::collections::HashMap;

#[derive(Clone)]
#[derive(Debug)]
pub enum Entry {
    Var(VarEntry),
    Array(ArrayEntry),
    Method(MethodEntry),
    Import(ImportEntry),
}

impl Entry {
    pub fn get_is_const(&self) -> bool {
        match self {
            Entry::Var(v) => v.is_const,
            Entry::Array(a) => a.is_const,
            Entry::Method(m) => m.is_const,
            Entry::Import(i) => i.is_const,
        }
    }

    pub fn get_type(&self) -> Type {
        match self {
            Entry::Var(v) => v.var_type.clone(),
            Entry::Array(a) => a.var_type.clone(),
            Entry::Method(m) => m.return_type.clone(),
            Entry::Import(_) => Type::Int,
        }
    }
}

#[derive(Clone)]
#[derive(PartialEq)]
#[derive(Debug)]
pub enum Type {
    Void,
    Int,
    Long,
    Bool,
    IntArray,
    LongArray,
    BoolArray,
    None, // default value for error propogation
}

#[derive(Clone)]
#[derive(Debug)]
pub struct VarEntry {
    pub name: String,
    pub var_type: Type,
    pub is_const: bool,
    pub scope: usize,
    pub id: usize,
}

#[derive(Clone)]
#[derive(Debug)]
pub struct ArrayEntry {
    pub name: String,
    pub var_type: Type,
    pub is_const: bool,
    pub scope: usize, 
    pub id: usize,
}

#[derive(Clone)]
#[derive(Debug)]
pub struct MethodEntry {
    pub name: String,
    pub return_type: Type,
    pub is_const: bool,
    pub param_list: Vec<VarEntry>,
    pub param_count: usize,
    pub scope: usize,
    pub id: usize,
}

#[derive(Clone)]
#[derive(Debug)]
pub struct ImportEntry {
    pub name: String,
    pub is_const: bool,
    pub return_type: Type, // int by default
    pub scope: usize,
    pub id: usize,
}

#[derive(Clone)]
#[derive(Debug)]
pub struct Table {
    pub method_return_type: Type,
    pub entries: HashMap<String, Entry>,
    pub scope_ind: usize,
    pub parent_ind: Option<usize>,
    pub children_inds: Vec<usize>,
}

#[derive(Debug)]
pub struct SymbolTable {
    pub vars: Vec<Box<Entry>>,
    pub scopes: Vec<Box<Table>>,
}
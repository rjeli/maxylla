use std::collections::HashMap;
use std::fmt;
use strum_macros::EnumString;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Sym(String),
    Num(i32),
    Form(Vec<Expr>),
}

#[macro_export]
macro_rules! f {
    ( $h:expr $(, $t:expr )* $(,)? ) => (
        Expr::Form(vec![Expr::Sym(stringify!($h).to_string()), $( $t ),* ])
    );
}
// (

#[macro_export]
macro_rules! f_args {
    ( $h:expr, $t:expr ) => {{
        let mut v = vec![s!($h)];
        v.extend_from_slice($t);
        Expr::Form(v)
    }};
}

#[macro_export]
macro_rules! s {
    ( $s:expr ) => {
        Expr::Sym(stringify!($s).to_string())
    };
}
// (

#[macro_export]
macro_rules! n {
    ( $n:expr ) => {
        Expr::Num($n)
    };
}

impl Expr {
    pub fn null() -> Expr {
        s!(Null)
    }
    pub fn display(&self) -> String {
        match self {
            Expr::Form(es) => match es.split_first() {
                Some((h, args)) => format!(
                    "{}[{}]",
                    h.display(),
                    args.iter()
                        .map(|a| a.display())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                None => "EMPTYFORM".to_owned(),
            },
            Expr::Sym(s) => s.clone(),
            Expr::Num(n) => format!("{}", n),
        }
    }
}
impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display())
    }
}
impl std::default::Default for Expr {
    fn default() -> Self {
        f![Sequence]
    }
}

#[derive(Debug, PartialEq, Eq, EnumString, Clone)]
pub enum Attr {
    HoldAll,
    HoldFirst,
    HoldRest,
    Flat,
    Orderless,
    OneIdentity,
}

#[derive(Debug, Default, Clone)]
pub struct Env {
    pub attrs: HashMap<String, Vec<Attr>>,
    pub owns: HashMap<String, Expr>,
    pub downs: HashMap<String, Vec<(Expr, Expr)>>,
    pub trace: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalError {
    pub msg: String,
}
impl EvalError {
    pub fn new(m: &str) -> EvalError {
        EvalError { msg: m.to_owned() }
    }
}
impl std::fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.msg)
    }
}
impl std::error::Error for EvalError {}
pub type EvalResult<T> = std::result::Result<T, EvalError>;

#[derive(Default, Debug, PartialEq, Eq, Clone)]
pub struct MatchInfo {
    pub expr: Expr,
    pub bindings: HashMap<String, Expr>,
    pub max_nest: i32,
    pub num_constants: i32,
}

#[derive(Debug, PartialEq, Eq)]
pub enum MatchError {
    Failure,
    Error(EvalError),
}

pub type MatchResultT<T> = std::result::Result<T, MatchError>;
pub type MatchResult = MatchResultT<(MatchInfo, usize)>;

pub struct Unification {
    pub env: Env,
}

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
        let mut v: Vec<Expr> = vec![s!($h)];
        // v.extend_from_slice($t);
        v.extend($t);
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

// have to import parse::parse for this
#[macro_export]
macro_rules! p {
    ( $s:expr ) => {
        parse($s).unwrap()
    };
}

impl Expr {
    pub fn null() -> Expr {
        s!(Null)
    }
    pub fn display(&self) -> String {
        match self {
            Expr::Form(es) => match es.split_first() {
                Some((h, args)) => {
                    if let Some(true) = h.as_sym().map(|s| s == "CompoundExpression") {
                        args.iter()
                            .map(|a| a.display())
                            .collect::<Vec<_>>()
                            .join("; ")
                    } else {
                        format!(
                            "{}[{}]",
                            h.display(),
                            args.iter()
                                .map(|a| a.display())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    }
                }
                None => "$EMPTYFORM".to_owned(),
            },
            Expr::Sym(s) => s.clone(),
            Expr::Num(n) => format!("{}", n),
        }
    }
    pub fn as_sym(&self) -> Option<&str> {
        match self {
            Expr::Sym(s) => Some(s),
            _ => None,
        }
    }
    pub fn as_form(&self) -> Option<&Vec<Expr>> {
        match self {
            Expr::Form(es) => Some(es),
            _ => None,
        }
    }
    pub fn flatten_seqs(exprs: &[Expr]) -> Vec<Expr> {
        let mut v: Vec<Expr> = vec![];
        for e in exprs {
            match e {
                Expr::Form(es) => {
                    let (head, args) = es.split_first().unwrap();
                    if let Some("Sequence") = head.as_sym() {
                        v.extend(Expr::flatten_seqs(args));
                    } else {
                        let mut e2: Vec<Expr> = vec![];
                        e2.push(head.clone());
                        e2.extend(Expr::flatten_seqs(args));
                        v.push(Expr::Form(e2));
                    }
                }
                _ => v.push(e.clone()),
            }
        }
        v
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
pub struct Subs {
    pub subs: HashMap<String, Expr>,
    // pub num_constants: i32,
}

#[derive(Debug, PartialEq, Eq)]
pub enum UnifyError {
    Failure,
    Error(EvalError),
}

pub type UnifyResultT<T> = std::result::Result<T, UnifyError>;
pub type UnifyResult = UnifyResultT<Subs>;

/*
pub struct Unification {
    pub env: Env,
}
*/

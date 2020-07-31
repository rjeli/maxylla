use std::cmp::{Ord, Ordering, PartialOrd};
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
                    if let Some(s) = h.as_sym() {
                        match s {
                            "CompoundExpression" => {
                                return args
                                    .iter()
                                    .map(|a| a.display())
                                    .collect::<Vec<_>>()
                                    .join("; ");
                            }
                            "List" => {
                                return format!(
                                    "{{{}}}",
                                    args.iter()
                                        .map(|a| a.display())
                                        .collect::<Vec<_>>()
                                        .join(", ")
                                );
                            }
                            "Rule" if args.len() == 2 => {
                                return format!("{} -> {}", args[0].display(), args[1].display());
                            }
                            _ => (),
                        }
                    }
                    format!(
                        "{}[{}]",
                        h.display(),
                        args.iter()
                            .map(|a| a.display())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
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
    pub fn as_num(&self) -> Option<i32> {
        match self {
            Expr::Num(n) => Some(*n),
            _ => None,
        }
    }
    pub fn as_form(&self) -> Option<&Vec<Expr>> {
        match self {
            Expr::Form(es) => Some(es),
            _ => None,
        }
    }
    pub fn head(&self) -> Option<&str> {
        match self {
            Expr::Sym(_) => Some("Symbol"),
            Expr::Num(_) => Some("Integer"),
            Expr::Form(es) => es.first().map(|e| e.as_sym()).flatten(),
        }
    }
    pub fn has_head(&self, h: &str) -> bool {
        self.head() == Some(h)
    }
    pub fn flat(self, h: &str) -> Vec<Expr> {
        if self.has_head(h) {
            self.as_form().unwrap()[1..].to_vec()
        } else {
            vec![self]
        }
    }
    pub fn flatten_seqs(exprs: &[Expr]) -> Vec<Expr> {
        let mut v: Vec<Expr> = vec![];
        for e in exprs {
            match e {
                Expr::Form(es) => {
                    let (head, args) = es.split_first().unwrap();
                    if head.as_sym() == Some("Sequence") {
                        v.extend(Expr::flatten_seqs(args));
                    } else {
                        let mut e2: Vec<Expr> = Expr::flatten_seqs(&[head.clone()]);
                        e2.extend(Expr::flatten_seqs(args));
                        v.push(Expr::Form(e2));
                    }
                }
                _ => v.push(e.clone()),
            }
        }
        v
    }
    fn sort_position(&self) -> i32 {
        match self {
            Expr::Num(_) => 0,
            Expr::Sym(_) => 1,
            Expr::Form(_) => 2,
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
impl PartialOrd for Expr {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Expr {
    fn cmp(&self, other: &Self) -> Ordering {
        self.sort_position()
            .cmp(&other.sort_position())
            .then_with(|| match (self, other) {
                (Expr::Num(n1), Expr::Num(n2)) => n1.cmp(n2),
                (Expr::Sym(s1), Expr::Sym(s2)) => s1.cmp(s2),
                (Expr::Form(es1), Expr::Form(es2)) => es1[0]
                    .cmp(&es2[0])
                    .then(es1.len().cmp(&es2.len()))
                    .then_with(|| {
                        for i in 1..es1.len() {
                            let c = es1[i].cmp(&es2[i]);
                            if c != Ordering::Equal {
                                return c;
                            }
                        }
                        Ordering::Equal
                    }),
                _ => panic!("huh? {} {}", self, other),
            })
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
    pub subs: HashMap<String, Vec<(Expr, Expr)>>,
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
    pub max_depth: i32,
    pub num_constants: i32,
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

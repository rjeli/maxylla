use crate::{
    f,
    parse::{parse, Expr},
    s,
};
use std::cmp::Ordering;
use std::collections::{hash_map, HashMap};
use std::default::Default;
use std::str::FromStr;
use std::{fmt, fs, iter};
use strum_macros::EnumString;

#[derive(Debug, PartialEq, Eq, EnumString)]
enum Attr {
    HoldAll,
    HoldFirst,
    HoldRest,
    Flat,
    Orderless,
    OneIdentity,
}

#[derive(Debug, Default)]
pub struct Env {
    attrs: HashMap<String, Vec<Attr>>,
    owns: HashMap<String, Expr>,
    downs: HashMap<String, Vec<(Expr, Expr)>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalError {
    msg: String,
}
impl EvalError {
    fn new(m: &str) -> EvalError {
        EvalError { msg: m.to_owned() }
    }
}
impl std::fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.msg)
    }
}
impl std::error::Error for EvalError {}
type EvalResult<T> = std::result::Result<T, EvalError>;

#[derive(Default, Debug, PartialEq, Eq)]
struct MatchInfo {
    max_nest: i32,
    num_constants: i32,
    bindings: HashMap<String, Expr>,
}
impl Ord for MatchInfo {
    fn cmp(&self, other: &Self) -> Ordering {
        let s = (self.max_nest, self.num_constants, self.bindings.len());
        let o = (other.max_nest, other.num_constants, other.bindings.len());
        s.cmp(&o)
    }
}
impl PartialOrd for MatchInfo {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
#[derive(Debug, PartialEq, Eq)]
enum Match {
    Failure,
    Success(MatchInfo),
}
impl Match {
    fn fail() -> EvalResult<Self> {
        Ok(Match::Failure)
    }
    fn succeed() -> EvalResult<Self> {
        Ok(Match::Success(Default::default()))
    }
    fn constant() -> EvalResult<Self> {
        Ok(Match::Success(MatchInfo {
            num_constants: 1,
            ..Default::default()
        }))
    }
    fn bind(name: &str, val: &Expr) -> EvalResult<Self> {
        let mut bindings = HashMap::new();
        bindings.insert(name.to_owned(), val.clone());
        Ok(Match::Success(MatchInfo {
            bindings,
            ..Default::default()
        }))
    }
    fn combine(matches: &[Match]) -> Match {
        let mut infos = vec![];
        for m in matches {
            match m {
                Match::Failure => return Match::Failure,
                Match::Success(info) => infos.push(info),
            }
        }
        let mut max_nest = 0;
        let mut num_constants = 0;
        let mut bindings = HashMap::new();
        for info in infos {
            for (k, v) in info.bindings.clone() {
                match bindings.entry(k) {
                    hash_map::Entry::Occupied(occ) => {
                        if occ.get() != &v {
                            return Match::Failure;
                        }
                    }
                    hash_map::Entry::Vacant(vac) => {
                        vac.insert(v);
                    }
                }
            }
            max_nest = max_nest.max(info.max_nest);
            num_constants += info.num_constants;
        }
        Match::Success(MatchInfo {
            max_nest,
            num_constants,
            bindings,
        })
    }
    fn nest(self) -> Self {
        match self {
            Match::Success(info) => Match::Success(MatchInfo {
                max_nest: info.max_nest + 1,
                ..info
            }),
            Match::Failure => Match::Failure,
        }
    }
    fn with_binding(self, name: &str, val: &Expr) -> EvalResult<Self> {
        match self {
            Match::Success(info) => {
                let mut bindings = info.bindings;
                bindings.insert(name.to_owned(), val.clone());
                Ok(Match::Success(MatchInfo {
                    bindings,
                    ..Default::default()
                }))
            }
            Match::Failure => Ok(Match::Failure),
        }
    }
}

impl Env {
    fn bare() -> Env {
        Default::default()
    }

    pub fn new() -> Env {
        let mut env = Env::bare();
        let entries = fs::read_dir("stdlib").unwrap();
        for entry in entries {
            let path = entry.unwrap().path();
            println!("evaling stdlib {}", path.display());
            let contents = fs::read_to_string(path).unwrap();
            let parsed = parse(&contents).unwrap();
            env.eval(&parsed).unwrap();
        }
        env
    }

    pub fn eval(&mut self, e: &Expr) -> EvalResult<Expr> {
        self.eval_at(e, 0)
    }

    fn eval_at(&mut self, e: &Expr, depth: i32) -> EvalResult<Expr> {
        if depth > 256 {
            return Err(EvalError::new("depth limit reached"));
        }
        match e {
            Expr::Form(es) => {
                let (head, args) = es.split_first().ok_or(EvalError::new("no head"))?;
                let head = self.eval_at(head, depth + 1)?;
                let head_sym = match head.clone() {
                    Expr::Sym(s) => Ok(s),
                    _ => Err(EvalError::new("head not a sym")),
                }?;
                /* flatten sequences */
                let args = args
                    .iter()
                    .flat_map(|a| match a {
                        Expr::Form(arg_exprs) => match arg_exprs.split_first() {
                            Some((arg_head, arg_rest)) => {
                                if arg_head == &s!(Sequence) {
                                    arg_rest.to_vec().into_iter()
                                } else {
                                    vec![a.clone()].into_iter()
                                }
                            }
                            None => vec![a.clone()].into_iter(),
                        },
                        _ => vec![a.clone()].into_iter(),
                    })
                    .collect::<Vec<_>>();
                /* evaluate args */
                let args = if self.has_attr(&head_sym, Attr::HoldAll) {
                    args.to_vec()
                } else {
                    match args.split_first() {
                        Some((first, rest)) => {
                            let first = if self.has_attr(&head_sym, Attr::HoldFirst) {
                                first.clone()
                            } else {
                                self.eval_at(first, depth + 1)?
                            };
                            let rest = if self.has_attr(&head_sym, Attr::HoldRest) {
                                rest.to_vec()
                            } else {
                                rest.iter()
                                    .map(|a| self.eval_at(a, depth + 1))
                                    .collect::<EvalResult<Vec<Expr>>>()?
                            };
                            let mut v = vec![first];
                            v.extend(rest);
                            v
                        }
                        None => vec![],
                    }
                };
                let mut v = vec![head];
                v.extend(args.clone());
                let expr = Expr::Form(v);
                // println!("evaluating: {:?}", expr);
                if let Some(downs) = self.downs.get(&head_sym) {
                    // println!("downs: {:?}", downs);
                    let mut candidates = vec![];
                    for (lhs, rhs) in downs {
                        if let Match::Success(info) = self.unify(lhs, &expr)? {
                            candidates.push((info, rhs));
                        }
                    }
                    // println!("cands: {:?}", candidates);
                    if let Some((info, rhs)) = candidates.iter().max_by_key(|e| &e.0) {
                        // println!("applying bindings {:?} to {:?}", &info.bindings, rhs);
                        let bound = self.apply_bindings(rhs, &info.bindings)?;
                        // println!("bound: {:?}", bound);
                        return self.eval(&bound);
                    }
                    // let matches = downs.iter().map(|(lhs, rhs)| self.unify(lhs, expr));
                }
                // println!("eval: {:?} {:?}", head, args);
                if let Some(result) = self.eval_builtins(&head_sym, &args)? {
                    return Ok(result);
                }
                Ok(expr)
            }
            Expr::Sym(s) => match self.owns.get(s).map(|e2| e2.clone()) {
                Some(e2) => self.eval_at(&e2, depth + 1),
                None => Ok(e.clone()),
            },
            Expr::Num(_) => Ok(e.clone()),
        }
    }

    fn set_attr(&mut self, s: &str, attr_s: &str) {
        if !self.attrs.contains_key(s) {
            self.attrs.insert(s.to_owned(), vec![]);
        }
        let attr = Attr::from_str(attr_s).unwrap();
        self.attrs.get_mut(s).unwrap().push(attr);
    }

    fn has_attr(&self, s: &str, attr: Attr) -> bool {
        self.attrs
            .get(s)
            .map(|attrs| attrs.contains(&attr))
            .unwrap_or(false)
    }

    fn eval_builtins(&mut self, head_sym: &str, args: &[Expr]) -> EvalResult<Option<Expr>> {
        match head_sym {
            "SetAttributes" => match args {
                [Expr::Sym(s), Expr::Sym(a)] => {
                    self.set_attr(s, a);
                    Ok(Some(Expr::null()))
                }
                [Expr::Sym(s), Expr::Form(es2)] => {
                    let (head2, args2) =
                        es2.split_first().ok_or(EvalError::new("bad setattr rhs"))?;
                    if head2 != &Expr::Sym("List".to_owned()) {
                        return Err(EvalError::new("bad setattr rhs (not list)"));
                    }
                    for ae in args2 {
                        if let Expr::Sym(a) = ae {
                            self.set_attr(s, a);
                        } else {
                            return Err(EvalError::new("bad setattr rhs (not sym)"));
                        }
                    }
                    Ok(Some(Expr::null()))
                }
                _ => Err(EvalError::new("bad setattributes args")),
            },
            "SetDelayed" => match args {
                [Expr::Sym(s), rhs] => {
                    self.owns.insert(s.to_owned(), rhs.clone());
                    Ok(Some(Expr::null()))
                }
                [Expr::Form(lhs), rhs] => {
                    let lhs_head = lhs.first().ok_or(EvalError::new("bad setdelayed head"))?;
                    let lhs_sym = match lhs_head {
                        Expr::Sym(s) => Ok(s.clone()),
                        _ => return Err(EvalError::new("setdelayed head not sym")),
                    }?;
                    if !self.downs.contains_key(&lhs_sym) {
                        self.downs.insert(lhs_sym.clone(), vec![]);
                    }
                    self.downs
                        .get_mut(&lhs_sym)
                        .unwrap()
                        .push((Expr::Form(lhs.clone()), rhs.clone()));
                    Ok(Some(Expr::null()))
                }
                _ => Err(EvalError::new("bad setdelayed args")),
            },
            "OwnValues" => match args {
                [Expr::Sym(s)] => Ok(Some(match self.owns.get(s) {
                    Some(rhs) => f![
                        List,
                        f![
                            RuleDelayed,
                            f![HoldPattern, Expr::Sym(s.clone())],
                            rhs.clone()
                        ]
                    ],
                    None => f![List],
                })),
                _ => Err(EvalError::new("bad ownvalues args")),
            },
            "DownValues" => match args {
                [Expr::Sym(s)] => Ok(Some(match self.downs.get(s) {
                    Some(downs) => {
                        let rules = downs
                            .iter()
                            .map(|(lhs, rhs)| {
                                f![RuleDelayed, f![HoldPattern, lhs.clone()], rhs.clone()]
                            })
                            .collect::<Vec<_>>();
                        let mut v = vec![Expr::Sym("List".to_owned())];
                        v.extend(rules);
                        Expr::Form(v)
                    }
                    None => f![List],
                })),
                _ => Err(EvalError::new("bad downvalues args")),
            },
            "Replace" => match args {
                [expr, Expr::Form(rule)] => {
                    if rule.len() < 3 {
                        return Err(EvalError::new("bad replace rule"));
                    }
                    if rule[0] != s!(Rule) {
                        return Err(EvalError::new("bad replace rule"));
                    }
                    let lhs = &rule[1];
                    let rhs = &rule[2];
                    Ok(Some(self.replace(&expr, &lhs, &rhs)?))
                }
                _ => Err(EvalError::new("bad replace args")),
            },
            "ReplaceAll" => match args {
                [expr, Expr::Form(rule)] => {
                    if rule.len() < 3 {
                        return Err(EvalError::new("bad replaceall rule"));
                    }
                    if rule[0] != s!(Rule) {
                        return Err(EvalError::new("bad replaceall rule"));
                    }
                    let lhs = &rule[1];
                    let rhs = &rule[2];
                    Ok(Some(self.replace_all(&expr, &lhs, &rhs)?))
                }
                _ => Err(EvalError::new("bad replace args")),
            },
            "ReplaceRepeated" => match args {
                [expr, Expr::Form(rule)] => {
                    if rule.len() < 3 {
                        return Err(EvalError::new("bad replaceall rule"));
                    }
                    if rule[0] != s!(Rule) {
                        return Err(EvalError::new("bad replaceall rule"));
                    }
                    let lhs = &rule[1];
                    let rhs = &rule[2];
                    let mut last = expr.clone();
                    loop {
                        let replaced = self.replace_all(&last, &lhs, &rhs)?;
                        // println!("last: {:?} replaced: {:?}", last, replaced);
                        if last == replaced {
                            return Ok(Some(replaced));
                        }
                        last = replaced;
                    }
                }
                _ => Err(EvalError::new("bad replace args")),
            },
            "Times" => match args {
                [Expr::Num(n1), Expr::Num(n2)] => Ok(Some(Expr::Num(n1 * n2))),
                _ => Ok(None),
            },
            "Plus" => match args {
                [Expr::Num(n1), Expr::Num(n2)] => Ok(Some(Expr::Num(n1 + n2))),
                _ => Ok(None),
            },
            _ => Ok(None),
        }
    }

    fn replace(&self, expr: &Expr, lhs: &Expr, rhs: &Expr) -> EvalResult<Expr> {
        match self.unify(lhs, expr)? {
            Match::Success(info) => self.apply_bindings(rhs, &info.bindings),
            Match::Failure => Ok(expr.clone()),
        }
    }

    fn replace_all(&self, expr: &Expr, lhs: &Expr, rhs: &Expr) -> EvalResult<Expr> {
        match self.unify(lhs, expr)? {
            Match::Success(info) => self.apply_bindings(rhs, &info.bindings),
            Match::Failure => match expr {
                Expr::Form(es) => {
                    let mapped = es
                        .iter()
                        .map(|e| self.replace(e, lhs, rhs))
                        .collect::<EvalResult<Vec<_>>>()?;
                    Ok(Expr::Form(mapped))
                }
                e => Ok(e.clone()),
            },
        }
    }

    fn apply_bindings(&self, expr: &Expr, bindings: &HashMap<String, Expr>) -> EvalResult<Expr> {
        match expr {
            Expr::Form(exprs) => Ok(Expr::Form(
                exprs
                    .iter()
                    .map(|e| self.apply_bindings(e, bindings))
                    .collect::<EvalResult<Vec<_>>>()?,
            )),
            e => {
                for (k, v) in bindings {
                    match self.unify(&Expr::Sym(k.to_owned()), e)? {
                        Match::Success(_) => return Ok(v.clone()),
                        _ => (),
                    }
                }
                Ok(e.clone())
            }
        }
    }

    fn unify(&self, patt: &Expr, expr: &Expr) -> EvalResult<Match> {
        match (patt, expr) {
            (Expr::Form(patt), expr) => {
                if patt.len() == 0 {
                    return Match::fail();
                }
                let (patt_head, patt_args) = patt.split_first().unwrap();
                let patt_sym = match patt_head.clone() {
                    Expr::Sym(s) => Ok(s),
                    _ => Err(EvalError::new("bad patt head")),
                }?;
                match &patt_sym[..] {
                    "Blank" => match &patt_args[..] {
                        [blank_head @ Expr::Sym(_)] => {
                            let exprs = match expr {
                                Expr::Form(exprs) => exprs,
                                _ => return Match::fail(),
                            };
                            if exprs.len() == 0 {
                                return Match::fail();
                            }
                            if exprs.first().unwrap() != blank_head {
                                return Match::fail();
                            }
                            Match::succeed()
                        }
                        [] => Match::succeed(),
                        _ => Match::fail(),
                    },
                    "Pattern" => match &patt_args[..] {
                        [Expr::Sym(name), body] => self.unify(body, expr)?.with_binding(name, expr),
                        _ => Match::fail(),
                    },
                    "Sequence" => {
                        let exprs = match expr {
                            Expr::Form(exprs) => exprs,
                            _ => return Match::fail(),
                        };
                        if exprs.len() == 0 {
                            return Match::fail();
                        }
                        let (expr_head, expr_args) = exprs.split_first().unwrap();
                        if expr_head != &s!(Sequence) {
                            return Match::fail();
                        }

                        if let Some(Expr::Form(pa0s)) = patt_args.first() {
                            if pa0s.get(0) == Some(&s!(Pattern))
                                && (pa0s.get(2) == Some(&f![BlankNullSequence])
                                    || (pa0s.get(2) == Some(&f![BlankSequence])
                                        && expr_args.len() > 0))
                            {
                                let name = match &pa0s[1] {
                                    Expr::Sym(s) => s.clone(),
                                    _ => unreachable!(),
                                };
                                let sidx = if pa0s.get(2) == Some(&f![BlankNullSequence]) {
                                    0
                                } else {
                                    1
                                };
                                for pivot in sidx..(expr_args.len() + 1) {
                                    let cap = &expr_args[..pivot];
                                    let cap_seq = {
                                        let mut v = vec![s!(Sequence)];
                                        v.extend_from_slice(cap);
                                        Expr::Form(v)
                                    };
                                    let cap_match =
                                        Match::succeed()?.with_binding(&name, &cap_seq)?;
                                    let leftover = &expr_args[pivot..];
                                    let leftover_seq = {
                                        let mut v = vec![s!(Sequence)];
                                        v.extend_from_slice(leftover);
                                        Expr::Form(v)
                                    };
                                    let rest_seq = {
                                        let mut v = vec![s!(Sequence)];
                                        v.extend_from_slice(&patt_args[1..]);
                                        Expr::Form(v)
                                    };
                                    let leftover_match = self.unify(&rest_seq, &leftover_seq)?;
                                    let combined = Match::combine(&[cap_match, leftover_match]);
                                    if let Match::Success(_) = combined {
                                        return Ok(combined);
                                    }
                                }
                            }
                        }

                        if patt_args.len() != expr_args.len() {
                            return Match::fail();
                        }
                        let matches = patt_args
                            .iter()
                            .zip(expr_args)
                            .map(|(p, e)| self.unify(p, e))
                            .collect::<EvalResult<Vec<_>>>()?;
                        Ok(Match::combine(&matches[..]))
                    }
                    _ => {
                        let exprs = match expr {
                            Expr::Form(exprs) => exprs,
                            _ => return Match::fail(),
                        };
                        if exprs.len() == 0 {
                            return Match::fail();
                        }
                        let (expr_head, expr_args) = exprs.split_first().unwrap();
                        if expr_head != patt_head {
                            return Match::fail();
                        }

                        let mut patt_v = vec![s!(Sequence)];
                        patt_v.extend_from_slice(patt_args);
                        let patt_seq = Expr::Form(patt_v);

                        let mut expr_v = vec![s!(Sequence)];
                        expr_v.extend_from_slice(expr_args);
                        let expr_seq = Expr::Form(expr_v);

                        let seq_match = self.unify(&patt_seq, &expr_seq)?;
                        Ok(seq_match.nest())
                    }
                }
            }
            (Expr::Sym(s1), Expr::Sym(s2)) if s1 == s2 => Match::constant(),
            (Expr::Num(n1), Expr::Num(n2)) if n1 == n2 => Match::constant(),
            (_, _) => Match::fail(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_unify() {
        let env = Env::new();
        assert_eq!(env.unify(&Expr::Num(0), &Expr::Num(0)), Match::constant(),);
        assert_eq!(env.unify(&Expr::Num(0), &Expr::Num(1)), Match::fail());
        assert_eq!(env.unify(&s!(a), &s!(a)), Match::constant());
        assert_eq!(env.unify(&s!(a), &s!(b)), Match::fail());
        assert_eq!(env.unify(&f![Blank], &s!(xyz)), Match::succeed());
        assert_eq!(
            env.unify(&f![Blank, s!(Foo)], &f![Foo, s!(xyz)]),
            Match::succeed(),
        );
        assert_eq!(
            env.unify(&f![Blank, s!(Foo)], &f![Bar, s!(xyz)]),
            Match::fail()
        );
        assert_eq!(
            env.unify(&f![Foo, f!(Blank)], &f![Foo, s!(x)]),
            Ok(Match::Success(MatchInfo {
                max_nest: 1,
                bindings: HashMap::new(),
                num_constants: 0,
            }))
        );
    }
}

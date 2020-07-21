use std::cmp::Ordering;
use std::collections::{hash_map, HashMap};

use crate::{f, s, types::*};

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

impl MatchInfo {
    pub fn succeed(consumed: usize) -> MatchResult {
        Ok((Default::default(), consumed))
    }
    pub fn fail<T>() -> MatchResultT<T> {
        Err(MatchError::Failure)
    }
    pub fn err<T>(msg: &str) -> MatchResultT<T> {
        Err(MatchError::Error(EvalError::new(msg)))
    }
    pub fn constant(expr: Expr, consumed: usize) -> MatchResult {
        Ok((
            MatchInfo {
                expr,
                num_constants: 1,
                ..Default::default()
            },
            consumed,
        ))
    }
    pub fn value(expr: Expr, consumed: usize) -> MatchResult {
        Ok((
            MatchInfo {
                expr,
                ..Default::default()
            },
            consumed,
        ))
    }
    pub fn guard(cond: bool) -> MatchResult {
        if cond {
            MatchInfo::succeed(0)
        } else {
            MatchInfo::fail()
        }
    }
    /*
    pub fn bind(name: &str, val: &Expr) -> MatchResult {
        let mut bindings = HashMap::new();
        bindings.insert(name.to_owned(), val.clone());
        Ok(MatchInfo {
            bindings,
            ..Default::default()
        })
    }
    pub fn combine(infos: &[MatchInfo]) -> MatchResult {
        let mut max_nest = 0;
        let mut num_constants = 0;
        let mut bindings = HashMap::new();
        for info in infos {
            for (k, v) in info.bindings.clone() {
                match bindings.entry(k) {
                    hash_map::Entry::Occupied(occ) => {
                        if occ.get() != &v {
                            return MatchInfo::fail();
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
        Ok(MatchInfo {
            max_nest,
            num_constants,
            bindings,
        })
    }
    */
    pub fn concat(infos: &[MatchInfo], consumed: usize) -> MatchResult {
        let mut max_nest = 0;
        let mut num_constants = 0;
        let mut bindings = HashMap::new();
        let mut exprs = vec![];
        for info in infos {
            for (k, v) in info.bindings.clone() {
                match bindings.entry(k) {
                    hash_map::Entry::Occupied(occ) => {
                        if *occ.get() != v {
                            return MatchInfo::fail();
                        }
                    }
                    hash_map::Entry::Vacant(vac) => {
                        vac.insert(v);
                    }
                }
            }
            max_nest = max_nest.max(info.max_nest);
            num_constants += info.num_constants;
            exprs.push(info.expr.clone());
        }
        Ok((
            MatchInfo {
                max_nest,
                num_constants,
                bindings,
                expr: f_args!(Sequence, &exprs).flatten_seq(),
            },
            consumed,
        ))
    }
    pub fn nest(self) -> Self {
        MatchInfo {
            max_nest: self.max_nest + 1,
            ..self
        }
    }
    pub fn bound_as(self, name: String) -> Self {
        let mut bindings = (&self.bindings).clone();
        bindings.insert(name, (&self.expr).clone());
        MatchInfo { bindings, ..self }
    }
}

impl Expr {
    pub fn to_split(&self) -> MatchResultT<(String, Vec<Expr>)> {
        match self {
            Expr::Form(es) => {
                MatchInfo::guard(es.len() > 0)?;
                Ok((es[0].to_sym()?.clone(), es[1..].to_vec()))
            }
            _ => MatchInfo::fail(),
        }
    }
    pub fn to_has_head(&self, s: &str) -> MatchResultT<Vec<Expr>> {
        match self {
            Expr::Form(es) => {
                MatchInfo::guard(es.len() > 0)?;
                MatchInfo::guard(*es.first().unwrap() == Expr::Sym(s.to_owned()))?;
                Ok(es[1..].to_vec())
            }
            _ => MatchInfo::fail(),
        }
    }
    pub fn to_sym(&self) -> MatchResultT<String> {
        match self {
            Expr::Sym(s) => Ok(s.clone()),
            _ => MatchInfo::fail(),
        }
    }
    pub fn to_num(&self) -> MatchResultT<i32> {
        match self {
            Expr::Num(n) => Ok(*n),
            _ => MatchInfo::fail(),
        }
    }
    fn flatten_seq_into(&self, exprs: &mut Vec<Expr>) {
        if let Ok(es) = self.to_has_head("Sequence") {
            for e in es {
                e.flatten_seq_into(exprs);
            }
        } else {
            exprs.push(self.clone());
        }
    }
    pub fn flatten_seq(&self) -> Expr {
        let mut exprs = vec![];
        self.flatten_seq_into(&mut exprs);
        if exprs.len() == 1 {
            exprs[0].clone()
        } else {
            f_args!(Sequence, &exprs)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_flatten_seq() {
        assert_eq!(f![x, s!(y)].flatten_seq(), f![x, s!(y)]);
        assert_eq!(f![Sequence].flatten_seq(), f![Sequence]);
        assert_eq!(f![Sequence, s!(x)].flatten_seq(), s!(x));
        assert_eq!(
            f![Sequence, s!(x), s!(y)].flatten_seq(),
            f![Sequence, s!(x), s!(y)]
        );
        assert_eq!(
            f![
                Sequence,
                s!(x),
                f![Sequence, s!(y), s!(z), f![Sequence, s!(a)]],
                s!(b)
            ]
            .flatten_seq(),
            f![Sequence, s!(x), s!(y), s!(z), s!(a), s!(b)]
        );
    }
}

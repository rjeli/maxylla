use crate::types::*;
use std::cmp::Ordering;
use std::collections::HashMap;

impl Subs {
    fn null() -> Self {
        Subs {
            subs: HashMap::new(),
            num_constants: 0,
        }
    }
    fn add_constant(&self) -> Self {
        let s = self.clone();
        let nc = s.num_constants;
        Subs {
            num_constants: nc + 1,
            ..s
        }
    }
}

fn fail() -> UnifyResult {
    Err(UnifyError::Failure)
}

fn succeed() -> UnifyResult {
    Ok(Subs::null())
}

fn constant() -> UnifyResult {
    Ok(Subs::null().add_constant())
}

fn guard(cond: bool) -> UnifyResult {
    if cond {
        succeed()
    } else {
        fail()
    }
}

pub fn run_unify(env: &Env, patt: &Expr, expr: &Expr) -> EvalResult<Option<Subs>> {
    match unify(env, patt, expr) {
        Ok(subs) => Ok(Some(subs)),
        Err(UnifyError::Failure) => Ok(None),
        Err(UnifyError::Error(e)) => Err(e),
    }
}

pub fn unify(env: &Env, patt: &Expr, expr: &Expr) -> UnifyResult {
    match (patt, expr) {
        (Expr::Sym(ps), Expr::Sym(es)) if ps == es => constant(),
        (Expr::Num(pn), Expr::Num(en)) if pn == en => constant(),
        (Expr::Form(pf), expr) => {
            let (ph, pt) = pf.split_first().unwrap();
            // check special patterns
            match &*ph {
                Expr::Sym(phs) => match &phs[..] {
                    "Blank" => {
                        if pt.len() == 0 {
                            return succeed();
                        } else {
                            let head = pt[0].as_sym().map(|s| s.to_owned());
                            guard(head.is_some() && expr.head() == head)?;
                            return constant();
                        }
                    }
                    "Pattern" => {
                        let name = pt[0].as_sym().ok_or(UnifyError::Failure)?;
                        let body = &pt[1];
                        let mut subs = unify(env, body, expr)?;
                        assert!(!subs.subs.contains_key(name));
                        subs.subs.insert(name.to_owned(), expr.clone());
                        return Ok(subs);
                    }
                    "Condition" => {
                        let body = &pt[0];
                        let cond = &pt[1];
                        let subs = unify(env, body, expr)?;
                        let mut env2 = env.clone();
                        let cond2 = subs.replace(cond);
                        return match env2.eval(&cond2) {
                            Ok(e) if e == s!(True) => Ok(subs),
                            Err(e) => Err(UnifyError::Error(e)),
                            _ => fail(),
                        };
                    }
                    _ => (),
                },
                _ => (),
            };
            // otherwise just unify as a form
            let ef = expr.as_form().ok_or(UnifyError::Failure)?;
            unify_seq(env, pf, ef)
        }
        (_, _) => fail(),
    }
}

#[derive(Debug, Eq, PartialEq)]
enum Card {
    One,
    Many1,
    Many0,
}

impl Card {
    fn from(patt: &Expr) -> Self {
        let head: Option<&str> = patt.as_form().map(|es| es[0].as_sym()).flatten();
        match head {
            Some("BlankNullSequence") => Card::Many0,
            Some("BlankSequence") => Card::Many1,
            _ => Card::One,
        }
    }
}

fn detect_cardinality(patt: &Expr) -> (Card, Expr) {
    let head: Option<&str> = patt.as_form().map(|es| es[0].as_sym()).flatten();
    match head {
        Some("Pattern") => {
            let pf = patt.as_form().unwrap();
            let mut v = vec![];
            v.push(s!(Pattern));
            v.push(pf[1].clone());
            let (card, _) = detect_cardinality(&pf[2]);
            let mut new_body = pf[2].as_form().unwrap().to_vec();
            new_body[0] = s!(Blank);
            v.push(Expr::Form(new_body));
            (card, Expr::Form(v))
        }
        _ => (Card::from(patt), patt.clone()),
    }
}

fn unify_seq(env: &Env, patts: &[Expr], exprs: &[Expr]) -> UnifyResult {
    // simple greedy unification of sequences.
    // so f[x_,xs___] works, but f[xs___,x_] doesn't.
    // println!("unify_seq {:?} {:?}", patts, exprs);
    let mut patts = patts.to_vec();
    let mut subs = Subs::null();
    let mut exprs = exprs.iter().map(|e| e.clone());
    for i in 0..patts.len() {
        let exprs_ref = &mut exprs;
        let (card, patt) = detect_cardinality(&patts[i]);
        let expr = match card {
            Card::One => exprs_ref.next().ok_or(UnifyError::Failure)?,
            Card::Many0 => {
                let mut v = vec![s!(Sequence)];
                v.extend(exprs_ref);
                Expr::Form(v)
            }
            Card::Many1 => {
                let mut v = vec![s!(Sequence)];
                v.push(exprs_ref.next().ok_or(UnifyError::Failure)?);
                v.extend(exprs_ref);
                Expr::Form(v)
            }
        };
        /*
        println!(
            "i: {}/{} card: {:?} patt: {} expr: {}",
            i,
            patts.len() - 1,
            card,
            patt,
            expr
        );
        */
        let new_subs = unify(env, &patt, &expr)?;
        for j in i..patts.len() {
            patts[j] = new_subs.reify(&patts[j]);
        }
        subs.merge(new_subs);
    }
    guard(exprs.next() == None)?;
    Ok(subs)
}

impl Subs {
    fn merge(&mut self, subs: Subs) {
        // extend, asserting there are no dupes.
        let old_sz = self.subs.len() + subs.subs.len();
        self.subs.extend(subs.subs);
        self.num_constants += subs.num_constants;
        assert_eq!(self.subs.len(), old_sz);
    }
    pub fn reify(&self, expr: &Expr) -> Expr {
        match expr {
            Expr::Form(es) => {
                let (eh, et) = es.split_first().unwrap();
                match &*eh {
                    Expr::Sym(ehs) if ehs == "Pattern" => {
                        let name = match &et[0] {
                            Expr::Sym(name) => name,
                            _ => panic!(),
                        };
                        // assume body is identical..
                        if self.subs.contains_key(name) {
                            return self.subs[name].clone();
                        }
                    }
                    _ => (),
                };
                let es = es.iter().map(|e| self.reify(e)).collect::<Vec<_>>();
                Expr::Form(es)
            }
            expr => expr.clone(),
        }
    }
    pub fn replace(&self, expr: &Expr) -> Expr {
        match expr {
            Expr::Sym(s) if self.subs.contains_key(s) => self.subs[s].clone(),
            Expr::Form(es) => Expr::Form(es.iter().map(|e| self.replace(e)).collect::<Vec<_>>()),
            _ => expr.clone(),
        }
    }
}

impl Ord for Subs {
    fn cmp(&self, other: &Self) -> Ordering {
        self.num_constants.cmp(&other.num_constants)
    }
}

impl PartialOrd for Subs {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;
    use maplit::hashmap;

    macro_rules! succs {
        ( $p:expr, $e:expr ) => {
            assert!(unify(&Env::bare(), &p!($p), &p!($e)).is_ok());
        };
        ( $p:expr, $e:expr, c: $c:expr ) => {
            let subs = Subs {
                num_constants: $c,
                ..Subs::null()
            };
            assert_eq!(unify(&Env::bare(), &p!($p), &p!($e)), Ok(subs));
        };
    }
    macro_rules! fails {
        ( $p:expr, $e:expr ) => {
            assert_eq!(unify(&Env::bare(), &p!($p), &p!($e)), fail())
        };
    }
    macro_rules! binds {
        ( $p:expr, $e:expr, c: $c:expr $(, $name:ident => $val:expr )* $(,)? ) => {
            let subs = hashmap![ $( stringify!($name).to_owned() => $val ),* ];
            let result = unify(&Env::bare(), &p!($p), &p!($e));
            assert_eq!(result, Ok(Subs { subs, num_constants: $c, ..Subs::null() }))
        };
        ( $p:expr, $e:expr $(, $name:ident => $val:expr )* $(,)? ) => {
            let subs = hashmap![ $( stringify!($name).to_owned() => $val ),* ];
            let result = unify(&Env::bare(), &p!($p), &p!($e));
            assert!(result.is_ok());
            assert_eq!(result.unwrap().subs, subs);
        };
        // (
    }

    #[test]
    fn pattern_reify() {
        let subs = Subs {
            subs: hashmap!["x".to_owned() => n!(0)],
            num_constants: 0,
        };
        assert_eq!(subs.reify(&s!(x)), s!(x));
        assert_eq!(subs.reify(&s!(y)), s!(y));
        // reifies bare pattern
        assert_eq!(subs.reify(&f![Pattern, s!(x), n!(1)]), n!(0));
        // reifies pattern inside form
        assert_eq!(
            subs.reify(&f![Foo, n!(123), f![Pattern, s!(x), n!(1)], s!(y)]),
            f![Foo, n!(123), n!(0), s!(y)]
        );
    }

    #[test]
    fn pattern_detect_card() {
        assert_eq!(detect_cardinality(&p!("x")), (Card::One, s!(x)));
        assert_eq!(detect_cardinality(&p!("0")), (Card::One, n!(0)));
        assert_eq!(detect_cardinality(&p!("f[x]")), (Card::One, f![f, s!(x)]));
        assert_eq!(detect_cardinality(&p!("x_")), (Card::One, p!("x_")));
        assert_eq!(detect_cardinality(&p!("x__")), (Card::Many1, p!("x_")));
        assert_eq!(detect_cardinality(&p!("x___")), (Card::Many0, p!("x_")));
    }

    #[test]
    fn pattern_syms() {
        succs!("a", "a", c: 1);
        fails!("a", "b");
        fails!("b", "a");
    }

    #[test]
    fn pattern_nums() {
        succs!("0", "0", c: 1);
        succs!("123", "123", c: 1);
        fails!("10", "123");
    }

    #[test]
    fn pattern_forms() {
        succs!("f[x]", "f[x]", c: 2);
        fails!("f[x]", "g[x]");
        fails!("f[x]", "f[y]");
    }

    #[test]
    fn pattern_basic_subs() {
        binds!("x_", "0", c: 0, x => n!(0));
        binds!("x_", "y", c: 0, x => s!(y));
        binds!("x_", "x", c: 0, x => s!(x));
        binds!("x_", "x", c: 0, x => s!(x));
        binds!("f[x_]", "f[0]", c: 1, x => n!(0));
        binds!("f_[x]", "g[x]", c: 1, f => s!(g));
        binds!("f_[x_]", "g[y]", c: 0, 
            f => s!(g), x => s!(y));
        // for self-referential patterns, each additional match
        // adds a constant
        binds!("f[x_,x_]", "f[0,0]", c: 2, x => n!(0));
        fails!("f[x_,x_]", "f[0,1]");
        fails!("f[x_,g[x_]]", "f[0,g[1]]");
        binds!("f_[x_,f_[x_]]", "g[0,g[0]]", c: 2,
            f => s!(g), x => n!(0));
    }

    #[test]
    fn pattern_basic_seq_subs() {
        binds!("f[xs___]", "f[]", c: 1, 
            xs => f![Sequence]);
        binds!("f[xs___]", "f[0,1,2]", c: 1, 
            xs => p!("Sequence[0,1,2]"));
        binds!("f[x_,xs___]", "f[0,1,2]", c: 1,
            x => n!(0),
            xs => p!("Sequence[1,2]"));
    }

    #[test]
    fn pattern_heads() {
        succs!("x_List", "List[1,2,3]");
        fails!("x_List", "Foo[1,2,3]");
        succs!("x_Integer", "0");
        fails!("x_Integer", "foo");
        succs!("f[x_Integer]", "f[0]");
        fails!("f[x_Integer]", "f[a]");
    }

    #[test]
    fn pattern_cond() {
        succs!("a/;True", "a");
        fails!("a/;False", "a");
        succs!("x_/;True", "a");
        fails!("x_/;False", "a");
        succs!("x_/;x", "True");
        fails!("x_/;x", "False");
    }
}

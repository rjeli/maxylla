use crate::types::*;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

impl Subs {
    fn null() -> Self {
        Subs {
            subs: HashMap::new(),
            num_constants: 0,
            max_depth: 0,
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
    fn add_depth(&self) -> Self {
        let s = self.clone();
        let md = s.max_depth;
        Subs {
            max_depth: md + 1,
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
    // println!("unifying {} and {}", patt, expr);
    match (patt, expr) {
        (Expr::Sym(ps), Expr::Sym(es)) if ps == es => constant(),
        (Expr::Num(pn), Expr::Num(en)) if pn == en => constant(),
        (Expr::Form(pf), expr) => {
            let (ph, pt) = pf.split_first().unwrap();
            // check special patterns
            match &**ph {
                Expr::Sym(phs) => match &phs[..] {
                    "Blank" => {
                        if pt.len() == 0 {
                            return succeed();
                        } else {
                            let head = pt[0].as_sym();
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
                        guard(pt.len() == 2)?;
                        let body = &pt[0];
                        let cond = &pt[1];
                        let subs = unify(env, body, expr)?;
                        let mut env2 = env.clone();
                        let cond2 = subs.replace(cond);
                        return match env2.eval(&cond2) {
                            Ok(e) if e == s!(True) => Ok(subs.add_constant()),
                            Err(e) => Err(UnifyError::Error(e)),
                            _ => fail(),
                        };
                    }
                    "Verbatim" => {
                        let s = pt[0].as_sym().ok_or(UnifyError::Failure)?;
                        if let Expr::Sym(es) = expr {
                            if s == es {
                                return constant();
                            }
                        }
                    }
                    "Alternatives" => {
                        for arg in pt {
                            if let Ok(subs) = unify(env, arg, expr) {
                                return Ok(subs);
                            }
                        }
                        return Err(UnifyError::Failure);
                    }
                    _ => (),
                },
                _ => (),
            };
            // otherwise just unify as a form
            if let Some(ef) = expr.as_form() {
                if let Ok(subs) = unify_seq(env, pf, ef).map(|s| s.add_depth()) {
                    return Ok(subs);
                }
            }
            if let Some(phs) = ph.as_sym() {
                if env.has_attr(phs, Attr::OneIdentity) && !expr.has_head(phs) {
                    let wrapped = Expr::from_ref_vec(vec![ph.clone(), Rc::new(expr.clone())]);
                    if let Ok(subs) = unify(env, patt, &wrapped) {
                        return Ok(subs);
                    }
                }
            }
            fail()
        }
        (_, _) => fail(),
    }
}

#[derive(Debug, Eq, PartialEq)]
enum Card {
    Opt,
    One,
    Many0,
    Many1,
}

impl Card {
    fn from(patt: &Expr) -> Self {
        let head: Option<&str> = patt.as_form().map(|es| es[0].as_sym()).flatten();
        match head {
            Some("BlankNullSequence") => Card::Many0,
            Some("BlankSequence") => Card::Many1,
            Some("Optional") => Card::Opt,
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
            v.push(Rc::new(s!(Pattern)));
            v.push(pf[1].clone());
            let (card, _) = detect_cardinality(&*pf[2]);
            let mut new_body = pf[2].as_form().unwrap().to_vec();
            new_body[0] = Rc::new(s!(Blank));
            v.push(Rc::new(Expr::from_ref_vec(new_body)));
            (card, Expr::from_ref_vec(v))
        }
        Some("Optional") => (Card::from(patt), (*patt.as_form().unwrap()[1]).clone()),
        _ => (Card::from(patt), patt.clone()),
    }
}

fn unify_seq(env: &Env, prefs: &[Eref], erefs: &[Eref]) -> UnifyResult {
    // simple greedy unification of sequences.
    // so f[x_,xs___] works, but f[xs___,x_] doesn't.
    // println!("unify_seq {:?} {:?}", patts, exprs);
    let mut erefs = erefs.iter().cloned();
    let mut all_subs = vec![];
    for i in 0..prefs.len() {
        let erefs_ref = &mut erefs;
        let (card, patt) = detect_cardinality(&*prefs[i]);
        let eref = match card {
            Card::One => erefs_ref.next().ok_or(UnifyError::Failure)?,
            Card::Opt => match erefs_ref.next() {
                Some(e) => e,
                None => Rc::new(f![Default, (*prefs[0]).clone()]),
            },
            Card::Many0 => {
                let mut v = vec![Rc::new(s!(Sequence))];
                v.extend(erefs_ref);
                Rc::new(Expr::from_ref_vec(v))
            }
            Card::Many1 => {
                let mut v = vec![Rc::new(s!(Sequence))];
                v.push(erefs_ref.next().ok_or(UnifyError::Failure)?);
                v.extend(erefs_ref);
                Rc::new(Expr::from_ref_vec(v))
            }
        };
        let new_subs = unify(env, &patt, &*eref)?;
        all_subs.push(new_subs);
    }
    // make sure we consumed the whole sequence
    guard(erefs.next() == None)?;
    let mut subs = Subs::null();
    for s in all_subs {
        subs.merge(s)?;
    }
    Ok(subs)
}

impl Subs {
    fn merge(&mut self, other: Subs) -> UnifyResultT<()> {
        // self.subs.extend(subs.subs);
        for (name, val) in other.subs {
            if self.subs.contains_key(&name) {
                guard(self.subs[&name] == val)?;
                self.num_constants += 1;
            } else {
                self.subs.insert(name, val);
            }
        }
        self.num_constants += other.num_constants;
        self.max_depth = self.max_depth.max(other.max_depth);
        Ok(())
    }
    pub fn reify(&self, expr: &Expr) -> Expr {
        match expr {
            Expr::Form(es) => {
                let (eh, et) = es.split_first().unwrap();
                match &**eh {
                    Expr::Sym(ehs) if ehs == "Pattern" => {
                        let name = match &*et[0] {
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
                Expr::from_vec(es)
            }
            expr => expr.clone(),
        }
    }
    pub fn replace(&self, expr: &Expr) -> Expr {
        match expr {
            Expr::Sym(s) if self.subs.contains_key(s) => self.subs[s].clone(),
            Expr::Form(es) => {
                Expr::from_vec(es.iter().map(|e| self.replace(e)).collect::<Vec<_>>())
            }
            _ => expr.clone(),
        }
    }
}

impl Ord for Subs {
    fn cmp(&self, other: &Self) -> Ordering {
        self.max_depth
            .cmp(&other.max_depth)
            .then(self.num_constants.cmp(&other.num_constants))
            .then(self.subs.len().cmp(&other.subs.len()))
    }
}

impl PartialOrd for Subs {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Expr {
    pub fn patterns_to_gensyms(self, key: usize, names: &mut HashSet<String>) -> Self {
        if self.has_head("Pattern") {
            let es = self.as_form().unwrap();
            let name = es[1].as_sym().unwrap();
            names.insert(name.to_owned());
            let body = &es[2];
            let new_name = format!("{}~{}", name, key);
            f![Pattern, Expr::Sym(new_name), (&**body).clone()]
        } else {
            match self {
                Expr::Form(es) => Expr::from_vec(
                    es.iter()
                        .map(|e| (&**e).clone().patterns_to_gensyms(key, names))
                        .collect(),
                ),
                e => e,
            }
        }
    }
    pub fn conds_to_gensyms(self, key: usize, names: &HashSet<String>) -> Self {
        if self.has_head("Condition") {
            let es = self.as_form().unwrap();
            let body = &es[1];
            let cond = &es[2];
            let new_cond = (&**cond).clone().syms_to_gensyms(key, names);
            f![Condition, (&**body).clone(), new_cond]
        } else {
            match self {
                Expr::Form(es) => Expr::from_vec(
                    es.iter()
                        .map(|e| (&**e).clone().conds_to_gensyms(key, names))
                        .collect(),
                ),
                e => e,
            }
        }
    }
    pub fn syms_to_gensyms(self, key: usize, names: &HashSet<String>) -> Self {
        match self {
            Expr::Sym(s) if names.contains(&s) => Expr::Sym(format!("{}~{}", s, key)),
            Expr::Form(es) => Expr::from_vec(
                es.iter()
                    .map(|e| (&**e).clone().syms_to_gensyms(key, names))
                    .collect(),
            ),
            _ => self,
        }
    }
    pub fn gensymify(self, rhs: &Expr, key: usize) -> (Self, Self) {
        let mut names = HashSet::new();
        let lhs = self.patterns_to_gensyms(key, &mut names);
        let lhs = lhs.conds_to_gensyms(key, &names);
        let rhs = rhs.clone().syms_to_gensyms(key, &names);
        (lhs, rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;
    use maplit::hashmap;

    #[test]
    fn test_patterns_to_gensyms() {
        let mut s = HashSet::new();
        assert_eq!(s!(a).patterns_to_gensyms(123, &mut s), s!(a));
        assert_eq!(n!(0).patterns_to_gensyms(123, &mut s), n!(0));
        assert_eq!(
            f![Foo, s!(x)].patterns_to_gensyms(123, &mut s),
            f![Foo, s!(x)]
        );
        assert_eq!(s, HashSet::new());

        assert_eq!(
            f![Pattern, s!(x), f![Blank]].patterns_to_gensyms(123, &mut s),
            f![Pattern, Expr::Sym("x~123".to_owned()), f![Blank]]
        );
        let mut s2 = HashSet::new();
        s2.insert("x".to_owned());
        assert_eq!(s, s2);
        assert_eq!(
            f![Foo, s!(3), f![Pattern, s!(x), f![Blank]]].patterns_to_gensyms(123, &mut s),
            f![
                Foo,
                s!(3),
                f![Pattern, Expr::Sym("x~123".to_owned()), f![Blank]]
            ]
        );
    }

    #[test]
    fn test_gensymify() {
        assert_eq!(
            f![Pattern, s!(x), f![Blank]].gensymify(&s!(x), 123),
            (
                f![Pattern, Expr::Sym("x~123".to_owned()), f![Blank]],
                Expr::Sym("x~123".to_owned())
            )
        );
    }

    macro_rules! succs {
        ( $p:expr, $e:expr ) => {
            assert!(unify(&Env::bare(), &p!($p), &p!($e)).is_ok());
        };
        ( $p:expr, $e:expr, c: $c:expr, d: $d:expr ) => {
            let subs = Subs {
                num_constants: $c,
                max_depth: $d,
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
        ( $p:expr, $e:expr, c: $c:expr, d: $d:expr $(, $name:ident => $val:expr )* $(,)? ) => {
            let subs = hashmap![ $( stringify!($name).to_owned() => $val ),* ];
            let result = unify(&Env::bare(), &p!($p), &p!($e));
            assert_eq!(result, Ok(Subs {
                subs,
                num_constants: $c,
                max_depth: $d,
                ..Subs::null()
            }))
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
            max_depth: 0,
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
        succs!("a", "a", c: 1, d: 0);
        fails!("a", "b");
        fails!("b", "a");
    }

    #[test]
    fn pattern_nums() {
        succs!("0", "0", c: 1, d: 0);
        succs!("123", "123", c: 1, d: 0);
        fails!("10", "123");
    }

    #[test]
    fn pattern_forms() {
        succs!("f[x]", "f[x]", c: 2, d: 1);
        fails!("f[x]", "g[x]");
        fails!("f[x]", "f[y]");
    }

    #[test]
    fn pattern_basic_subs() {
        binds!("x_", "0", c: 0, d: 0,
            x => n!(0));
        binds!("x_", "y", c: 0, d: 0,
            x => s!(y));
        binds!("x_", "x", c: 0, d: 0,
            x => s!(x));
        binds!("x_", "x", c: 0, d: 0,
            x => s!(x));
        binds!("f[x_]", "f[0]", c: 1, d: 1,
            x => n!(0));
        binds!("f_[x]", "g[x]", c: 1, d: 1,
            f => s!(g));
        binds!("f_[x_]", "g[y]", c: 0, d: 1,
            f => s!(g), x => s!(y));
        // for self-referential patterns, each additional match
        // adds a constant
        binds!("f[x_,x_]", "f[0,0]", c: 2, d: 1,
            x => n!(0));
        fails!("f[x_,x_]", "f[0,1]");
        fails!("f[x_,g[x_]]", "f[0,g[1]]");
        binds!("f_[x_,f_[x_]]", "g[0,g[0]]", c: 2, d: 2,
            f => s!(g), x => n!(0));
    }

    #[test]
    fn pattern_basic_seq_subs() {
        binds!("f[xs___]", "f[]", c: 1, d: 1,
            xs => f![Sequence]);
        binds!("f[xs___]", "f[0,1,2]", c: 1, d: 1,
            xs => p!("Sequence[0,1,2]"));
        binds!("f[x_,xs___]", "f[0,1,2]", c: 1, d: 1,
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

    #[test]
    fn pattern_verbatim() {
        fails!("Condition[x]", "Condition[x]");
        succs!("Verbatim[Condition][x]", "Condition[x]", c: 2, d: 1);
    }
}

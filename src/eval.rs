use std::collections::HashMap;
use std::convert::TryInto;
use std::default::Default;
use std::fs;
use std::str::FromStr;

use crate::pattern::run_unify;
use crate::{parse::parse, s, types::*};

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
        if self.trace {
            println!("~e {}{}", "  ".repeat(depth.try_into().unwrap()), e);
        }
        match e {
            Expr::Form(es) => {
                let (head, args) = es.split_first().ok_or(EvalError::new("no head"))?;
                let head = self.eval_at(head, depth + 1)?;
                let head_sym = match head.clone() {
                    Expr::Sym(s) => Ok(s),
                    _ => Err(EvalError::new(&format!("head not a sym: {:?}", head))),
                }?;
                /* flatten sequences (?) */
                let args = Expr::flatten_seqs(args);
                /*
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
                */
                /* dispatch to prim */
                if head_sym.starts_with("Prim`") {
                    return self.eval_prim(&head_sym, &args);
                }
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
                // now expr is our canonical expression to eval.
                println!("evaluating: {}", expr);
                if let Some(downs) = self.downs.get(&head_sym) {
                    println!("downs:");
                    for (lhs, rhs) in downs {
                        println!("  {} -> {}", lhs, rhs);
                    }
                    let mut candidates = vec![];
                    for (lhs, rhs) in downs {
                        if let Some(subs) = run_unify(lhs, &expr)? {
                            candidates.push((subs, rhs));
                        }
                    }
                    println!("cands:");
                    for (subs, rhs) in &candidates {
                        println!("  {} with {:?}", rhs, subs);
                    }
                    if let Some((subs, rhs)) = candidates.first() {
                        let reified = subs.replace(&rhs);
                        println!("reified: {}", reified);
                        let reiflats = Expr::flatten_seqs(&[reified]);
                        let reiflat = reiflats.first().unwrap();
                        println!("reiflat: {}", reiflat);
                        return self.eval(&reiflat);
                    }
                }
                Ok(expr)
            }
            Expr::Sym(s) => {
                let own = self.owns.get(s).map(|e2| e2.clone());
                match own {
                    Some(e2) => self.eval_at(&e2, depth + 1),
                    None => Ok(Expr::Sym(s.clone())),
                }
            }
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

    fn eval_prim(&mut self, prim_head: &str, args: &[Expr]) -> EvalResult<Expr> {
        if self.trace {
            println!("~p {} {:?}", prim_head, args);
        }
        // println!("evaling prim: {} {:?}", prim_head, args);
        match prim_head {
            "Prim`SetAttributes" => match args {
                [Expr::Sym(s), Expr::Form(attr_list)] => {
                    let (attrs_head, attrs_args) =
                        attr_list.split_first().ok_or(EvalError::new("bad args"))?;
                    if attrs_head != &s!(List) {
                        return Err(EvalError::new("bad args"));
                    }
                    for arg in attrs_args {
                        if let Expr::Sym(a) = arg {
                            self.set_attr(s, &a);
                        } else {
                            return Err(EvalError::new("bad setattr rhs (not sym)"));
                        }
                    }
                    Ok(Expr::null())
                }
                _ => Err(EvalError::new(&format!(
                    "bad Prim`SetAttributes args: {:?}",
                    args
                ))),
            },
            "Prim`AddDownValue" => {
                if let Expr::Sym(s) = &args[0] {
                    if !self.downs.contains_key(s) {
                        self.downs.insert(s.clone(), vec![]);
                    }
                    self.downs
                        .get_mut(s)
                        .unwrap()
                        .push((args[1].clone(), args[2].clone()));
                    println!("added downval on: {} {} {}", args[0], args[1], args[2]);
                    Ok(Expr::null())
                } else {
                    Err(EvalError::new("bad adddownvalue lhs (not sym)"))
                }
            }
            "Prim`AddOwnValue" => {
                if let Expr::Sym(s) = &args[0] {
                    self.owns.insert(s.clone(), args[1].clone());
                    Ok(Expr::null())
                } else {
                    Err(EvalError::new("bad adddownvalue lhs (not sym)"))
                }
            }
            "Prim`SetTrace" => {
                if let Expr::Sym(s) = &args[0] {
                    if s == "True" {
                        self.trace = true;
                    } else {
                        self.trace = false;
                    }
                    Ok(Expr::null())
                } else {
                    Err(EvalError::new("bad settrace arg (not sym)"))
                }
            }
            "Prim`PrintDownValues" => {
                for (s, downs) in &self.downs {
                    println!("{}: ", s);
                    for (lhs, rhs) in downs {
                        println!("  {} -> {}", lhs, rhs);
                    }
                }
                Ok(Expr::null())
            }
            _ => Err(EvalError::new(&format!(
                "no such primitive: {:?}",
                prim_head
            ))),
        }
    }

    /*
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
    */

    /*

    fn replace(&self, expr: &Expr, lhs: &Expr, rhs: &Expr) -> EvalResult<Expr> {
        match self.run_unify(lhs, expr)? {
            Some(info) => self.apply_bindings(rhs, &info.bindings),
            None => Ok(expr.clone()),
        }
    }

    fn replace_all(&self, expr: &Expr, lhs: &Expr, rhs: &Expr) -> EvalResult<Expr> {
        match self.run_unify(lhs, expr)? {
            Some(info) => self.apply_bindings(rhs, &info.bindings),
            None => match expr {
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
                    match self.run_unify(&Expr::Sym(k.to_owned()), e)? {
                        Some(_) => return Ok(v.clone()),
                        _ => (),
                    }
                }
                Ok(e.clone())
            }
        }
    }

    fn run_unify(&self, patt: &Expr, expr: &Expr) -> EvalResult<Option<MatchInfo>> {
        match self.unify(&[patt.clone()], &[expr.clone()]) {
            Ok((info, 1)) => Ok(Some(info)),
            Ok((info, _)) => Ok(None),
            Err(MatchError::Failure) => Ok(None),
            Err(MatchError::Error(e)) => Err(e),
        }
    }

    fn unify(&self, patts: &[Expr], exprs: &[Expr]) -> MatchResult {
        if self.trace {
            println!("~u {:?} with {:?}", patts, exprs);
        }

        if patts.len() == 0 {
            if exprs.len() == 0 {
                return MatchInfo::succeed(0);
            } else {
                return MatchInfo::fail();
            }
        }

        let (p_first, p_rest) = patts.split_first().unwrap();

        /* literals */
        if let Some((e_first, e_rest)) = exprs.split_first() {
            let literal_eq = match (p_first, e_first) {
                (Expr::Sym(s1), Expr::Sym(s2)) if s1 == s2 => true,
                (Expr::Num(n1), Expr::Num(n2)) if n1 == n2 => true,
                _ => false,
            };
            if literal_eq {
                return MatchInfo::constant(e_first.clone(), 1);
            }
        }

        if let Ok((p_head, p_args)) = p_first.to_split() {
            /* special pattern forms */
            match &p_head[..] {
                "Pattern" => {
                    let name = p_args[0].to_sym()?;
                    let (m1, c1) = self.unify(&[p_args[1].clone()], exprs)?;
                    let (m2, c2) = self.unify(p_rest, &exprs[c1..])?;
                    return MatchInfo::concat(&[m1.bound_as(name.clone()), m2], c1 + c2);
                }
                "Blank" => {
                    MatchInfo::guard(exprs.len() > 0)?;
                    return MatchInfo::value(exprs[0].clone(), 1);
                }
                _ => (),
            }
            /* any other form */
            /*
                        let (e_first, e_rest) = exprs.split_first().unwrap();
                        let (e_head, e_args) = e_first.split();
                        /* unify head */
                        let (mh, ch) = self.unify(&[p_head.clone()], &[e_head.clone()])?;
                        /* unify args */
                        let mut args_consumed = 0;
            */
        }

        MatchInfo::fail()

        /*
                match (patts, exprs) {
                    (Expr::Sym(s1), [Expr::Sym(s2)]) if s1 == s2 => MatchInfo::constant(),
                    (Expr::Num(n1), [Expr::Num(n2)]) if n1 == n2 => MatchInfo::constant(),
                    (Expr::Form(patt), exprs) => {
                        if patt.len() == 0 {
                            return MatchInfo::fail();
                        }
                        let (patt_head, patt_args) = patt.split_first().unwrap();

                        if let Expr::Sym(patt_sym) = patt_head {
                            match &patt_sym[..] {
                                "Pattern" => match patt_args {
                                    /* Pattern[x, patt], foo */
                                    [Expr::Sym(name), body] => {
                                        return self
                                            .unify(body, exprs)
                                            .map(|m| m.with_binding(name, f_args![Sequence, exprs]));
                                    }
                                    _ => return MatchInfo::fail(),
                                },
                                _ => (),
                            }
                        }

                        MatchInfo::fail()
                    }
        */

        /*
                    (Expr::Form(patt), expr) => {
                        if patt.len() == 0 {
                            return MatchInfo::fail();
                        }
                        let (patt_head, patt_args) = patt.split_first().unwrap();

                        if let Expr::Sym(patt_sym) = patt_head {
                            match &patt_sym[..] {
                                "Blank" => match patt_args {
                                    /* Blank[Integer], foo */
                                    [blank_head @ Expr::Sym(_)] => {
                                        let exprs = match expr {
                                            Expr::Form(exprs) => exprs,
                                            _ => return MatchInfo::fail(),
                                        };
                                        if exprs.len() == 0 {
                                            return MatchInfo::fail();
                                        }
                                        if exprs.first().unwrap() != blank_head {
                                            return MatchInfo::fail();
                                        }
                                        return MatchInfo::succeed();
                                    }
                                    /* Blank[], foo */
                                    [] => return MatchInfo::succeed(),
                                    _ => return MatchInfo::fail(),
                                },
                                "Pattern" => match patt_args {
                                    /* Pattern[x, patt], foo */
                                    [Expr::Sym(name), body] => {
                                        return self.unify(body, expr).map(|m| m.with_binding(name, expr));
                                    }
                                    _ => return MatchInfo::fail(),
                                },
                                "Sequence" => {
                                    /* Sequence[x,y], Sequence[z,w] */
                                    let exprs = match expr {
                                        Expr::Form(exprs) => exprs,
                                        _ => return MatchInfo::fail(),
                                    };
                                    if exprs.len() == 0 {
                                        return MatchInfo::fail();
                                    }
                                    let (expr_head, expr_args) = exprs.split_first().unwrap();
                                    if expr_head != &s!(Sequence) {
                                        return MatchInfo::fail();
                                    }
                                    /* rm for patt seqs */
                                    if patt_args.len() != expr_args.len() {
                                        return MatchInfo::fail();
                                    }
                                    let matches = patt_args
                                        .iter()
                                        .zip(expr_args)
                                        .map(|(p, e)| self.unify(p, e))
                                        .collect::<MatchResultT<Vec<_>>>()?;
                                    return MatchInfo::combine(&matches[..]);
                                }
                                _ => (),
                            }
                        }

                        let exprs = match expr {
                            Expr::Form(exprs) => Ok(exprs),
                            _ => return MatchInfo::fail(),
                        }?;
                        if exprs.len() == 0 {
                            return MatchInfo::fail();
                        }
                        let (expr_head, expr_args) = exprs.split_first().unwrap();

                        let head_match = self.unify(patt_head, expr_head)?;

                        let patt_args_seq = f_args!(Sequence, patt_args);
                        let expr_args_seq = f_args!(Sequence, expr_args);
                        self.unify(&patt_args_seq, &expr_args_seq)
                            .map(|info| info.nest())
                    }
        */
    }
    */
}

#[cfg(test)]
mod tests {
    use super::*;
    /*
        #[test]
        fn test_unify_literals() {
            let env = Env::new();
            assert_eq!(env.unify(&[s!(x)], &[s!(x)]), MatchInfo::constant(s!(x), 1));
            assert_eq!(env.unify(&[s!(x)], &[s!(y)]), MatchInfo::fail());
            assert_eq!(
                env.unify(&[s!(x)], &[s!(x), s!(y)]),
                MatchInfo::constant(s!(x), 1)
            );
            assert_eq!(env.unify(&[n!(0)], &[n!(0)]), MatchInfo::constant(n!(0), 1));
            assert_eq!(env.unify(&[n!(0)], &[n!(1)]), MatchInfo::fail());
            assert_eq!(
                env.unify(&[n!(0)], &[n!(0), n!(1)]),
                MatchInfo::constant(n!(0), 1)
            );
        }
        #[test]
        fn test_unify_patterns() {
            let env = Env::new();
            assert_eq!(
                env.unify(&[f![Pattern, s!(x), n!(0)]], &[n!(0)]),
                MatchInfo::constant(n!(0), 1).map(|(m, c)| (m.bound_as("x"), c))
            );
        }
        #[test]
        fn test_unify_blank() {
            let env = Env::new();
            assert_eq!(
                env.unify(&[f![Blank]], &[n!(0)]),
                MatchInfo::value(n!(0), 1)
            );
            assert_eq!(
                env.unify(&[f![Pattern, s!(x), f![Blank]]], &[n!(0)]),
                MatchInfo::value(n!(0), 1).map(|(m, c)| (m.bound_as("x"), c))
            );
        }
        #[test]
        fn test_unify_form() {
            let env = Env::new();
            let mut bindings = HashMap::new();
            bindings.insert("y".to_owned(), n!(10));
            assert_eq!(
                env.unify(
                    &[f![Foo, s!(x), f![Pattern, s!(y), f![Blank]]]],
                    &[f![Foo, s!(x), n!(10)]]
                ),
                Ok((
                    MatchInfo {
                        expr: f![Foo, s!(x), n!(10)],
                        bindings,
                        num_constants: 2,
                        max_nest: 1,
                    },
                    3
                ))
            );
        }
    */

    /*
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
    */
}

/*
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
*/

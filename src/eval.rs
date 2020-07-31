use permutohedron::Heap;
use std::cmp::Ordering;
use std::collections::HashSet;
use std::convert::TryInto;
use std::default::Default;
use std::fs;
use std::str::FromStr;
use std::sync::atomic;

use crate::pattern::run_unify;
use crate::util::insert_or_append;
use crate::{parse::parse, s, types::*};

static GENSYM_CNT: atomic::AtomicUsize = atomic::AtomicUsize::new(0);
fn next_gensym() -> usize {
    GENSYM_CNT.load(atomic::Ordering::SeqCst)
}

impl Env {
    pub fn bare() -> Env {
        Default::default()
    }

    pub fn new() -> Env {
        let mut env = Env::bare();
        let entries = fs::read_dir("stdlib").unwrap();
        for entry in entries {
            let path = entry.unwrap().path();
            println!("parsing stdlib {}", path.display());
            let contents = fs::read_to_string(path).unwrap();
            let parsed = parse(&contents).unwrap();
            println!("evaling stdlib");
            env.eval(&parsed).unwrap();
        }
        env
    }

    pub fn eval(&mut self, e: &Expr) -> EvalResult<Expr> {
        self.eval_fix(e, 0)
    }

    fn eval_fix(&mut self, e: &Expr, depth: i32) -> EvalResult<Expr> {
        let mut last = e.clone();
        let mut n = 0;
        loop {
            let evaled = self.eval_at(&last, depth)?;
            if evaled == last {
                // println!("fix point reached on {}", evaled);
                return Ok(evaled);
            }
            n += 1;
            if n > 1000 {
                return Err(EvalError::new(&format!(
                    "fix point exhaustion on {} -> {}",
                    last, evaled,
                )));
            }
            last = evaled;
        }
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
                let head = self.eval_fix(head, depth + 1)?;
                let (head_sym, is_sub) = match head.clone() {
                    Expr::Sym(s) => Ok((s, false)),
                    Expr::Form(es) => {
                        let sub_head = es[0].as_sym().unwrap();
                        Ok((sub_head.to_owned(), true))
                    }
                    _ => Err(EvalError::new(&format!("head not a sym: {:?}", head))),
                }?;
                // skip fixed point eval for CompoundExpression
                if &head_sym == "CompoundExpression" {
                    let mut last = Expr::null();
                    for a in args {
                        last = self.eval_fix(a, depth + 1)?;
                    }
                    return Ok(last);
                }
                let args = Expr::flatten_seqs(args);
                let args = if self.has_attr(&head_sym, Attr::Flat) {
                    args.iter()
                        .flat_map(|a| a.clone().flat(&head_sym))
                        .collect::<Vec<_>>()
                } else {
                    args
                };
                if self.has_attr(&head_sym, Attr::OneIdentity) && args.len() == 1 {
                    return Ok(args[0].clone());
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
                                self.eval_fix(first, depth + 1)?
                            };
                            let rest = if self.has_attr(&head_sym, Attr::HoldRest) {
                                rest.to_vec()
                            } else {
                                rest.iter()
                                    .map(|a| self.eval_fix(a, depth + 1))
                                    .collect::<EvalResult<Vec<Expr>>>()?
                            };
                            let mut v = vec![first];
                            v.extend(rest);
                            v
                        }
                        None => vec![],
                    }
                };
                /* dispatch to prim */
                if head_sym.starts_with("Prim`") {
                    let res = self.eval_prim(&head_sym, &args);
                    if self.trace {
                        if let Ok(res) = &res {
                            println!(
                                "~p {}= {}",
                                "  ".repeat((depth + 1).try_into().unwrap()),
                                res
                            );
                        }
                    }
                    return res;
                }
                let mut v = vec![head.clone()];
                v.extend(args.clone());
                let expr = Expr::Form(v);
                // now expr is our canonical expression to eval.
                // println!("evaluating: {}", expr);
                if is_sub {
                    if let Some(subs) = self.subs.get(&head_sym) {
                        if let Some(replaced) = self.replace(&expr, subs)? {
                            return Ok(replaced);
                        }
                    }
                }
                if let Some(downs) = self.downs.get(&head_sym) {
                    if self.has_attr(&head_sym, Attr::Orderless) {
                        let mut margs = args.clone();
                        let heap = Heap::new(&mut margs);
                        for perm in heap {
                            let mut v = vec![head.clone()];
                            v.extend(perm.clone());
                            let pexpr = Expr::Form(v);
                            if let Some(replaced) = self.replace(&pexpr, downs)? {
                                return Ok(replaced);
                            }
                        }
                    } else {
                        if let Some(replaced) = self.replace(&expr, downs)? {
                            return Ok(replaced);
                        }
                    }
                }
                if self.has_attr(&head_sym, Attr::Orderless) {
                    let mut args = args.clone();
                    args.sort();
                    let mut v = vec![head.clone()];
                    v.extend(args);
                    Ok(Expr::Form(v))
                } else {
                    Ok(expr)
                }
            }
            Expr::Sym(s) => {
                let own = self.owns.get(s).map(|e2| e2.clone());
                match own {
                    Some(e2) => Ok(e2),
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

    fn replace(&self, expr: &Expr, rules: &[(Expr, Expr)]) -> EvalResult<Option<Expr>> {
        let mut candidates = vec![];

        let key = next_gensym();
        for (lhs, rhs) in rules {
            let (lhs, rhs) = lhs.clone().gensymify(rhs, key);
            if let Some(subs) = run_unify(self, &lhs, &expr)? {
                candidates.push((subs, rhs));
            }
        }
        candidates.sort_by(|a, b| b.0.cmp(&a.0));
        if let Some((subs, rhs)) = candidates.first() {
            let reified = subs.replace(&rhs);
            let flat = Expr::flatten_seqs(&[reified]);
            let reified = flat.first().unwrap();
            // return self.eval_fix(&reified, depth + 1);
            Ok(Some(reified.clone()))
        } else {
            Ok(None)
        }
    }

    fn eval_prim(&mut self, prim_head: &str, args: &[Expr]) -> EvalResult<Expr> {
        if self.trace {
            println!("~p {} {:?}", prim_head, args);
        }
        // println!("evaling prim: {} {:?}", prim_head, args);
        match prim_head {
            "Prim`Print" => {
                println!("// {}", args[0]);
                Ok(Expr::null())
            }
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
                            return Err(EvalError::new(&format!(
                                "bad setattr rhs (not sym): {}",
                                arg
                            )));
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
                let s = args[0].as_sym().unwrap().to_owned();
                /*
                let cnt = GENSYM_CNT.fetch_add(1, atomic::Ordering::SeqCst);
                let (lhs, rhs) = args[1].clone().gensymify(&args[2], cnt);
                */
                let (lhs, rhs) = (args[1].clone(), args[2].clone());
                insert_or_append(&mut self.downs, &s, (lhs, rhs));
                Ok(Expr::null())
            }
            "Prim`AddOwnValue" => {
                if let Expr::Sym(s) = &args[0] {
                    self.owns.insert(s.clone(), args[1].clone());
                    Ok(Expr::null())
                } else {
                    Err(EvalError::new(&format!("bad addownvalue lhs: {}", args[0])))
                }
            }
            "Prim`AddSubValue" => {
                let s = args[0].as_sym().unwrap();
                insert_or_append(
                    &mut self.subs,
                    &s.to_owned(),
                    (args[1].clone(), args[2].clone()),
                );
                Ok(Expr::null())
            }
            "Prim`OwnValues" => {
                let s = args[0].as_sym().unwrap();
                let mut v: Vec<Expr> = vec![s!(List)];
                if let Some(e) = self.owns.get(s) {
                    v.push(f![
                        RuleDelayed,
                        f![HoldPattern, Expr::Sym(s.to_owned())],
                        e.clone()
                    ]);
                }
                Ok(Expr::Form(v))
            }
            "Prim`DownValues" => {
                let s = args[0].as_sym().unwrap();
                let mut v = vec![s!(List)];
                if let Some(down) = self.downs.get(s) {
                    for (lhs, rhs) in down {
                        v.push(f![RuleDelayed, f![HoldPattern, lhs.clone()], rhs.clone()]);
                    }
                }
                Ok(Expr::Form(v))
            }
            "Prim`SubValues" => {
                let s = args[0].as_sym().unwrap();
                let mut v = vec![s!(List)];
                if let Some(sub) = self.subs.get(s) {
                    for (lhs, rhs) in sub {
                        v.push(f![RuleDelayed, f![HoldPattern, lhs.clone()], rhs.clone()]);
                    }
                }
                Ok(Expr::Form(v))
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
            "Prim`Plus" => {
                let x = args[0].as_num().ok_or(EvalError::new(&format!(
                    "tried to plus non num: {}",
                    args[0]
                )))?;
                let y = args[1]
                    .as_num()
                    .ok_or(EvalError::new("tried to plus non num"))?;
                return Ok(Expr::Num(x + y));
            }
            "Prim`Times" => {
                let x = args[0]
                    .as_num()
                    .ok_or(EvalError::new("tried to times non num"))?;
                let y = args[1]
                    .as_num()
                    .ok_or(EvalError::new("tried to times non num"))?;
                return Ok(Expr::Num(x * y));
            }
            "Prim`Replace" => {
                let expr = &args[0];
                let lhs = &args[1];
                let rhs = &args[2];
                /*
                if let Some(subs) = run_unify(self, lhs, expr)? {
                    Ok(subs.replace(rhs))
                } else {
                    Ok(expr.clone())
                }
                */
                if let Some(replaced) = self.replace(expr, &[(lhs.clone(), rhs.clone())])? {
                    Ok(replaced)
                } else {
                    Ok(expr.clone())
                }
            }
            "Prim`Cmp" => {
                let x = args[0].as_num().unwrap();
                let y = args[1].as_num().unwrap();
                Ok(match x.cmp(&y) {
                    Ordering::Less => s!(LT),
                    Ordering::Equal => s!(EQ),
                    Ordering::Greater => s!(GT),
                })
            }
            _ => Err(EvalError::new(&format!(
                "no such primitive: {:?}",
                prim_head
            ))),
        }
    }
}

#[cfg(test)]
mod tests {}

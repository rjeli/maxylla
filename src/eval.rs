use permutohedron::Heap;
use std::cmp::Ordering;
use std::convert::TryInto;
use std::default::Default;
use std::fs;
use std::str::FromStr;
use std::sync::atomic;
use std::thread;
use std::time::{Duration, SystemTime};

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

    pub fn eval(&mut self, expr: &Expr) -> EvalResult<Expr> {
        self.eval_fix(expr, 0)
    }

    fn eval_fix(&mut self, expr: &Expr, depth: i32) -> EvalResult<Expr> {
        let mut last = expr.clone();
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

    fn eval_at(&mut self, expr: &Expr, depth: i32) -> EvalResult<Expr> {
        if depth > 256 {
            return Err(EvalError::new("depth limit reached"));
        }
        if self.trace {
            println!("~e {}{}", "  ".repeat(depth.try_into().unwrap()), expr);
        }
        match expr {
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
                        .flat_map(|a| (**a).clone().flat(&head_sym))
                        .collect::<Vec<_>>()
                } else {
                    args
                };
                if self.has_attr(&head_sym, Attr::OneIdentity) && args.len() == 1 {
                    return Ok((*args[0]).clone());
                }
                /* evaluate args */
                let args = if self.has_attr(&head_sym, Attr::HoldAll) {
                    args.to_vec()
                } else {
                    match args.split_first() {
                        Some((first, rest)) => {
                            let first = if self.has_attr(&head_sym, Attr::HoldFirst) {
                                (**first).clone()
                            } else {
                                self.eval_fix(first, depth + 1)?
                            };
                            let rest = if self.has_attr(&head_sym, Attr::HoldRest) {
                                rest.to_vec()
                            } else {
                                let rs = rest
                                    .iter()
                                    .map(|a| self.eval_fix(&**a, depth + 1))
                                    .collect::<EvalResult<Vec<Expr>>>()?;
                                rs.into_iter().map(|r| Rc::new(r)).collect::<Vec<_>>()
                            };
                            let mut v = vec![Rc::new(first)];
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
                let mut v: Vec<Eref> = vec![Rc::new(head.clone())];
                v.extend_from_slice(&args.clone());
                let expr = Expr::from_ref_vec(v);
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
                        let mut margs: Vec<Eref> = args.to_vec();
                        let heap = Heap::new(&mut margs);
                        for perm in heap {
                            let mut v: Vec<Eref> = vec![Rc::new(head.clone())];
                            v.extend(perm.clone());
                            let pexpr = Expr::from_ref_vec(v);
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
                    let mut args: Vec<Eref> = args.to_vec();
                    args.sort();
                    let mut v: Vec<Eref> = vec![Rc::new(head.clone())];
                    v.extend(args);
                    Ok(Expr::from_ref_vec(v))
                } else {
                    Ok(expr)
                }
            }
            Expr::Sym(s) => {
                let own = self.owns.get(s);
                match own {
                    Some(e2) => Ok((**e2).clone()),
                    None => Ok(expr.clone()),
                }
            }
            Expr::Num(_) => Ok(expr.clone()),
        }
    }

    fn set_attr(&mut self, s: &str, attr_s: &str) {
        if !self.attrs.contains_key(s) {
            self.attrs.insert(s.to_owned(), vec![]);
        }
        let attr = Attr::from_str(attr_s).unwrap();
        self.attrs.get_mut(s).unwrap().push(attr);
    }

    pub fn has_attr(&self, s: &str, attr: Attr) -> bool {
        self.attrs
            .get(s)
            .map(|attrs| attrs.contains(&attr))
            .unwrap_or(false)
    }

    fn replace(&self, expr: &Expr, rules: &[(Eref, Eref)]) -> EvalResult<Option<Expr>> {
        let mut candidates = vec![];

        let key = next_gensym();
        for (lhs, rhs) in rules {
            let (lhs, rhs) = (&**lhs).clone().gensymify(rhs, key);
            if let Some(subs) = run_unify(self, &lhs, &expr)? {
                candidates.push((subs, rhs));
            }
        }
        candidates.sort_by(|a, b| b.0.cmp(&a.0));
        if let Some((subs, rhs)) = candidates.first() {
            let reified = subs.replace(&rhs);
            let flat = Expr::flatten_seqs(&[Rc::new(reified)]);
            let reified = flat.first().unwrap();
            // return self.eval_fix(&reified, depth + 1);
            Ok(Some((**reified).clone()))
        } else {
            Ok(None)
        }
    }

    fn eval_prim(&mut self, prim_head: &str, args: &[Eref]) -> EvalResult<Expr> {
        if self.trace {
            println!("~p {} {:?}", prim_head, args);
        }
        // println!("evaling prim: {} {:?}", prim_head, args);
        match prim_head {
            "Prim`Print" => {
                for arg in args {
                    print!("{} ", arg);
                }
                println!();
                Ok(Expr::null())
            }
            "Prim`SetAttributes" => {
                let s = args[0].as_sym().unwrap();
                let (_, attrs_args) = args[1].as_form().unwrap().split_first().unwrap();
                for arg in attrs_args {
                    let a = arg.as_sym().unwrap();
                    self.set_attr(s, &a);
                }
                Ok(Expr::null())
            }
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
                if let Expr::Sym(s) = &*args[0] {
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
                        (**e).clone()
                    ]);
                }
                Ok(Expr::from_vec(v))
            }
            "Prim`DownValues" => {
                let s = args[0].as_sym().unwrap();
                let mut v = vec![s!(List)];
                if let Some(down) = self.downs.get(s) {
                    for (lhs, rhs) in down {
                        v.push(f![
                            RuleDelayed,
                            f![HoldPattern, (**lhs).clone()],
                            (**rhs).clone()
                        ]);
                    }
                }
                Ok(Expr::from_vec(v))
            }
            "Prim`SubValues" => {
                let s = args[0].as_sym().unwrap();
                let mut v = vec![s!(List)];
                if let Some(sub) = self.subs.get(s) {
                    for (lhs, rhs) in sub {
                        v.push(f![
                            RuleDelayed,
                            f![HoldPattern, (**lhs).clone()],
                            (**rhs).clone()
                        ]);
                    }
                }
                Ok(Expr::from_vec(v))
            }
            "Prim`SetTrace" => {
                if let Expr::Sym(s) = &*args[0] {
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
                let x = args[0].as_num().unwrap();
                let y = args[1].as_num().unwrap();
                return Ok(Expr::Num(x + y));
            }
            "Prim`Times" => {
                let x = args[0].as_num().unwrap();
                let y = args[1].as_num().unwrap();
                return Ok(Expr::Num(x * y));
            }
            "Prim`Replace" => {
                let expr = args[0].clone();
                let lhs = args[1].clone();
                let rhs = args[2].clone();
                if let Some(replaced) = self.replace(&*expr, &[(lhs, rhs)])? {
                    Ok(replaced)
                } else {
                    Ok((*expr).clone())
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
            "Prim`Load" => {
                let path = args[0].as_form().unwrap()[1].as_sym().unwrap();
                println!("Prim`Load {}", path);
                let contents = fs::read_to_string(path).unwrap();
                let parsed = parse(&contents).unwrap();
                self.eval(&parsed)?;
                Ok(Expr::null())
            }
            "Prim`MicrosSinceEpoch" => {
                let ms = SystemTime::now()
                    .duration_since(SystemTime::UNIX_EPOCH)
                    .unwrap()
                    .as_micros();
                Ok(Expr::Num(ms.try_into().unwrap()))
            }
            "Prim`Sleep" => {
                let secs = args[0].as_num().unwrap();
                thread::sleep(Duration::from_secs(secs.try_into().unwrap()));
                Ok(Expr::null())
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

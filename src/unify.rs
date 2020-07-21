use crate::{f, s, types::*};
use std::collections::HashMap;
use std::default::Default;

pub fn unify(env: &Env, patt: Expr, exprs: &[Expr]) -> Box<dyn Iterator<Item = MatchResult>> {
    let is_literal = match patt {
        Expr::Sym(_) => true,
        Expr::Num(_) => true,
        _ => false,
    };
    if is_literal {
        if let Some((e_first, _)) = exprs.split_first() {
            if patt == *e_first {
                return Box::new(SingleUnif {
                    expr: e_first.clone(),
                    done: false,
                    constant: true,
                });
            }
        }
        return Box::new(NullUnif {});
    }
    let p_exprs = match patt {
        Expr::Form(es) => es,
        _ => unreachable!(),
    };
    let (p_head, p_args) = p_exprs.split_first().unwrap();

    /* special patterns */
    if let Ok(p_sym) = p_head.to_sym() {
        match &p_sym[..] {
            "Pattern" => {
                let name = p_args[0].to_sym().unwrap();
                return Box::new(BoundUnif {
                    inner: unify(env, p_args[1].clone(), exprs),
                    name,
                });
            }
            "Blank" => {
                if exprs.len() == 0 {
                    return Box::new(NullUnif {});
                }
                return Box::new(SingleUnif {
                    expr: exprs.first().unwrap().clone(),
                    done: false,
                    constant: false,
                });
            }
            "BlankSequence" => {
                return Box::new(SeqUnif {
                    exprs: exprs.to_vec(),
                    consume_next: 1,
                })
            }
            "BlankNullSequence" => {
                return Box::new(SeqUnif {
                    exprs: exprs.to_vec(),
                    consume_next: 0,
                })
            }
            _ => (),
        }
    }

    /* any other form (greedy) */
    let e_exprs = match &exprs[0] {
        Expr::Form(es) => es,
        _ => return Box::new(NullUnif {}),
    };
    let (e_head, e_args) = e_exprs.split_first().unwrap();
    /* unify the heads */
    let u_head = unify(env, p_head.clone(), &[e_head.clone()]);
    /* unify the args */
    let mut states: Vec<(MatchInfo, usize)> = vec![(Default::default(), 0)];
    for p in p_args {
        let mut new_states = vec![];
        for (i, c) in &states {
            println!("state {:?} {} e_args.len: {}", i, c, e_args.len());
            assert!(*c <= e_args.len());
            if *c < e_args.len() {
                for r in unify(env, p.clone(), &e_args[*c..]) {
                    println!("r: {:?}", r);
                    match r {
                        Ok((i2, c2)) => match MatchInfo::concat(&[(*i).clone(), i2], c + c2) {
                            Ok((i3, c3)) => new_states.push((i3, c3)),
                            _ => panic!(),
                        },
                        _ => panic!(),
                    }
                }
            }
        }
        states = new_states;
    }
    let n_e_args = e_args.len();
    Box::new(
        states
            .iter()
            .filter(move |(i, c)| *c == n_e_args)
            .map(move |(i, c)| Ok((i.clone(), *c))),
    )
}

struct SingleUnif {
    expr: Expr,
    done: bool,
    constant: bool,
}
impl Iterator for SingleUnif {
    type Item = MatchResult;
    fn next(&mut self) -> Option<MatchResult> {
        if !self.done {
            self.done = true;
            if self.constant {
                Some(MatchInfo::constant(self.expr.clone(), 1))
            } else {
                Some(MatchInfo::value(self.expr.clone(), 1))
            }
        } else {
            None
        }
    }
}

struct BoundUnif {
    inner: Box<dyn Iterator<Item = MatchResult>>,
    name: String,
}
impl Iterator for BoundUnif {
    type Item = MatchResult;
    fn next(&mut self) -> Option<MatchResult> {
        self.inner
            .next()
            .map(|m| m.map(|(i, c)| (i.bound_as(self.name.clone()), c)))
    }
}

struct NullUnif {}
impl Iterator for NullUnif {
    type Item = MatchResult;
    fn next(&mut self) -> Option<MatchResult> {
        None
    }
}

struct SeqUnif {
    exprs: Vec<Expr>,
    consume_next: usize,
}
impl Iterator for SeqUnif {
    type Item = MatchResult;
    fn next(&mut self) -> Option<MatchResult> {
        if self.consume_next > self.exprs.len() {
            None
        } else {
            let m = MatchInfo::value(
                f_args![Sequence, &self.exprs[..self.consume_next]],
                self.consume_next,
            );
            self.consume_next += 1;
            Some(m)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_literals() {
        let env = Env::new();

        let u = unify(&env, s!(x), &[]).collect::<Vec<_>>();
        assert_eq!(u, vec![]);

        let u = unify(&env, s!(x), &[s!(x)]).collect::<Vec<_>>();
        assert_eq!(u, vec![MatchInfo::constant(s!(x), 1)]);

        let u = unify(&env, s!(x), &[s!(x), s!(y)]).collect::<Vec<_>>();
        assert_eq!(u, vec![MatchInfo::constant(s!(x), 1)]);

        let u = unify(&env, s!(x), &[s!(y), s!(x)]).collect::<Vec<_>>();
        assert_eq!(u, vec![]);

        let u = unify(&env, f!(Blank), &[s!(x), s!(y)]).collect::<Vec<_>>();
        assert_eq!(u, vec![MatchInfo::value(s!(x), 1)]);
    }

    #[test]
    fn test_unify_patterns() {
        let env = Env::new();
        let u = unify(&env, f![Pattern, s!(x), f!(Blank)], &[n!(123)]).collect::<Vec<_>>();
        assert_eq!(
            u,
            vec![MatchInfo::value(n!(123), 1).map(|(m, c)| (m.bound_as("x".to_owned()), c))]
        );
    }

    #[test]
    fn test_unify_bns() {
        let env = Env::new();

        let u = unify(&env, f![BlankNullSequence], &[]).collect::<Vec<_>>();
        assert_eq!(u, vec![MatchInfo::succeed(0)]);

        let u = unify(&env, f![BlankNullSequence], &[s!(x)]).collect::<Vec<_>>();
        assert_eq!(
            u,
            vec![
                MatchInfo::succeed(0),
                MatchInfo::value(f![Sequence, s!(x)], 1)
            ]
        );

        let u = unify(&env, f![BlankNullSequence], &[s!(x), s!(y)]).collect::<Vec<_>>();
        assert_eq!(
            u,
            vec![
                MatchInfo::succeed(0),
                MatchInfo::value(f![Sequence, s!(x)], 1),
                MatchInfo::value(f![Sequence, s!(x), s!(y)], 2),
            ]
        );
    }

    #[test]
    fn test_unify_fn() {
        let env = Env::new();

        let u = unify(&env, f![Foo, s!(x)], &[f![Foo, s!(x)]]).collect::<Vec<_>>();
        assert_eq!(
            u,
            vec![Ok((
                MatchInfo {
                    expr: f![Foo, s!(x)],
                    bindings: HashMap::new(),
                    max_nest: 1,
                    num_constants: 2
                },
                1
            ))]
        );
    }
}

use crate::{f, s, types::Expr};

// https://reference.wolfram.com/language/tutorial/OperatorInputForms.html
peg::parser! { pub grammar maxylla_parser() for str {
    rule ws() = (" " / ("(*" (!("*)") [_])* "*)"))+
    rule _() = quiet!{("\n" / ws())*} / expected!("whitespace or newline")
    rule __() = quiet!{ws()*} / expected!("whitespace")
    rule sep() = quiet!{([';'|'\n'] _)+} / expected!("statement separator (newline or semicolon)")
    rule letters() -> &'input str = $(quiet!{['a'..='z'|'A'..='Z'|'`'|'$']+} / expected!("letters"))
    rule blank() -> Expr = us:$("_"*<1,3>) ms:sym()? {
        let mut v = match us.len() {
            1 => vec![s!(Blank)],
            2 => vec![s!(BlankSequence)],
            3 => vec![s!(BlankNullSequence)],
            _ => unreachable!(),
        };
        match ms {
            Some(s) => v.push(s),
            _ => (),
        };
        Expr::from_vec(v)
    }
    rule slot() -> Expr = "#" { f![Slot, n!(1)] }
    rule msg() -> Expr = "::" s:sym() { s }
    rule sym() -> Expr = ls:letters() mmsg:msg()? mb:blank()? dot:"."? {
        let s = Expr::Sym(ls.to_owned());
        if let Some(msg) = mmsg {
            f![MessageName, s, msg]
        } else {
            let p = match mb {
                Some(b) => f![Pattern, s, b],
                None => s,
            };
            if dot.is_some() {
                f![Optional, p]
            } else {
                p
            }
        }
    }
    rule num() -> i64 = n:$(quiet!{['0'..='9']+ ("." ['0'..='9']+)?} / expected!("number")) {
        n.parse::<f32>().expect(&format!("couldnt parse {}", n)).round() as i64
    }
    rule string() -> &'input str = ss:$("\"" (!"\"" [_])* "\"") { &ss[1..(ss.len()-1)] }
    pub rule expr() -> Expr = precedence! {
        x:@ sep() y:(@) { f![CompoundExpression, x, y] }
        x:@ sep() { f![CompoundExpression, x, Expr::null()] }
        --
        x:@ "=" _ y:(@) { f![Set, x, y] }
        x:@ ":=" _ y:(@) { f![SetDelayed, x, y] }
        --
        x:(@) "//" _ y:@ { Expr::from_vec(vec![y, x]) }
        --
        x:(@) "&" !"&" _ { f![Function, x] }
        --
        x:(@) "/." _ y:@ { f![ReplaceAll, x, y] }
        x:(@) "//." _ y:@ { f![ReplaceRepeated, x, y] }
        --
        x:@ "->" _ y:(@) { f![Rule, x, y] }
        x:@ ":>" _ y:(@) { f![RuleDelayed, x, y] }
        --
        x:(@) "/;" _ y:@ { f![Condition, x, y] }
        --
        x:(@) "|" _ y:@ { f![Alternatives, x, y] }
        --
        x:(@) "||" _ y:@ { f![Or, x, y] }
        --
        x:(@) "&&" _ y:@ { f![And, x, y] }
        --
        x:(@) "===" _ y:@ { f![SameQ, x, y] }
        x:(@) "=!=" _ y:@ { f![UnsameQ, x, y] }
        --
        x:(@) "==" _ y:@ { f![Equal, x, y] }
        x:(@) "!=" _ y:@ { f![Unequal, x, y] }
        x:(@) ">" _ y:@ { f![Greater, x, y] }
        x:(@) ">=" _ y:@ { f![GreaterEqual, x, y] }
        x:(@) "<" _ y:@ { f![Less, x, y] }
        x:(@) "<=" _ y:@ { f![LessEqual, x, y] }
        --
        x:(@) "+" _ y:@ { f![Plus, x, y] }
        x:(@) "-" _ y:@ { f![Plus, x, f![Times, Expr::Num(-1), y]] }
        --
        x:(@) "*" _ y:@ { f![Times, x, y] }
        x:(@) "/" _ y:@ {
            if x == n!(1) {
                f![Power, y, n!(-1)]
            } else {
                f![Times, x, f![Power, y, n!(-1)]]
            }
        }
        x:(@) __ y:@ { f![Times, x, y] }
        --
        "-" x:(@) {
            match x {
                Expr::Num(n) => n!(-n),
                _ => f![Times, x, n!(-1)],
            }
        }
        --
        x:@ "^" _ y:(@) { f![Power, x, y] }
        --
        x:@ "@" _ y:(@) { Expr::from_vec(vec![x, y]) }
        --
        x:@ "/@" _ y:(@) { f![Map, x, y] }
        x:@ "@@" _ y:(@) { f![Apply, x, y] }
        --
        x:(@) "[" _ y:(expr() ** ("," _)) "]" __ {
            let mut v = vec![x];
            v.append(&mut y.clone());
            Expr::from_vec(v)
        }
        x:(@) "[[" _ y:expr() _ "]]" __ {
            f![Part, x, y]
        }
        --
        b:blank() __ { b }
        s:sym() __ { s }
        n:num() __ { Expr::Num(n) }
        s:slot() __ { s }
        s:string() __ { f![String, Expr::Sym(s.to_owned())] }
        "{" _ xs:(expr() ** ("," _)) "}" __ {
            let mut v = vec![s!(List)];
            v.append(&mut xs.clone());
            Expr::from_vec(v)
        }
        "(" _ x:expr() ")" __ { x }
    }
    pub rule prog() -> Expr = _ sep()? e:expr() { e }
}}

pub fn parse(s: &str) -> std::result::Result<Expr, Box<dyn std::error::Error>> {
    maxylla_parser::prog(s).map_err(|e| e.into())
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! parses {
        (
            $what:ident:
            $( $i:expr => $output:expr; )*
        ) => {
            #[test]
            fn $what() {
                $(
                    assert_eq!(parse($i).unwrap(), $output);
                )*
            }
        };
    }

    parses!(simple_infix:
        "a+b" => f![Plus, s!(a), s!(b)];
        "a + b *c+ d   e " => f![Plus, f![Plus, s!(a), f![Times, s!(b), s!(c)]], f![Times, s!(d), s!(e)]];
    );

    parses!(forms:
        "f[x]" => f![f, s!(x)];
        "f[x, y, z]" => f![f, s!(x), s!(y), s!(z)];
        "f[x, 1, 2]" => f![f, s!(x), Expr::Num(1), Expr::Num(2)];
    );

    parses!(subs:
        "a[b][c]" => Expr::from_vec(vec![f![a, s!(b)], s!(c)]);
        "a[b][c][d]" => Expr::from_vec(vec![Expr::from_vec(vec![f![a, s!(b)], s!(c)]), s!(d)]);
    );

    parses!(lambdas:
        "(x+#)&" => f![Function, f![Plus, s!(x), f![Slot, n!(1)]]];
    );

    parses!(ands:
        "a&&b" => f![And, s!(a), s!(b)];
    );

    parses!(newlines:
        "f[x]; g[y]" => f![CompoundExpression, f![f,s!(x)], f![g,s!(y)]];
        "f[x];\ng[y]" => f![CompoundExpression, f![f,s!(x)], f![g,s!(y)]];
        "f[x]\ng[y]" => f![CompoundExpression, f![f,s!(x)], f![g,s!(y)]];
        "f[x];\n" => f![CompoundExpression, f![f,s!(x)], s!(Null)];
        "f[x];\n\n\n\n" => f![CompoundExpression, f![f,s!(x)], s!(Null)];
        "(* comment *)\n\nf[x];\n\n\n\n" => f![CompoundExpression, f![f,s!(x)], s!(Null)];
    );

    parses!(strings:
        "\"\"" => f![String, Expr::Sym("".to_owned())];
        "\"abc 123\"" => f![String, Expr::Sym("abc 123".to_owned())];
        "foo[\"abc 123\"]" => f![foo, f![String, Expr::Sym("abc 123".to_owned())]];
    );
}

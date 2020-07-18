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
macro_rules! s {
    ( $s:expr ) => {
        Expr::Sym(stringify!($s).to_string())
    };
}
// (

impl Expr {
    pub fn null() -> Expr {
        s!(Null)
    }
}

// https://reference.wolfram.com/language/tutorial/OperatorInputForms.html
peg::parser! { pub grammar maxylla_parser() for str {
    rule _() = [' ' | '\n']*
    rule letters() -> &'input str = $(['a'..='z'|'A'..='Z']+)
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
        Expr::Form(v)
    }
    rule sym() -> Expr = ls:letters() mb:blank()? {
        let s = Expr::Sym(ls.to_owned());
        match mb {
            Some(b) => f![Pattern, s, b],
            None => s,
        }
    }
    rule num() -> i32 = n:$(['0'..='9']+) { n.parse().unwrap() }
    pub rule expr() -> Expr = precedence! {
        x:@ ";" _ y:(@) { f![CompoundExpression, x, y] }
        x:@ ";" _ { f![CompoundExpression, x, Expr::null()] }
        --
        x:@ "=" _ y:(@) { f![Set, x, y] }
        x:@ ":=" _ y:(@) { f![SetDelayed, x, y] }
        --
        x:(@) "//" _ y:@ { Expr::Form(vec![y, x]) }
        --
        x:@ "&" _ { f![Function, x] }
        --
        x:(@) "/." _ y:@ { f![ReplaceAll, x, y] }
        x:(@) "//." _ y:@ { f![ReplaceRepeated, x, y] }
        --
        x:@ "->" _ y:(@) { f![Rule, x, y] }
        x:@ ":>" _ y:(@) { f![RuleDelayed, x, y] }
        --
        x:(@) "/;" _ y:@ { f![Condition, x, y] }
        --
        x:(@) ">" _ y:@ { f![Greater, x, y] }
        x:(@) "<" _ y:@ { f![Less, x, y] }
        --
        x:(@) "+" _ y:@ { f![Plus, x, y] }
        x:(@) "-" _ y:@ { f![Plus, x, f![Times, Expr::Num(-1), y]] }
        --
        x:(@) "*" _ y:@ { f![Times, x, y] }
        x:(@) _ y:@ { f![Times, x, y] }
        --
        x:@ "^" _ y:(@) { f![Power, x, y] }
        --
        x:@ "@" _ y:(@) { Expr::Form(vec![x, y]) }
        --
        x:(@) "[" _ y:(expr() ** ("," _)) "]" _ {
            let mut v = vec![x];
            v.append(&mut y.clone());
            Expr::Form(v)
        }
        --
        b:blank() _ { b }
        s:sym() _ { s }
        n:num() _ { Expr::Num(n) }
        "{" _ xs:(expr() ** ("," _)) "}" _ {
            let mut v = vec![s!(List)];
            v.append(&mut xs.clone());
            Expr::Form(v)
        }
        "(" _ x:expr() ")" _ { x }
    }
}}

pub fn parse(s: &str) -> std::result::Result<Expr, Box<dyn std::error::Error>> {
    maxylla_parser::expr(s).map_err(|e| e.into())
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
}
use glob::glob;
use std::error::Error;
use std::{fmt, fs, result};
use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};

use maxylla::eval::Env;
use maxylla::parse::{parse, Expr};

#[derive(Debug)]
struct SuiteErr {
    msg: String,
}

impl fmt::Display for SuiteErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl Error for SuiteErr {
    fn description(&self) -> &str {
        &self.msg
    }
}

fn run_line(env: &mut Env, last: &mut Expr, line: &str) -> result::Result<bool, Box<dyn Error>> {
    if line == "" {
        *env = Env::new();
        *last = Expr::null();
        Ok(false)
    } else if line.starts_with("= ") {
        let expected = parse(&line[2..])?;
        if expected == *last {
            Ok(true)
        } else {
            Err(Box::new(SuiteErr {
                msg: format!("expected {:?}, but got {:?}", expected, last),
            }))
        }
    } else {
        let parsed = parse(line)?;
        *last = env.eval(&parsed)?;
        Ok(false)
    }
}

#[test]
fn suite() {
    let mut failures = 0;
    for entry in glob("./tests/suite/*.txt").unwrap() {
        let path = entry.unwrap();
        let contents = fs::read_to_string(&path).unwrap();

        let mut stdout = StandardStream::stdout(ColorChoice::Always);
        let mut env = Env::new();
        let mut last = Expr::null();
        for (i, line) in contents.lines().enumerate() {
            print!("{}:{}: ", path.display(), i + 1);
            match run_line(&mut env, &mut last, line) {
                Ok(true) => {
                    stdout
                        .set_color(ColorSpec::new().set_fg(Some(Color::Green)))
                        .unwrap();
                    println!("OK");
                    stdout.reset().unwrap();
                }
                Ok(false) => (),
                Err(e) => {
                    stdout
                        .set_color(ColorSpec::new().set_fg(Some(Color::Red)))
                        .unwrap();
                    println!("{}", e);
                    stdout.reset().unwrap();
                    failures += 1;
                }
            }
        }
    }
    assert_eq!(failures, 0);
}

use clap::{App, Arg};
use maxylla::{parse::parse, types::*};
use rustyline::{error::ReadlineError, Editor};

fn main() {
    println!("hello maxylla");
    let args = App::new("maxylla")
        .arg(Arg::with_name("command").short("c").takes_value(true))
        .get_matches();

    let mut env = Env::new();

    if let Some(c) = args.value_of("command") {
        match parse(c) {
            Ok(parsed) => match env.eval(&parsed) {
                Ok(res) => println!("{}", res),
                Err(err) => println!("eval err: {}", err),
            },
            Err(err) => {
                println!("parse err: {}", err);
            }
        }
        return;
    }

    let mut rl = Editor::<()>::new();
    if rl.load_history("history.txt").is_err() {
        println!("no previous history");
    }
    loop {
        let readline = rl.readline(">> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                println!("line: {}", line);
                match parse(&line) {
                    Ok(parsed) => match env.eval(&parsed) {
                        Ok(res) => {
                            println!("{}", res);
                        }
                        Err(err) => {
                            println!("evaluation error: {}", err);
                        }
                    },
                    Err(err) => {
                        println!("parse error: {}", err);
                    }
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("interrupted");
            }
            Err(ReadlineError::Eof) => {
                println!("eof, exiting");
                break;
            }
            Err(err) => {
                println!("error: {:?}", err);
                break;
            }
        }
    }
    rl.save_history("history.txt").unwrap();
}

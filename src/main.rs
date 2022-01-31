extern crate logroll;

use std::collections::BTreeMap;
use std::io::Read;

use log::{error, info};

use logroll::checker::Checker;
use logroll::syntax::*;

fn main() {
    let config = clap::App::new(env!("CARGO_PKG_NAME"))
        .version(env!("CARGO_PKG_VERSION"))
        .author(env!("CARGO_PKG_AUTHORS"))
        .arg(
            clap::Arg::new("INPUT")
                .help("Sets the input file (defaults to '-', meaning STDIN)")
                .default_value("-")
                .index(1),
        )
        .arg(
            clap::Arg::new("VERBOSE")
                .short('v')
                .multiple_occurrences(true)
                .help("Sets the level of verbosity (more occurrences for more output)"),
        )
        .get_matches();

    let verbosity = match config.occurrences_of("VERBOSE") {
        0 => log::LevelFilter::Warn,
        1 => log::LevelFilter::Info,
        2 => log::LevelFilter::Debug,
        _ => log::LevelFilter::Trace,
    };
    env_logger::Builder::from_default_env()
        .filter(None, verbosity)
        .init();

    let input_source = config.value_of("INPUT").expect("input source");
    let mut input = String::new();
    let res = if input_source == "-" {
        std::io::stdin().read_to_string(&mut input)
    } else {
        std::fs::File::open(input_source).and_then(|mut f| f.read_to_string(&mut input))
    };

    if let Err(err) = res {
        error!("I/O error: {}", err);
        std::process::exit(4);
    }

    let p = Program::parse(&input).unwrap_or_else(|e| {
        error!("Parse error:\n{}", e);
        std::process::exit(2);
    });

    info!("% parsed\n{}", p);

    let checker = Checker::new(&p);

    let checker = match checker {
        Err(errs) => {
            for err in errs {
                error!("Error: {}", err);
            }
            std::process::exit(3);
        }
        Ok(checker) => checker,
    };

    println!("{}", checker.show_refs());

    if !p.is_ground() {
        println!("program isn't grounded");
        std::process::exit(4);
    }

    let graph = checker
        .backrefs
        .iter()
        .enumerate()
        .map(|(h, ls)| (h, ls.clone()))
        .collect::<BTreeMap<_, _>>();

    let circuits = logroll::circuits::find(&graph);

    info!("found {} circuits", circuits.len());
    for c in circuits {
        println!(
            "{}",
            c.into_iter()
                .map(|i| checker.atoms[i].to_string())
                .collect::<Vec<_>>()
                .join(" -> ")
        );
    }
}

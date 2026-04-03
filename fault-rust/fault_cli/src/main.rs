//! CLI for the Fault bounded model-checking compiler (Rust implementation).
//!
//! Usage:
//!   fault-rust -f input.fspec               # check model (requires Z3)
//!   fault-rust -m smt -f input.fspec        # emit SMT-LIB2
//!   fault-rust -m parse -f input.fspec      # parse and dump AST (debug)
//!   fault-rust -m check --raw -f input.fspec  # raw Z3 model output

use std::fs;
use std::process;

use fault_cli::{Mode, RunOptions};

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let mut file_path: Option<&str> = None;
    let mut mode_str = "check";
    let mut opts = RunOptions::default();

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-f" => {
                i += 1;
                file_path = args.get(i).map(|s| s.as_str());
            }
            "-m" => {
                i += 1;
                mode_str = match args.get(i) {
                    Some(m) => m.as_str(),
                    None => {
                        eprintln!("error: -m requires a mode (smt, parse, check)");
                        process::exit(1);
                    }
                };
            }
            "--raw" => {
                opts.raw = true;
            }
            "-h" | "--help" => {
                print_usage();
                return;
            }
            other => {
                eprintln!("error: unknown argument: {}", other);
                print_usage();
                process::exit(1);
            }
        }
        i += 1;
    }

    let path = match file_path {
        Some(p) => p,
        None => {
            eprintln!("error: no input file specified (-f <file>)");
            print_usage();
            process::exit(1);
        }
    };

    let mode = match mode_str {
        "smt" => Mode::Smt,
        "parse" => Mode::Parse,
        "check" => Mode::Check,
        other => {
            eprintln!("error: unknown mode '{}' (use smt, parse, or check)", other);
            process::exit(1);
        }
    };

    let src = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", path, e);
            process::exit(1);
        }
    };

    let output = fault_cli::run_with_options(mode, &src, path, &opts);
    print!("{}", output.stdout);
    eprint!("{}", output.stderr);
    process::exit(output.exit_code);
}

fn print_usage() {
    eprintln!("Usage: fault-rust [-m <mode>] [--raw] -f <input.fspec>");
    eprintln!("Modes:");
    eprintln!("  smt    Emit SMT-LIB2 encoding");
    eprintln!("  parse  Parse and dump AST (debug)");
    eprintln!("  check  Check model with Z3 solver (default)");
    eprintln!("Options:");
    eprintln!("  --raw  Print raw Z3 model output (check mode only)");
}

//! CLI for the Fault bounded model-checking compiler (Rust implementation).
//!
//! Usage:
//!   fault-rust -f input.fspec           # check model (requires Z3)
//!   fault-rust -m smt -f input.fspec    # emit SMT-LIB2
//!   fault-rust -m parse -f input.fspec  # parse and dump AST (debug)

use std::fs;
use std::path::Path;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let mut file_path: Option<&str> = None;
    let mut mode = "check";

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-f" => {
                i += 1;
                file_path = args.get(i).map(|s| s.as_str());
            }
            "-m" => {
                i += 1;
                mode = match args.get(i) {
                    Some(m) => m.as_str(),
                    None => {
                        eprintln!("error: -m requires a mode (smt, parse, check)");
                        process::exit(1);
                    }
                };
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

    let src = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", path, e);
            process::exit(1);
        }
    };

    // Extract spec name from file (fallback), will be overridden by parsed spec name
    let file_spec_name = Path::new(path)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("spec")
        .to_string();
    let spec_name = file_spec_name.as_str();

    let base_dir = Path::new(path)
        .parent()
        .unwrap_or(Path::new("."))
        .to_path_buf();

    match mode {
        "smt" => run_smt_mode(&src, spec_name, &base_dir),
        "parse" => run_parse_mode(&src),
        "check" => run_check_mode(&src, spec_name, &base_dir),
        other => {
            eprintln!("error: unknown mode '{}' (use smt, parse, or check)", other);
            process::exit(1);
        }
    }
}

fn print_usage() {
    eprintln!("Usage: fault-rust [-m <mode>] -f <input.fspec>");
    eprintln!("Modes:");
    eprintln!("  smt    Emit SMT-LIB2 encoding");
    eprintln!("  parse  Parse and dump AST (debug)");
    eprintln!("  check  Check model with Z3 solver (default)");
}

fn parse_and_validate(src: &str, base_dir: &Path) -> fault_syntax::Spec {
    let mut spec = match fault_syntax::parser::parse_spec(src) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("parse error: {}", e);
            process::exit(1);
        }
    };

    if !spec.import_decls.is_empty() {
        fault_resolve::loader::load_imports(&mut spec, base_dir);
    }

    let errors = fault_resolve::validate::validate_spec(&spec);
    if !errors.is_empty() {
        for e in &errors {
            eprintln!("{}", e);
        }
        process::exit(1);
    }

    spec
}

fn run_smt_mode(src: &str, _spec_name: &str, base_dir: &Path) {
    let spec = parse_and_validate(src, base_dir);
    let name = spec.name.clone();
    let resolved = fault_resolve::resolve_spec(spec);
    let smt = fault_smt::encode_program(&resolved, &name);
    print!("{}", smt);
}

fn run_parse_mode(src: &str) {
    let spec = match fault_syntax::parser::parse_spec(src) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("parse error: {}", e);
            process::exit(1);
        }
    };

    println!("{:#?}", spec);
}

fn run_check_mode(src: &str, _spec_name: &str, base_dir: &Path) {
    let spec = parse_and_validate(src, base_dir);
    let name = spec.name.clone();
    let resolved = fault_resolve::resolve_spec(spec);
    let smt = fault_smt::encode_program(&resolved, &name);

    // Try to shell out to Z3
    let z3_cmd = std::env::var("SOLVERCMD").unwrap_or_else(|_| "z3".into());
    let z3_arg = std::env::var("SOLVERARG").unwrap_or_else(|_| "-in".into());

    let smt_with_check = format!("{}\n(check-sat)\n(get-model)\n", smt);

    match std::process::Command::new(&z3_cmd)
        .arg(&z3_arg)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
    {
        Ok(mut child) => {
            use std::io::Write;
            if let Some(ref mut stdin) = child.stdin {
                let _ = stdin.write_all(smt_with_check.as_bytes());
            }

            match child.wait_with_output() {
                Ok(output) => {
                    let stdout = String::from_utf8_lossy(&output.stdout);
                    let lines: Vec<&str> = stdout.lines().collect();

                    if let Some(result_line) = lines.first() {
                        match *result_line {
                            "sat" => {
                                println!("COUNTEREXAMPLE FOUND (assertion violated)");
                                for line in &lines[1..] {
                                    println!("{}", line);
                                }
                            }
                            "unsat" => {
                                println!("CORRECT (no counterexample found)");
                            }
                            "unknown" => {
                                println!("UNKNOWN (solver could not determine)");
                            }
                            other => {
                                eprintln!("unexpected solver output: {}", other);
                                process::exit(1);
                            }
                        }
                    }
                }
                Err(e) => {
                    eprintln!("error waiting for solver: {}", e);
                    process::exit(1);
                }
            }
        }
        Err(_) => {
            eprintln!(
                "warning: solver '{}' not found; printing SMT encoding instead",
                z3_cmd
            );
            eprintln!("(install Z3 or set SOLVERCMD environment variable)");
            print!("{}", smt);
        }
    }
}

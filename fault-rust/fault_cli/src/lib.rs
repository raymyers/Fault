//! Library interface for the Fault compiler pipeline.
//!
//! Extracts the core logic from `main` so it can be unit-tested
//! without `process::exit`.

pub mod z3_parse;

use std::path::Path;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Smt,
    Parse,
    Check,
}

#[derive(Debug, Clone, Default)]
pub struct RunOptions {
    /// When true, print raw Z3 model output instead of friendly format.
    pub raw: bool,
}

#[derive(Debug)]
pub struct Output {
    pub stdout: String,
    pub stderr: String,
    pub exit_code: i32,
}

enum ParsedInput {
    Spec(fault_syntax::Spec),
    System(fault_syntax::System),
}

fn parse_and_validate(src: &str, base_dir: &Path, file_path: &str) -> Result<ParsedInput, String> {
    let is_system = file_path.ends_with(".fsystem");

    if is_system {
        let mut sys = fault_syntax::parser::parse_system(src)
            .map_err(|e| format!("parse error: {}", e))?;
        fault_resolve::loader::load_system_imports(&mut sys, base_dir);
        Ok(ParsedInput::System(sys))
    } else {
        let mut spec = fault_syntax::parser::parse_spec(src)
            .map_err(|e| format!("parse error: {}", e))?;

        if !spec.import_decls.is_empty() {
            fault_resolve::loader::load_imports(&mut spec, base_dir);
        }

        let errors = fault_resolve::validate::validate_spec(&spec);
        if !errors.is_empty() {
            let msg = errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>().join("\n");
            return Err(msg);
        }

        Ok(ParsedInput::Spec(spec))
    }
}

fn resolve_input(input: ParsedInput) -> (fault_resolve::ResolvedProgram, String) {
    match input {
        ParsedInput::Spec(spec) => {
            let name = spec.name.clone();
            let resolved = fault_resolve::resolve_spec(spec);
            (resolved, name)
        }
        ParsedInput::System(sys) => {
            let name = sys.name.clone();
            let resolved = fault_resolve::resolve_system(sys);
            (resolved, name)
        }
    }
}

/// Run the compiler pipeline with the given mode and source file content.
///
/// For `Mode::Check`, the caller can pass `src` and `file_path` but Z3
/// invocation is handled inline; when Z3 is unavailable, SMT is printed.
pub fn run(mode: Mode, src: &str, file_path: &str) -> Output {
    run_with_options(mode, src, file_path, &RunOptions::default())
}

/// Like [`run`] but accepts additional options (e.g. `--raw`).
pub fn run_with_options(mode: Mode, src: &str, file_path: &str, opts: &RunOptions) -> Output {
    let base_dir = Path::new(file_path)
        .parent()
        .unwrap_or(Path::new("."))
        .to_path_buf();

    match mode {
        Mode::Smt => run_smt(src, &base_dir, file_path),
        Mode::Parse => run_parse(src, file_path),
        Mode::Check => run_check(src, &base_dir, file_path, opts),
    }
}

fn run_smt(src: &str, base_dir: &Path, file_path: &str) -> Output {
    let input = match parse_and_validate(src, base_dir, file_path) {
        Ok(i) => i,
        Err(e) => return Output { stdout: String::new(), stderr: e, exit_code: 1 },
    };
    let (resolved, name) = resolve_input(input);
    let smt = fault_smt::encode_program(&resolved, &name);
    Output { stdout: smt, stderr: String::new(), exit_code: 0 }
}

fn run_parse(src: &str, file_path: &str) -> Output {
    if file_path.ends_with(".fsystem") {
        match fault_syntax::parser::parse_system(src) {
            Ok(s) => Output { stdout: format!("{:#?}\n", s), stderr: String::new(), exit_code: 0 },
            Err(e) => Output { stdout: String::new(), stderr: format!("parse error: {}", e), exit_code: 1 },
        }
    } else {
        match fault_syntax::parser::parse_spec(src) {
            Ok(s) => Output { stdout: format!("{:#?}\n", s), stderr: String::new(), exit_code: 0 },
            Err(e) => Output { stdout: String::new(), stderr: format!("parse error: {}", e), exit_code: 1 },
        }
    }
}

fn run_check(src: &str, base_dir: &Path, file_path: &str, opts: &RunOptions) -> Output {
    let input = match parse_and_validate(src, base_dir, file_path) {
        Ok(i) => i,
        Err(e) => return Output { stdout: String::new(), stderr: e, exit_code: 1 },
    };
    let (resolved, name) = resolve_input(input);

    let has_assertions = resolved.invariants.iter().any(|inv| {
        matches!(
            inv,
            fault_syntax::Invariant::Assert { .. }
                | fault_syntax::Invariant::AssertWhen { .. }
        )
    });

    let smt = fault_smt::encode_program(&resolved, &name);

    if !has_assertions {
        return Output {
            stdout: "Fault could not find a failure case.\n(no assertions to check)\n".into(),
            stderr: String::new(),
            exit_code: 0,
        };
    }

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
                    let raw = String::from_utf8_lossy(&output.stdout);
                    let lines: Vec<&str> = raw.lines().collect();

                    if let Some(result_line) = lines.first() {
                        match *result_line {
                            "sat" => {
                                let model_text: String =
                                    lines[1..].iter().flat_map(|l| [*l, "\n"]).collect();

                                let stdout = if opts.raw {
                                    format!("COUNTEREXAMPLE FOUND (assertion violated)\n{}", model_text)
                                } else {
                                    let model = z3_parse::parse_model(&model_text);
                                    z3_parse::format_counterexample(&model, &name)
                                };
                                Output { stdout, stderr: String::new(), exit_code: 0 }
                            }
                            "unsat" => Output {
                                stdout: "Fault could not find a failure case. All good!\n".into(),
                                stderr: String::new(),
                                exit_code: 0,
                            },
                            "unknown" => Output {
                                stdout: "UNKNOWN (solver could not determine)\n".into(),
                                stderr: String::new(),
                                exit_code: 0,
                            },
                            other => Output {
                                stdout: String::new(),
                                stderr: format!("unexpected solver output: {}", other),
                                exit_code: 1,
                            },
                        }
                    } else {
                        Output { stdout: String::new(), stderr: "empty solver output".into(), exit_code: 1 }
                    }
                }
                Err(e) => Output {
                    stdout: String::new(),
                    stderr: format!("error waiting for solver: {}", e),
                    exit_code: 1,
                },
            }
        }
        Err(_) => {
            let stderr = format!(
                "warning: solver '{}' not found; printing SMT encoding instead\n\
                 (install Z3 or set SOLVERCMD environment variable)\n",
                z3_cmd
            );
            Output { stdout: smt, stderr, exit_code: 0 }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn testdata_dir() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .join("testdata")
    }

    fn read_fixture(name: &str) -> (String, String) {
        let path = testdata_dir().join(name);
        let src = std::fs::read_to_string(&path)
            .unwrap_or_else(|_| panic!("missing fixture: {}", name));
        (src, path.to_string_lossy().into_owned())
    }

    #[test]
    fn smt_mode_simple_spec() {
        let (src, path) = read_fixture("simple.fspec");
        let out = run(Mode::Smt, &src, &path);
        assert_eq!(out.exit_code, 0, "stderr: {}", out.stderr);
        assert!(out.stdout.contains("(set-logic"), "expected SMT output, got: {}", &out.stdout[..80.min(out.stdout.len())]);
    }

    #[test]
    fn parse_mode_simple_spec() {
        let (src, path) = read_fixture("simple.fspec");
        let out = run(Mode::Parse, &src, &path);
        assert_eq!(out.exit_code, 0, "stderr: {}", out.stderr);
        assert!(out.stdout.contains("Spec"), "expected AST dump");
    }

    #[test]
    fn check_mode_no_assertions() {
        let (src, path) = read_fixture("simple.fspec");
        let out = run(Mode::Check, &src, &path);
        assert_eq!(out.exit_code, 0, "stderr: {}", out.stderr);
        assert!(
            out.stdout.contains("no assertions to check") || out.stdout.contains("(set-logic"),
            "expected no-assertions message or SMT fallback, got: {}",
            out.stdout
        );
    }

    #[test]
    fn smt_mode_parse_error() {
        let out = run(Mode::Smt, "this is not valid fault", "invalid.fspec");
        assert_eq!(out.exit_code, 1);
        assert!(out.stderr.contains("parse error"), "expected parse error, got: {}", out.stderr);
    }

    #[test]
    fn smt_mode_with_imports() {
        let (src, path) = read_fixture("imports/single_import.fspec");
        let out = run(Mode::Smt, &src, &path);
        assert_eq!(out.exit_code, 0, "stderr: {}", out.stderr);
        assert!(out.stdout.contains("(set-logic"));
    }

    #[test]
    fn check_mode_with_assertions() {
        let (src, path) = read_fixture("asserts/input.fspec");
        let out = run(Mode::Check, &src, &path);
        // Depending on Z3 availability: either check result or SMT fallback
        assert_eq!(out.exit_code, 0, "stderr: {}", out.stderr);
    }

    #[test]
    fn smt_mode_booleans() {
        let (src, path) = read_fixture("booleans/input.fspec");
        let out = run(Mode::Smt, &src, &path);
        assert_eq!(out.exit_code, 0, "stderr: {}", out.stderr);
        assert!(out.stdout.contains("Bool"));
    }
}

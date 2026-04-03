//! Data-driven test: parse every fixture in testdata/ without errors.

use fault_syntax::parser;
use std::fs;
use std::path::Path;

fn parse_fixture(dir: &Path, name: &str) {
    let fspec = dir.join("input.fspec");
    let fsystem = dir.join("input.fsystem");

    if fspec.exists() {
        let src = fs::read_to_string(&fspec)
            .unwrap_or_else(|e| panic!("cannot read {}: {}", fspec.display(), e));
        parser::parse_spec(&src)
            .unwrap_or_else(|e| panic!("parse error in {}/input.fspec: {}", name, e));
    } else if fsystem.exists() {
        let src = fs::read_to_string(&fsystem)
            .unwrap_or_else(|e| panic!("cannot read {}: {}", fsystem.display(), e));
        parser::parse_system(&src)
            .unwrap_or_else(|e| panic!("parse error in {}/input.fsystem: {}", name, e));
    }
}

fn parse_raw_file(path: &Path) {
    let src = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read {}: {}", path.display(), e));
    let name = path.file_name().unwrap().to_string_lossy();

    if name.ends_with(".fspec") {
        parser::parse_spec(&src)
            .unwrap_or_else(|e| panic!("parse error in {}: {}", path.display(), e));
    } else if name.ends_with(".fsystem") {
        parser::parse_system(&src)
            .unwrap_or_else(|e| panic!("parse error in {}: {}", path.display(), e));
    }
}

#[test]
fn parse_all_standard_fixtures() {
    let testdata = Path::new(env!("CARGO_MANIFEST_DIR")).join("../testdata");

    for entry in fs::read_dir(&testdata).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.is_dir() {
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            if matches!(
                name.as_str(),
                "statecharts" | "imports" | "swaps" | "badspecs" | "conditionals"
            ) {
                continue;
            }
            parse_fixture(&path, &name);
        }
    }
}

#[test]
fn parse_conditional_fixtures() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../testdata/conditionals");
    if !dir.exists() {
        return;
    }
    for entry in fs::read_dir(&dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().map(|e| e == "fspec").unwrap_or(false) {
            parse_raw_file(&path);
        }
    }
}

#[test]
fn parse_swap_fixtures() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../testdata/swaps");
    if !dir.exists() {
        return;
    }
    for entry in fs::read_dir(&dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().map(|e| e == "fspec").unwrap_or(false) {
            parse_raw_file(&path);
        }
    }
}

#[test]
fn parse_statechart_fixtures() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../testdata/statecharts");
    if !dir.exists() {
        return;
    }
    for entry in fs::read_dir(&dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().map(|e| e == "fsystem").unwrap_or(false) {
            parse_raw_file(&path);
        }
    }
}

#[test]
fn parse_import_fixtures() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../testdata/imports");
    if !dir.exists() {
        return;
    }
    for entry in fs::read_dir(&dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().map(|e| e == "fspec").unwrap_or(false) {
            parse_raw_file(&path);
        }
    }
}

// --- Parser error-path tests (M33b) ---

#[test]
fn parse_error_empty_file() {
    let src = "";
    assert!(parser::parse_spec(src).is_err(), "empty file should fail to parse");
}

#[test]
fn parse_error_missing_semi() {
    let src = "spec bad\ndef s = stock{ v: 10, }";
    assert!(parser::parse_spec(src).is_err(), "missing semicolon should fail");
}

#[test]
fn parse_error_bad_token() {
    let src = "spec bad;\n@@@ not valid;";
    assert!(parser::parse_spec(src).is_err(), "invalid tokens should fail");
}

#[test]
fn parse_error_incomplete_def() {
    let src = "spec bad;\ndef s = ";
    assert!(parser::parse_spec(src).is_err(), "incomplete def should fail");
}

#[test]
fn parse_error_missing_spec_name() {
    let src = "spec;";
    assert!(parser::parse_spec(src).is_err(), "spec without name should fail");
}

#[test]
fn parse_error_fixtures_all_fail() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../testdata/parse_errors");
    if !dir.exists() {
        return;
    }
    for entry in fs::read_dir(&dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().map(|e| e == "fspec").unwrap_or(false) {
            let src = fs::read_to_string(&path).unwrap();
            let name = path.file_name().unwrap().to_string_lossy();
            assert!(
                parser::parse_spec(&src).is_err(),
                "{} should fail to parse",
                name
            );
        }
    }
}

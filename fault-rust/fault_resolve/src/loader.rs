//! Import loader — reads imported `.fspec` files from disk and attaches
//! them to the importing `Spec` or `System`. Handles circular imports
//! by tracking already-visited paths.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use fault_syntax::{Spec, System};
use fault_syntax::parser::parse_spec;

/// Load all imports for `spec`, resolving paths relative to `base_dir`.
/// Circular imports are broken: an already-visited path yields a stub Spec
/// with only the constants collected so far (no re-parse).
pub fn load_imports(spec: &mut Spec, base_dir: &Path) {
    let mut visited = HashSet::new();
    load_imports_inner(spec, base_dir, &mut visited);
}

fn load_imports_inner(spec: &mut Spec, base_dir: &Path, visited: &mut HashSet<PathBuf>) {
    let decls: Vec<_> = spec.import_decls.clone();
    for decl in &decls {
        let import_path = base_dir.join(&decl.path);
        let canonical = import_path
            .canonicalize()
            .unwrap_or_else(|_| import_path.clone());

        if !visited.insert(canonical.clone()) {
            // Circular import — skip recursive loading but still need a stub
            // so that cross-spec constant references work.
            if let Ok(src) = std::fs::read_to_string(&canonical)
                && let Ok(mut imported) = parse_spec(&src)
            {
                imported.flows.clear();
                imported.stocks.clear();
                imported.run_block = None;
                spec.imported_specs.push(imported);
            }
            continue;
        }

        let src = match std::fs::read_to_string(&canonical) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("warning: cannot read import {:?}: {}", decl.path, e);
                continue;
            }
        };

        let mut imported = match parse_spec(&src) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("warning: cannot parse import {:?}: {:?}", decl.path, e);
                continue;
            }
        };

        // Recursively load sub-imports
        let import_dir = canonical.parent().unwrap_or(base_dir);
        load_imports_inner(&mut imported, import_dir, visited);

        spec.imported_specs.push(imported);
    }
}

/// Load all imports for a `System`, resolving paths relative to `base_dir`.
/// Replaces the stub Specs created by the parser with fully loaded ones.
pub fn load_system_imports(sys: &mut System, base_dir: &Path) {
    let mut loaded = Vec::new();
    for decl in &sys.import_decls {
        let import_path = base_dir.join(&decl.path);
        let canonical = import_path
            .canonicalize()
            .unwrap_or_else(|_| import_path.clone());

        let src = match std::fs::read_to_string(&canonical) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("warning: cannot read import {:?}: {}", decl.path, e);
                continue;
            }
        };

        let mut imported = match parse_spec(&src) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("warning: cannot parse import {:?}: {:?}", decl.path, e);
                continue;
            }
        };

        // Recursively load sub-imports
        let import_dir = canonical.parent().unwrap_or(base_dir).to_path_buf();
        let mut visited = HashSet::new();
        visited.insert(canonical);
        load_imports_inner(&mut imported, &import_dir, &mut visited);

        loaded.push(imported);
    }
    sys.imports = loaded;
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn write_temp_spec(dir: &Path, name: &str, content: &str) -> PathBuf {
        let path = dir.join(name);
        fs::write(&path, content).unwrap();
        path
    }

    #[test]
    fn load_imports_missing_file_continues() {
        let dir = tempfile::tempdir().unwrap();
        let mut spec = parse_spec("spec main;").unwrap();
        spec.import_decls.push(fault_syntax::ImportDecl {
            path: "nonexistent.fspec".into(),
            alias: "nonexistent".into(),
        });
        // Should not panic; missing import is a warning
        load_imports(&mut spec, dir.path());
        assert!(spec.imported_specs.is_empty());
    }

    #[test]
    fn load_imports_parse_error_continues() {
        let dir = tempfile::tempdir().unwrap();
        write_temp_spec(dir.path(), "bad.fspec", "this is not valid fault");
        let mut spec = parse_spec("spec main;").unwrap();
        spec.import_decls.push(fault_syntax::ImportDecl {
            path: "bad.fspec".into(),
            alias: "bad".into(),
        });
        load_imports(&mut spec, dir.path());
        assert!(spec.imported_specs.is_empty());
    }

    #[test]
    fn load_imports_valid_file_succeeds() {
        let dir = tempfile::tempdir().unwrap();
        write_temp_spec(
            dir.path(),
            "other.fspec",
            "spec other;\nconst x = 5;",
        );
        let mut spec = parse_spec("spec main;").unwrap();
        spec.import_decls.push(fault_syntax::ImportDecl {
            path: "other.fspec".into(),
            alias: "other".into(),
        });
        load_imports(&mut spec, dir.path());
        assert_eq!(spec.imported_specs.len(), 1);
        assert_eq!(spec.imported_specs[0].name, "other");
    }

    #[test]
    fn load_imports_circular_import_breaks_cycle() {
        let dir = tempfile::tempdir().unwrap();
        // a.fspec imports b.fspec, b.fspec imports a.fspec
        write_temp_spec(
            dir.path(),
            "a.fspec",
            "spec a;\nimport \"b.fspec\";\nconst x = 1;",
        );
        write_temp_spec(
            dir.path(),
            "b.fspec",
            "spec b;\nimport \"a.fspec\";\nconst y = 2;",
        );
        let src = fs::read_to_string(dir.path().join("a.fspec")).unwrap();
        let mut spec = parse_spec(&src).unwrap();
        load_imports(&mut spec, dir.path());
        // Should have imported b, but b's recursive import of a is a stub
        assert_eq!(spec.imported_specs.len(), 1);
        assert_eq!(spec.imported_specs[0].name, "b");
    }

    #[test]
    fn load_system_imports_missing_file_continues() {
        let dir = tempfile::tempdir().unwrap();
        let mut sys = fault_syntax::System {
            name: "test_sys".into(),
            import_decls: vec![fault_syntax::ImportDecl {
                path: "missing.fspec".into(),
                alias: "missing".into(),
            }],
            imports: vec![],
            globals: vec![],
            components: vec![],
            invariants: vec![],
            start_states: vec![],
            run_block: None,
        };
        load_system_imports(&mut sys, dir.path());
        assert!(sys.imports.is_empty());
    }
}

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


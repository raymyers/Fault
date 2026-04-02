//! SSA variable versioning for SMT encoding.
//!
//! Each variable gets monotonically increasing version suffixes:
//! `name_0` (initial), `name_1` (after first assignment), etc.

use std::collections::HashMap;

/// Tracks SSA version numbers for each variable.
#[derive(Debug, Clone)]
pub struct Ssa {
    versions: HashMap<String, u32>,
}

impl Ssa {
    pub fn new() -> Self {
        Self {
            versions: HashMap::new(),
        }
    }

    /// Get the current version of a variable, initializing to 0 if unseen.
    pub fn current(&mut self, name: &str) -> u32 {
        *self.versions.entry(name.to_string()).or_insert(0)
    }

    /// Get the versioned name for the current version of a variable.
    pub fn current_name(&mut self, name: &str) -> String {
        let v = self.current(name);
        format!("{}_{}", name, v)
    }

    /// Bump to next version, returning the new versioned name.
    pub fn next_name(&mut self, name: &str) -> String {
        let v = self.versions.entry(name.to_string()).or_insert(0);
        *v += 1;
        format!("{}_{}", name, *v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ssa_versioning() {
        let mut ssa = Ssa::new();
        assert_eq!(ssa.current_name("x"), "x_0");
        assert_eq!(ssa.next_name("x"), "x_1");
        assert_eq!(ssa.current_name("x"), "x_1");
        assert_eq!(ssa.next_name("x"), "x_2");

        // New variable starts at 0
        assert_eq!(ssa.current_name("y"), "y_0");
    }
}

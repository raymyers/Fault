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

    /// Get the current version without mutating (returns 0 if not tracked).
    pub fn current_ro(&self, name: &str) -> u32 {
        self.versions.get(name).copied().unwrap_or(0)
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

    /// Snapshot current version state for later restore.
    pub fn snapshot(&self) -> HashMap<String, u32> {
        self.versions.clone()
    }

    /// Restore version state from a snapshot.
    pub fn restore(&mut self, snap: HashMap<String, u32>) {
        self.versions = snap;
    }

    /// Advance version numbers to be at least as high as those in `other`.
    #[allow(dead_code)]
    pub fn merge_max(&mut self, other: &HashMap<String, u32>) {
        for (k, v) in other {
            let cur = self.versions.entry(k.clone()).or_insert(0);
            if *v > *cur {
                *cur = *v;
            }
        }
    }

    /// Set the version of a specific variable.
    /// Bump version and return the new version number (not the name).
    pub fn bump(&mut self, name: &str) -> u32 {
        let v = self.versions.entry(name.to_string()).or_insert(0);
        *v += 1;
        *v
    }

    pub fn set_version(&mut self, name: &str, ver: u32) {
        self.versions.insert(name.to_string(), ver);
    }

    /// Check whether a variable is already tracked.
    pub fn has(&self, name: &str) -> bool {
        self.versions.contains_key(name)
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

    #[test]
    fn snapshot_restore_roundtrip() {
        let mut ssa = Ssa::new();
        ssa.next_name("x"); // x_0 → x_1
        ssa.next_name("x"); // x_1 → x_2
        assert_eq!(ssa.current("x"), 2);
        let snap = ssa.snapshot();
        ssa.next_name("x"); // x_2 → x_3
        assert_eq!(ssa.current("x"), 3);
        ssa.restore(snap);
        assert_eq!(ssa.current("x"), 2);
    }

    #[test]
    fn merge_max_takes_higher() {
        let mut ssa = Ssa::new();
        ssa.next_name("a"); // a_1
        ssa.next_name("a"); // a_2
        assert_eq!(ssa.current("a"), 2);
        let snap = ssa.snapshot(); // {a: 2}

        let mut ssa2 = Ssa::new();
        ssa2.next_name("a"); // a_1
        assert_eq!(ssa2.current("a"), 1);
        ssa2.merge_max(&snap);
        assert_eq!(ssa2.current("a"), 2);
    }

    #[test]
    fn merge_max_keeps_own_if_higher() {
        let mut ssa = Ssa::new();
        ssa.next_name("a"); // a_1
        let snap = ssa.snapshot(); // {a: 1}

        let mut ssa2 = Ssa::new();
        ssa2.next_name("a");
        ssa2.next_name("a");
        ssa2.next_name("a"); // a_3
        assert_eq!(ssa2.current("a"), 3);
        ssa2.merge_max(&snap);
        assert_eq!(ssa2.current("a"), 3);
    }

    #[test]
    fn current_ro_does_not_bump() {
        let ssa = Ssa::new();
        let v = ssa.current_ro("x");
        assert_eq!(v, 0);
        assert!(!ssa.has("x"));
    }

    #[test]
    fn has_after_bump() {
        let mut ssa = Ssa::new();
        assert!(!ssa.has("x"));
        ssa.next_name("x");
        assert!(ssa.has("x"));
    }

    #[test]
    fn set_version_overrides() {
        let mut ssa = Ssa::new();
        ssa.set_version("y", 5);
        assert_eq!(ssa.current("y"), 5);
    }

    #[test]
    fn bump_returns_incremented_version() {
        let mut ssa = Ssa::new();
        assert_eq!(ssa.bump("z"), 1);
        assert_eq!(ssa.bump("z"), 2);
        assert_eq!(ssa.current("z"), 2);
    }
}

//! Event log for recording the encoding trace.
//!
//! During SMT encoding, events are recorded in order. After Z3 solving,
//! the results map is populated and the log is replayed to produce
//! human-readable output matching the Go implementation's `Logger.Print()`.

use std::collections::BTreeMap;

/// A single event recorded during encoding.
#[derive(Debug, Clone)]
pub enum Event {
    /// Entering the @__run meta-function (start of model).
    RunStart { rounds: u32 },
    /// Entering a named function in a given round.
    FunctionEntry { name: String, round: u32 },
    /// Exiting a named function.
    FunctionExit { name: String },
    /// A variable was assigned (SSA variable name with version suffix).
    VariableUpdate { ssa_name: String },
    /// An unknown/solvable variable was resolved.
    Solvable { ssa_name: String },
}

/// Records events during encoding and holds Z3 results after solving.
#[derive(Debug, Clone, Default)]
pub struct EventLog {
    pub events: Vec<Event>,
    /// Populated after solving: SSA variable name → value string.
    pub results: BTreeMap<String, String>,
    /// Spec name for stripping prefixes.
    pub spec_name: String,
}

impl EventLog {
    pub fn new(spec_name: &str) -> Self {
        Self {
            events: Vec::new(),
            results: BTreeMap::new(),
            spec_name: spec_name.to_string(),
        }
    }

    pub fn log_run_start(&mut self, rounds: u32) {
        self.events.push(Event::RunStart { rounds });
    }

    pub fn log_function_entry(&mut self, name: &str, round: u32) {
        self.events.push(Event::FunctionEntry {
            name: name.to_string(),
            round,
        });
    }

    pub fn log_function_exit(&mut self, name: &str) {
        self.events.push(Event::FunctionExit {
            name: name.to_string(),
        });
    }

    pub fn log_variable_update(&mut self, ssa_name: &str) {
        self.events.push(Event::VariableUpdate {
            ssa_name: ssa_name.to_string(),
        });
    }

    pub fn log_solvable(&mut self, ssa_name: &str) {
        self.events.push(Event::Solvable {
            ssa_name: ssa_name.to_string(),
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn event_log_records_events() {
        let mut log = EventLog::new("test");
        log.log_run_start(5);
        log.log_function_entry("cache_r_store", 1);
        log.log_variable_update("test_r_machine_blocks_1");
        log.log_function_exit("cache_r_store");
        assert_eq!(log.events.len(), 4);
    }
}

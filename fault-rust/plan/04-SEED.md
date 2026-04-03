In cases where a counter example was found, the cli output format needs to look friendly like the Go.

Make fault-rust/plan/04-PLAN.md for this.

* execute the plan
* test/lint
* update the plan
* commit push

---

Redo `fault-rust/plan/04-PLAN.md` with the right task bullets to make it descriptive, matching the Go impl if not char by char than fairly close. Read the display logic and make sure we'll wind up with a test for each case.

## Current Rust (Wrong)

cargo run --release -- -f examples/repl/cache.fspec 

```
COUNTEREXAMPLE FOUND
The following assertion can be violated:

  r_machine_blocks
    step 0: 0.0
    step 1: 0.0 → 1.0
    step 2: 1.0 → 0.0
    step 4: 0.0 → -1.0
    step 5: -1.0 → 0.0
    step 7: 0.0 → 1.0
    step 8: 1.0 → 0.0
    step 10: 0.0 → -1.0
    step 11: -1.0 → 0.0
    step 13: 0.0 → 1.0
    step 14: 1.0 → 0.0
    step 16: 0.0 → -1.0
    step 17: -1.0 → 0.0
    step 19: 0.0 → 1.0
    step 20: 1.0 → 0.0
    step 22: 0.0 → -1.0
    step 23: -1.0 → 0.0
    step 25: 0.0 → 1.0
    step 26: 1.0 → 0.0
    step 28: 0.0 → -1.0
    step 29: -1.0 → 0.0
    step 30: 0.0 → 5.0

  r_machine_table
    step 0: 0.0
    step 1: 0.0 → 1.0
    step 4: 1.0 → -1.0
    step 5: -1.0 → 0.0
    step 8: 0.0 → -1.0
    step 9: -1.0 → 0.0
    step 12: 0.0 → -1.0
    step 13: -1.0 → 0.0
    step 16: 0.0 → -1.0
    step 17: -1.0 → 0.0
    step 20: 0.0 → 5.0
```
## Correct Go
```
go run main.go -f fault-rust/testdata/examples/repl/cache.fspec

Start model, run for 5 rounds
-----------------------------------
   Run function cache_r_store (round 1)
      Run function cache_r_release (round 1)
         Set variable cache_r_machine_blocks to value 0.0
         Set variable cache_r_machine_table to value 1.0
         Run function cache_r_release (round 1)
            Run function cache_r_store (round 1)
               Run function cache_r_store (round 2)
                  Run function cache_r_release (round 2)
                     Variable cache_r_machine_blocks is still 0.0
                     cache_r_machine_table: 1.0 → 0.0
                     Run function cache_r_release (round 2)
                        Run function cache_r_store (round 2)
                           Run function cache_r_store (round 3)
                              Run function cache_r_release (round 3)
                                 Variable cache_r_machine_table is still 0.0
                                 Variable cache_r_machine_blocks is still 0.0
                                 Run function cache_r_release (round 3)
                                    Run function cache_r_store (round 3)
                                       Run function cache_r_store (round 4)
                                          Run function cache_r_release (round 4)
                                             Variable cache_r_machine_table is still 0.0
                                             Variable cache_r_machine_blocks is still 0.0
                                             Run function cache_r_release (round 4)
                                                Run function cache_r_store (round 4)
                                                   Run function cache_r_store (round 5)
                                                      Run function cache_r_release (round 5)
                                                         Variable cache_r_machine_blocks is still 0.0
                                                         Variable cache_r_machine_table is still 0.0
                                                         Run function cache_r_release (round 5)
                                                
```
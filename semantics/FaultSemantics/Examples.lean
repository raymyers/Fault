/-
  FaultSemantics.Examples

  Phase 6 (partial): Concrete Fault models encoded as Lean terms,
  verifying that the semantics produces expected behavior.
  These serve as oracle tests against the Go compiler output.
-/
import FaultSemantics.Properties

/-! ## Example 1: Fibonacci

  ```fault
  spec fibonacci;
  def n = stock{ value: 1 };
  def fib = flow{
    num: new n,
    increment: func{ num.value <- num.value[now-1]; },
  };
  for 6 init{ f = new fib; } run { f.increment; }
  ```

  Expected behavior: value goes 1, 2, 3, 5, 8, 13, 21
  (Each round: value += value[now-1], i.e. value_new = value + value_prev)
-/

/-- The fibonacci spec as a Lean Spec -/
def fibonacciSpec : Spec where
  name := "fibonacci"
  constants := []
  stocks := [{ name := "n", props := [("value", .float 1.0)] }]
  flows := [{
    name := "fib"
    stocks := [("num", "n")]
    funcs := [("increment", [
      -- num.value <- num.value[now-1]
      .flowAssign "fib.num.value" .inflow (.history "fib.num.value" (-1))
    ])]
  }]
  invariants := []
  runBlock := some (6, [], [.call "increment"])

/-- Initial state for the fibonacci model -/
def fibInitState : FaultState where
  env := fun x =>
    if x == "fib.num.value" then .real 1.0
    else .nil
  round := 0
  compState := fun _ => ""
  history := fun x n =>
    -- Initial history: value is 1 at round 0
    if x == "fib.num.value" && n == 0 then .real 1.0
    else .nil

/-! ## Example 2: Sandwich (Free Lunch)

  ```fault
  spec sandwich;
  def supplies = stock{ ham: 20 };
  def people = stock{ num: 15 };
  def lunch = flow{
    sandwiches: new supplies,
    toFeed: new people,
    service: func{ sandwiches.ham -> toFeed.num; },
    prep: func{
      if sandwiches.ham < toFeed.num {
        sandwiches.ham <- (toFeed.num - sandwiches.ham);
      }
    },
  };
  assert supplies.ham >= 0;
  for 5 init{ day = new lunch; } run { day.prep; day.service; }
  ```
-/

/-- The sandwich spec -/
def sandwichSpec : Spec where
  name := "sandwich"
  constants := []
  stocks := [
    { name := "supplies", props := [("ham", .float 20.0)] },
    { name := "people", props := [("num", .float 15.0)] }
  ]
  flows := [{
    name := "lunch"
    stocks := [("sandwiches", "supplies"), ("toFeed", "people")]
    funcs := [
      ("service", [
        -- sandwiches.ham -> toFeed.num
        .flowAssign "lunch.sandwiches.ham" .outflow (.var "lunch.toFeed.num")
      ]),
      ("prep", [
        -- if sandwiches.ham < toFeed.num { sandwiches.ham <- (toFeed.num - sandwiches.ham) }
        .ifThenElse
          (.binop .lt (.var "lunch.sandwiches.ham") (.var "lunch.toFeed.num"))
          [.flowAssign "lunch.sandwiches.ham" .inflow
            (.binop .sub (.var "lunch.toFeed.num") (.var "lunch.sandwiches.ham"))]
          []
      ])
    ]
  }]
  invariants := [
    .assert (.binop .ge (.var "lunch.sandwiches.ham") (.lit (.float 0.0))) .always
  ]
  runBlock := some (5, [], [.call "prep", .call "service"])

/-- Initial state for the sandwich model -/
def sandwichInitState : FaultState where
  env := fun x =>
    if x == "lunch.sandwiches.ham" then .real 20.0
    else if x == "lunch.toFeed.num" then .real 15.0
    else .nil
  round := 0
  compState := fun _ => ""
  history := fun _ _ => .nil

/-! ## Example 3: Battery (Drone) — with assertion

  ```fault
  spec battery;
  const frameMass = 600;
  const batteryMass = 1300;
  const batteryEnergy = .15;
  def ft = stock{ numPropellers: 4, propEff: uncertain(4.73, 2.5), time: 0 };
  def life = flow{
    capacity: new ft,
    charge: func{
      x = batteryEnergy * batteryMass;
      y = frameMass + batteryMass;
      capacity.time <- (x / y) * (capacity.propEff * (y/capacity.numPropellers));
    },
  };
  assert ft.time >= 0;
  ```
-/

/-- The battery spec (simplified, without uncertain) -/
def batterySpec : Spec where
  name := "battery"
  constants := [
    { name := "frameMass", value := .float 600.0 },
    { name := "batteryMass", value := .float 1300.0 },
    { name := "batteryEnergy", value := .float 0.15 }
  ]
  stocks := [{
    name := "ft"
    props := [
      ("numPropellers", .float 4.0),
      ("propEff", .uncertain 4.73 2.5),  -- uncertain in full model
      ("time", .float 0.0)
    ]
  }]
  flows := [{
    name := "life"
    stocks := [("capacity", "ft")]
    funcs := [("charge", [
      -- capacity.time <- (batteryEnergy * batteryMass / (frameMass + batteryMass))
      --                   * (capacity.propEff * ((frameMass + batteryMass) / capacity.numPropellers))
      .flowAssign "life.capacity.time" .inflow
        (.binop .mul
          (.binop .div
            (.binop .mul (.var "batteryEnergy") (.var "batteryMass"))
            (.binop .add (.var "frameMass") (.var "batteryMass")))
          (.binop .mul
            (.var "life.capacity.propEff")
            (.binop .div
              (.binop .add (.var "frameMass") (.var "batteryMass"))
              (.var "life.capacity.numPropellers"))))
    ])]
  }]
  invariants := [
    .assert (.binop .ge (.var "life.capacity.time") (.lit (.float 0.0))) .always
  ]
  runBlock := none

/-! ## Semantic Evaluation Tests

  Float arithmetic is opaque in Lean's kernel, so equality proofs
  use `#eval`-based verification rather than `rfl`. We use `#guard`
  to check concrete computations at elaboration time. -/

-- Flow operation tests
#guard applyFlowOp .inflow (.real 20.0) (.real 5.0) == .real 25.0
#guard applyFlowOp .outflow (.real 20.0) (.real 15.0) == .real 5.0
#guard applyFlowOp .assign (.real 20.0) (.real 42.0) == .real 42.0

-- Binary operation tests
#guard evalBinOp .add (.real 3.0) (.real 4.0) == .real 7.0
#guard evalBinOp .lt (.real 5.0) (.real 10.0) == .bool true
#guard evalBinOp .ge (.real 20.0) (.real 0.0) == .bool true

/-! ## Sandwich Model: Manual Trace Verification

  Round 0 initial state: ham = 20, num = 15
  - prep: ham (20) < num (15)? No → skip
  - service: ham -> num means ham -= 15 → ham = 5
  Round 1: ham = 5, num = 15
  - prep: ham (5) < num (15)? Yes → ham += (15-5) = 10 → ham = 15
  - service: ham -> num → ham -= 15 → ham = 0
  Round 2: ham = 0, num = 15
  - prep: ham (0) < num (15)? Yes → ham += 15 → ham = 15
  - service: ham -= 15 → ham = 0
  ...
-/

-- Sandwich trace step checks
#guard evalBinOp .lt (.real 20.0) (.real 15.0) == .bool false   -- prep skip
#guard evalBinOp .lt (.real 5.0) (.real 15.0) == .bool true     -- prep triggers
#guard evalBinOp .sub (.real 15.0) (.real 5.0) == .real 10.0    -- top-up amount
#guard applyFlowOp .inflow (.real 5.0) (.real 10.0) == .real 15.0 -- after prep
#guard applyFlowOp .outflow (.real 15.0) (.real 15.0) == .real 0.0 -- after service
#guard evalBinOp .ge (.real 0.0) (.real 0.0) == .bool true      -- assertion holds

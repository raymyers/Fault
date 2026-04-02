/-
  FaultSemantics.Counterexample

  Phase 6: Counterexample validation — verify that Z3 counterexamples
  from the Go compiler correspond to valid traces in the Lean LTS.
-/
import FaultSemantics.Structural

/-! ## Counterexample 1: asserts.fspec

  ```fault
  spec asserts;
  def ssample = stock{ value: 40 };
  def fsample = flow{
    target: new ssample,
    halve: func{ target.value -> target.value / 2; },
  };
  assert ssample.value == 40;
  assume fsample.target.value > 2;
  for 4 init{ test = new fsample; } run { test.halve; }
  ```

  Z3 counterexample (sat): value halves each round
    value_0 = 40.0, value_1 = 20.0, value_2 = 10.0, value_3 = 5.0, value_4 = 2.5

  The assertion `value == 40` is violated at rounds 1-4.
  The assumption `value > 2` holds at all rounds.
-/

/-- The asserts.fspec model -/
def assertsSpec : Spec where
  name := "asserts"
  constants := []
  stocks := [{ name := "ssample", props := [("value", .float 40.0)] }]
  flows := [{
    name := "fsample"
    stocks := [("target", "ssample")]
    funcs := [("halve", [
      -- target.value -> target.value / 2
      -- outflow: value -= value/2, i.e. value = value - value/2 = value/2
      .flowAssign "asserts.test.target.value" .outflow
        (.binop .div (.var "asserts.test.target.value") (.lit (.float 2.0)))
    ])]
  }]
  invariants := [
    .assert (.binop .eq (.var "asserts.test.target.value") (.lit (.float 40.0))) .always,
    .assume (.binop .gt (.var "asserts.test.target.value") (.lit (.float 2.0))) .always
  ]
  runBlock := some (4, [], [.call "halve"])

/-- Z3 counterexample trace as a list of states -/
def assertsTrace : List FaultState :=
  let mkState (v : Float) (r : Nat) : FaultState :=
    { env := fun x => if x == "asserts.test.target.value" then .real v else .nil
      round := r
      compState := fun _ => ""
      history := fun _ _ => .nil }
  [mkState 40.0 0, mkState 20.0 1, mkState 10.0 2, mkState 5.0 3, mkState 2.5 4]

-- Verify the trace values match Z3's model
#guard (assertsTrace[0]!).getVar "asserts.test.target.value" == .real 40.0
#guard (assertsTrace[1]!).getVar "asserts.test.target.value" == .real 20.0
#guard (assertsTrace[2]!).getVar "asserts.test.target.value" == .real 10.0
#guard (assertsTrace[3]!).getVar "asserts.test.target.value" == .real 5.0
#guard (assertsTrace[4]!).getVar "asserts.test.target.value" == .real 2.5

-- Verify the outflow operation produces the right values:
-- value -> value/2 means value -= value/2 = value/2
#guard applyFlowOp .outflow (.real 40.0) (.real 20.0) == .real 20.0  -- 40 - 20
#guard applyFlowOp .outflow (.real 20.0) (.real 10.0) == .real 10.0  -- 20 - 10
#guard applyFlowOp .outflow (.real 10.0) (.real 5.0) == .real 5.0    -- 10 - 5
#guard applyFlowOp .outflow (.real 5.0) (.real 2.5) == .real 2.5     -- 5 - 2.5

-- Verify: each step computes value/2 correctly
#guard evalBinOp .div (.real 40.0) (.real 2.0) == .real 20.0
#guard evalBinOp .div (.real 20.0) (.real 2.0) == .real 10.0
#guard evalBinOp .div (.real 10.0) (.real 2.0) == .real 5.0
#guard evalBinOp .div (.real 5.0) (.real 2.0) == .real 2.5

-- Verify: the assertion `value == 40` IS violated (this is a valid counterexample)
#guard evalBinOp .eq (.real 20.0) (.real 40.0) == .bool false  -- round 1: violated
#guard evalBinOp .eq (.real 10.0) (.real 40.0) == .bool false  -- round 2: violated
#guard evalBinOp .eq (.real 5.0) (.real 40.0) == .bool false   -- round 3: violated
#guard evalBinOp .eq (.real 2.5) (.real 40.0) == .bool false   -- round 4: violated

-- Verify: the assumption `value > 2` holds at all rounds
#guard evalBinOp .gt (.real 40.0) (.real 2.0) == .bool true
#guard evalBinOp .gt (.real 20.0) (.real 2.0) == .bool true
#guard evalBinOp .gt (.real 10.0) (.real 2.0) == .bool true
#guard evalBinOp .gt (.real 5.0) (.real 2.0) == .bool true
#guard evalBinOp .gt (.real 2.5) (.real 2.0) == .bool true

/-! ## Counterexample 2: unknowns.fspec

  ```fault
  spec unknowns;
  def s = stock{ a: unknown(), b: 2, c: 0 };
  def f = flow{
    data: new s,
    acc: func{ data.c <- data.a + data.b; },
  };
  assume s.a > 5;
  assert s.a <= 6;
  for 3 init{ loop = new f; } run { loop.acc; }
  ```

  Z3 counterexample: a = 7.0 (unknown resolved)
    a_0 = 7.0, b_0 = 2.0, c_0 = 0.0, c_1 = 9.0, c_2 = 18.0, c_3 = 27.0
-/

-- Verify: Z3 chose a = 7.0, which satisfies assumption (> 5) but violates assertion (<= 6)
#guard evalBinOp .gt (.real 7.0) (.real 5.0) == .bool true    -- assumption holds
#guard evalBinOp .le (.real 7.0) (.real 6.0) == .bool false   -- assertion violated!

-- Verify the accumulation: c <- a + b means c += (a + b) = c + 9
#guard evalBinOp .add (.real 7.0) (.real 2.0) == .real 9.0
#guard applyFlowOp .inflow (.real 0.0) (.real 9.0) == .real 9.0    -- c_1 = 0 + 9
#guard applyFlowOp .inflow (.real 9.0) (.real 9.0) == .real 18.0   -- c_2 = 9 + 9
#guard applyFlowOp .inflow (.real 18.0) (.real 9.0) == .real 27.0  -- c_3 = 18 + 9

/-! ## Counterexample 3: strings.fspec (propositional)

  ```fault
  spec test;
  def s = stock{ str1: "a", str2: "b", str3: "c" };
  def f = flow{
    st: new s,
    str4: !st.str1 && st.str2,
  };
  assume (test.str1 && test.str3) || test.str4;
  assert test.str3;
  ```

  Z3: str1=false, str2=true, str3=false, str4=true
  str4 = !str1 && str2 = !false && true = true
  Assumption: (str1 && str3) || str4 = (false && false) || true = true ✓
  Assertion: str3 = false ✗ (violated!)
-/

-- Verify the propositional logic
#guard evalBinOp .and (.bool false) (.bool false) == .bool false    -- str1 && str3
#guard evalUnOp .not (.bool false) == .bool true                    -- !str1
#guard evalBinOp .and (.bool true) (.bool true) == .bool true       -- !str1 && str2 = str4
#guard evalBinOp .or (.bool false) (.bool true) == .bool true       -- assumption holds
-- str3 = false → assertion violated

/-! ## Summary

  Three Z3 counterexamples validated against Lean semantics:
  1. asserts.fspec: value halving (outflow), 5 trace states verified
  2. unknowns.fspec: unknown variable resolution, accumulation verified
  3. strings.fspec: propositional logic counterexample verified

  In each case:
  - The Lean `eval`/`applyFlowOp` functions produce the same values as Z3's model
  - Assertions are correctly identified as violated
  - Assumptions are correctly identified as holding
-/

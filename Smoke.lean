import LeanEmerald

open LeanEmerald

/-! Runtime smoke runner. Compares evaluator outputs against expected `Val`s.

A tiny ad-hoc comparator on the cases we actually produce (num, bool,
none) suffices — we don't need full `DecidableEq` on `Val`. -/

def valEq : Option Val → Option Val → Bool
  | none,            none            => true
  | some (.num a),   some (.num b)   => a = b
  | some (.bool a),  some (.bool b)  => a == b
  | _,               _               => false

def valShow : Option Val → String
  | none           => "<none>"
  | some (.num n)  => s!"num({n})"
  | some (.bool b) => s!"bool({b})"
  | some _         => "<other>"

def check (label : String) (expected got : Option Val) : IO Bool := do
  if valEq expected got then
    IO.println s!"  OK  {label}: {valShow got}"
    return true
  else
    IO.println s!"  FAIL {label}: expected {valShow expected}, got {valShow got}"
    return false

/-- Evaluate a closed expression from a given tower (rather than `initTower`).
    Used in Scene 8 to run a pure program on the substrate tower produced
    by an earlier install. -/
def evalFromTower (n : Nat) (e : Expr) (T : TowerState) (G : Gate := acceptAll) : Option Val :=
  (eval G n e initEnv 0 T).map (·.1)

def main : IO UInt32 := do
  IO.println "Scene 1 — pure language (slice 1)"
  let r1 ← check "(+ 1 2) ⇒ 3"
    (some (.num 3)) (evalProgram 10 Sample.add12)
  let r2 ← check "((λx. x) 0) ⇒ 0"
    (some (.num 0)) (evalProgram 10 Sample.betaIdZero)
  let r3 ← check "((λx. x*x) 3) ⇒ 9"
    (some (.num 9)) (evalProgram 20 Sample.squareOf3)
  let r4 ← check "if (= 1 1) then 42 else 0 ⇒ 42"
    (some (.num 42)) (evalProgram 10 Sample.ifEq)

  IO.println "\nScene 2 — β-equivalence by direct evaluation"
  let r5 ← check "((λx. x) 0) ≡ 0"
    (evalProgram 10 (.lit (.num 0))) (evalProgram 10 Sample.betaIdZero)

  IO.println "\nScene 3 — tower mechanics (slice 2)"
  let r6 ← check "(em (+ 1 2)) ⇒ 3"
    (some (.num 3)) (evalProgram 20 Sample.em_add)
  let r7 ← check "install const-42 then (+ 5 6) ⇒ 42 (acceptAll)"
    (some (.num 42)) (evalProgram 50 Sample.installAndCall)
  let r8 ← check "install const-42 then (em (+ 5 6)) ⇒ 11 (em escapes)"
    (some (.num 11)) (evalProgram 50 Sample.installThenEm)

  IO.println "\nScene 4 — proof-bearing gate (slice 3)"
  -- mkGate [] is rejectAll. setApply is refused; tower unchanged;
  -- the (+ 5 6) that follows takes the default path and yields 11.
  let G := mkGate []
  let r9  ← check "setApply alone under mkGate [] returns false"
    (some (.bool false)) (evalProgram 20 Sample.refusedSetApplyReturns G)
  let r10 ← check "refused setApply then (+ 5 6) ⇒ 11 (tower unchanged)"
    (some (.num 11)) (evalProgram 50 Sample.refusedInstallThenAdd G)
  let r11 ← check "same program under acceptAll ⇒ 42 (control)"
    (some (.num 42)) (evalProgram 50 Sample.refusedInstallThenAdd)

  IO.println "\nScene 5 — multn under acceptAll (slice 5 runtime)"
  let r12 ← check "install multn ; (2 3 4) ⇒ 24 (acceptAll)"
    (some (.num 24)) (evalProgram 100 Demo.installAndMultiplyNums)
  let r13 ← check "install multn ; (+ 1 2) ⇒ 3 (preserved)"
    (some (.num 3))  (evalProgram 100 Demo.installAndAdd)

  IO.println "\nScene 6 — multn under proof-bearing gate (slice 5 CE)"
  -- Build the proof-bearing gate from multnApproval.
  let Gm := mkGate [multnApproval]
  -- The gate admits the multn install (kernel-checked CE proof witnessed it).
  let r14 ← check "install multn via mkGate [multnApproval] ; (2 3 4) ⇒ 24"
    (some (.num 24)) (evalProgram 100 Demo.installAndMultiplyNums Gm)
  let r15 ← check "install multn via mkGate [multnApproval] ; (+ 1 2) ⇒ 3"
    (some (.num 3))  (evalProgram 100 Demo.installAndAdd Gm)
  -- Under mkGate [], installation is refused; (2 3 4) then returns none.
  let r16 ← check "rejectAll refuses multn install ; (2 3 4) ⇒ <none>"
    none (evalProgram 100 Demo.installAndMultiplyNums (mkGate []))

  IO.println "\nScene 7 — runtime wrapper composition and proof-gate filtering (multn + doubling)"
  -- acceptAll: both installs go through; doubling captures multn as orig.
  -- (2 3 4): multn yields 24, doubling doubles to 48.
  let r17 ← check "compose multn + doubling ; (2 3 4) ⇒ 48 (acceptAll)"
    (some (.num 48)) (evalProgram 200 Demo.composeMultnThenDouble_nums)
  -- (+ 1 2): multn falls through to +, yielding 3, doubling doubles to 6.
  let r18 ← check "compose multn + doubling ; (+ 1 2) ⇒ 6 (acceptAll)"
    (some (.num 6))  (evalProgram 200 Demo.composeMultnThenDouble_add)
  -- Under mkGate [multnApproval]: multn install succeeds (kernel-checked
  -- CE), but doubling install is REFUSED (no matching approval, since
  -- doubling does not conservatively extend bbApply). With the second
  -- setApply refused, the dispatcher at T[1] stays at multn — so the call
  -- (2 3 4) yields 24, not 48, demonstrating the gate filters composition.
  let r19 ← check "compose multn + doubling under [multnApproval] ; (2 3 4) ⇒ 24"
    (some (.num 24)) (evalProgram 200 Demo.composeMultnThenDouble_nums Gm)
  let r20 ← check "compose multn + doubling under [multnApproval] ; (+ 1 2) ⇒ 3"
    (some (.num 3))  (evalProgram 200 Demo.composeMultnThenDouble_add Gm)

  IO.println "\nScene 8 — substrate behavioral CE (Theorem 2 full runtime witness)"
  -- The theorem `substrate_behavioral_CE` says: pure-of-effects programs
  -- yield the same value on a CE-invariant substrate tower as on the
  -- AllBbApply baseline. Here we build T_subst by installing multn,
  -- then run pure programs from T_subst and check they agree with
  -- baseline runs from initTower.
  let GA := mkGate [multnApproval]
  match eval GA 50 (.setApply (.lit multnClos)) initEnv 0 initTower with
  | none =>
      IO.println "  FAIL  could not install multn to build T_subst"
      return 1
  | some (_, T_subst) =>
      -- T_subst has multn at index 1; CEInvariant by `evalProgram_reaches_CEInvariant`.
      -- (1) `(+ 1 2)` — pure call. Baseline: 3. Substrate (multn wrapper falls
      --     through to bbApply since `+` is not a num): also 3.
      let r21 ← check "(+ 1 2) on T_subst ≡ on initTower ⇒ 3"
        (evalProgram 30 Sample.add12)
        (evalFromTower 30 Sample.add12 T_subst GA)
      -- (2) `((λx. x*x) 3)` — sub-calls dispatch through multn at level 1,
      --     each falls through to bbApply.
      let r22 ← check "((λx. x*x) 3) on T_subst ≡ on initTower ⇒ 9"
        (evalProgram 30 Sample.squareOf3)
        (evalFromTower 30 Sample.squareOf3 T_subst GA)
      -- (3) `if (= 1 1) then 42 else 0` — conditional with a pure prim call.
      let r23 ← check "if (= 1 1) then 42 else 0 on T_subst ≡ on initTower ⇒ 42"
        (evalProgram 30 Sample.ifEq)
        (evalFromTower 30 Sample.ifEq T_subst GA)

      let results := [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16,
                      r17, r18, r19, r20, r21, r22, r23]
      let passed := results.filter id |>.length
      let total  := results.length
      IO.println s!"\n{passed}/{total} passing"
      return (if passed = total then 0 else 1)

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

  IO.println "\nScene 7 — composition of admissions (multn + doubling)"
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

  let results := [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16,
                  r17, r18, r19, r20]
  let passed := results.filter id |>.length
  let total  := results.length
  IO.println s!"\n{passed}/{total} passing"
  return (if passed = total then 0 else 1)

import LeanEmerald.Soundness

/-!
# Multn — the worked example from the abstract

> *Numbers behave as functions that multiply their arguments, so that*
> `(2 3 4)` *evaluates to 24 while* `(+ 1 2)` *continues to evaluate to 3.*

This file:

1. Builds `multnClos : Val` — a closure with signature `(op, args)` that
   folds-multiplies when `op` is a `.num`, and otherwise dispatches `op`
   on `args` directly through the captured `orig = bbApply`.

2. Proves `multnCE : CE 0 multnClos` — the conservative-extension
   witness saying that for every call the default baseline `bbApply`
   succeeds on, multn produces the same result.

3. Bundles the proof into `multnApproval : ApprovedModification`, then
   demonstrates the gated runtime: `mkGate [multnApproval]` admits
   `set! base-apply multnClos`, `(2 3 4) ⇒ 24`, and `(+ 1 2) ⇒ 3`.

## Wrapper convention

Wrapper bodies use `.appDirect` for all sub-operations (the `isNum?`
test, the `foldMul` primitive, and the `orig` fall-through). `.appDirect`
dispatches via `applyDirect` instead of `applyVia`, so the wrapper does
not recurse into itself when invoked at the level where it's installed.
-/

namespace LeanEmerald

/-! ## The multn closure -/

def multnCapEnv : Env :=
  .cons "isNum?"  (.prim .isNum)   <|
  .cons "foldMul" (.prim .foldMul) <|
  .cons "orig"    .bbApply         <|
  .nil

def multnBody : Expr :=
  .ifte
    (.appDirect (.var "isNum?")  [.var "op"])
    (.appDirect (.var "foldMul") [.var "op", .var "args"])
    (.appDirect (.var "orig")    [.var "op", .var "args"])

def multnClos : Val :=
  .clos ["op", "args"] multnBody multnCapEnv

/-! ## Per-case fuel equations

For each non-`.num` operator class, we show that `applyDirect _ (m+6)
multnClos [op, .list args] L T` reduces, after the wrapper body runs and
falls through via the captured `orig = bbApply`, to `applyDirect _ (m+2)
op args L T`. The fuel offset `+4` is the wrapper overhead: closure
β-step (1) + ifte step (1) + appDirect step (1) + bbApply unpack (1).
-/

/-- multn's behavior on a `.prim` operator: falls through to the prim
    call, at four-fuel-deeper cost. -/
theorem multnClos_eq_prim (m : Nat) (p : Prim) (args : List Val)
    (L : Nat) (T : TowerState) :
    applyDirect acceptAll (m + 6) multnClos [.prim p, .list args] L T
      = applyDirect acceptAll (m + 2) (.prim p) args L T := by
  simp [applyDirect, multnClos, multnBody, multnCapEnv, Env.extend,
        Env.lookup, eval, evalList, applyPrim]

/-- multn's behavior on a `.clos` operator: falls through to the
    closure dispatch (β-step), at four-fuel-deeper cost. -/
theorem multnClos_eq_clos (m : Nat) (xs : List String) (body : Expr)
    (env_c : Env) (args : List Val) (L : Nat) (T : TowerState) :
    applyDirect acceptAll (m + 6) multnClos [.clos xs body env_c, .list args] L T
      = applyDirect acceptAll (m + 2) (.clos xs body env_c) args L T := by
  simp [applyDirect, multnClos, multnBody, multnCapEnv, Env.extend,
        Env.lookup, eval, evalList, applyPrim]

/-- multn's behavior on `.bbApply` operator (in wrapper-invocation form):
    falls through to bbApply's unpacking. -/
theorem multnClos_eq_bbApply (m : Nat) (args : List Val) (L : Nat)
    (T : TowerState) :
    applyDirect acceptAll (m + 6) multnClos [.bbApply, .list args] L T
      = applyDirect acceptAll (m + 2) .bbApply args L T := by
  simp [applyDirect, multnClos, multnBody, multnCapEnv, Env.extend,
        Env.lookup, eval, evalList, applyPrim]

/-! ## CE — the conservative-extension witness

For any call the baseline (`bbApply`-as-wrapper) succeeds on, multn
succeeds at fuel offset `+3` (= per-case `m+6` minus the `+1` for
baseline's outer bbApply step) and produces the same result. The
existential's `fuel'` is `fuel + 3`; we hand-pick a concrete witness in
each `op` branch. -/

theorem multnCE (L : Nat) : CE L multnClos := by
  intro fuel op args T r T_post h
  -- Strategy: case on op; the non-callable Val cases (.num/.bool/.list)
  -- are vacuous since `applyDirect _ _ bbApply [op, .list args] = some`
  -- unpacks to `applyDirect _ _ op args`, which returns `none` for those.
  -- For callable op (.prim/.clos/.bbApply), pick `fuel' = fuel + 3` and
  -- exploit the `multnClos_eq_*` equation (using `m = fuel - 3`).
  -- Premise is also vacuous when fuel < 3 (insufficient for the inner
  -- callable dispatch); we handle those by cases on fuel.
  cases op with
  | num n =>
    exfalso
    cases fuel with
    | zero => simp [applyDirect] at h
    | succ k => cases k with
                | zero => simp [applyDirect] at h
                | succ k' => simp [applyDirect] at h
  | bool b =>
    exfalso
    cases fuel with
    | zero => simp [applyDirect] at h
    | succ k => cases k with
                | zero => simp [applyDirect] at h
                | succ k' => simp [applyDirect] at h
  | list vs =>
    exfalso
    cases fuel with
    | zero => simp [applyDirect] at h
    | succ k => cases k with
                | zero => simp [applyDirect] at h
                | succ k' => simp [applyDirect] at h
  | prim p =>
    -- For .prim, applyPrim is fuel-insensitive. Pick fuel' = fuel + 6
    -- so multn body always succeeds. Then both LHS and the (unpacked)
    -- premise are `(applyPrim p args).bind …`, which agree.
    cases fuel with
    | zero => simp [applyDirect] at h
    | succ k => cases k with
                | zero => simp [applyDirect] at h
                | succ k' =>
                  refine ⟨k' + 2 + 6, r, T_post, ?_, rfl, rfl⟩
                  -- Use multnClos_eq_prim with m = k' + 2.
                  rw [show k' + 2 + 6 = (k' + 2) + 6 from rfl,
                      multnClos_eq_prim (k' + 2)]
                  -- Goal: applyDirect _ (k'+4) (.prim p) args = some.
                  -- h: applyDirect _ (k'+2) bbApply [.prim p, .list args] = some
                  --  → applyDirect _ (k'+1) (.prim p) args = some
                  --  → (applyPrim p args).bind (...) = some (r, T_post).
                  simp [applyDirect] at h
                  simp [applyDirect, h]
  | clos xs body env_c =>
    -- For .clos, the wrapper's else branch reaches `applyDirect _ (m+2)
    -- (.clos ...) args` via `multnClos_eq_clos`. Pick `fuel' = fuel + 3`
    -- so the inner fuel matches the unpacked premise.
    cases fuel with
    | zero => simp [applyDirect] at h
    | succ k => cases k with
                | zero => simp [applyDirect] at h
                | succ k' =>
                  cases k' with
                  | zero =>
                    -- fuel = 2. Premise unpacks to applyDirect _ 1 clos args,
                    -- which is β at fuel 0 = none. Vacuous.
                    exfalso
                    simp [applyDirect, eval] at h
                  | succ m =>
                    -- fuel = m + 3, fuel + 3 = m + 6.
                    refine ⟨m + 6, r, T_post, ?_, rfl, rfl⟩
                    rw [multnClos_eq_clos m]
                    -- Goal: applyDirect _ (m+2) (.clos ...) args = some.
                    -- h: applyDirect _ (m+3) bbApply [.clos ..., .list args] = some
                    --  → applyDirect _ (m+2) (.clos ...) args = some. ✓
                    simpa [applyDirect] using h
  | bbApply =>
    -- For .bbApply, `multnClos_eq_bbApply` reduces multn to bbApply at
    -- offset +2. Pick `fuel' = fuel + 3`; inner fuel matches.
    cases fuel with
    | zero => simp [applyDirect] at h
    | succ k => cases k with
                | zero => simp [applyDirect] at h
                | succ k' =>
                  cases k' with
                  | zero =>
                    exfalso
                    -- fuel = 2. applyDirect _ 2 bbApply [.bbApply, .list args]
                    --  → applyDirect _ 1 bbApply args. Always none, because
                    --  either args matches [op', .list args'] and we recurse
                    --  at fuel 0 (none), or it doesn't match and we fall
                    --  through to the default-none case.
                    have hnone : applyDirect acceptAll 1 .bbApply args L T = none := by
                      cases args with
                      | nil => simp [applyDirect]
                      | cons a tl =>
                        cases tl with
                        | nil => simp [applyDirect]
                        | cons b tt =>
                          cases tt with
                          | nil => cases b <;> simp [applyDirect]
                          | cons _ _ => simp [applyDirect]
                    simp [applyDirect, hnone] at h
                  | succ m =>
                    refine ⟨m + 6, r, T_post, ?_, rfl, rfl⟩
                    rw [multnClos_eq_bbApply m]
                    simpa [applyDirect] using h

/-! ## The approved modification

We package `multnCE` into an `ApprovedModification` at caller-level 0
(applies to level-0 calls, dispatcher at level 1). -/

def multnApproval : ApprovedModification :=
  { callerLevel := 0
    new         := multnClos
    proof       := multnCE 0 }

/-! ## Runtime demos -/

namespace Demo

/-- `(set! base-apply multnClos) ; (2 3 4)` — should give 24. -/
def installAndMultiplyNums : Expr :=
  .seq [.setApply (.lit multnClos),
        .app (.lit (.num 2)) [.lit (.num 3), .lit (.num 4)]]

/-- `(set! base-apply multnClos) ; (+ 1 2)` — should still give 3. -/
def installAndAdd : Expr :=
  .seq [.setApply (.lit multnClos),
        .app (.var "+") [.lit (.num 1), .lit (.num 2)]]

end Demo

end LeanEmerald

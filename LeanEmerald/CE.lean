import LeanEmerald.Eval

/-!
# Proof-bearing admission

`set! base-apply X` can be admitted in two regimes:

1. **Unconditional** — `acceptAll : Gate`. The runtime admits every
   modification. This is what slice 1's and slice 2's smoke uses; it lets
   us demonstrate tower mechanics without yet committing to a soundness
   discipline.

2. **Proof-bearing** — `mkGate approvals : Gate`, where `approvals : List
   ApprovedModification`. Each `ApprovedModification` carries a Lean term
   whose type is `CE callerLevel new` — a soundness witness for that
   specific modification.

The kernel type-checks the proof at construction time: an
`ApprovedModification` value cannot exist unless its `proof` field
type-checks. The runtime gate consults the list structurally
(matching on `callerLevel` and `Val.beq new`), and admits only when some
approval matches.

## The CE predicate

`CE callerLevel new` says:

> for every successful call that the *default* baseline would make
> through `bbApply`, the same call routed through `new`-as-wrapper also
> succeeds, with the same final value and tower state.

We state both sides in the wrapper-invocation form
`applyDirect _ _ [op, .list args]`. The `bbApply` arm is then literally
`applyDirect bbApply [op, .list args]`, which by the unpack case in
`applyDirect` reduces to `applyDirect op args` — direct dispatch. So the
two arms differ only in the dispatcher value (`bbApply` vs `new`).

## What the smoke shows here

Slice 3's smoke installs an empty approval list, builds the gate, and
exercises it on a `set! apply` attempt. The gate refuses (no approval
matches), so `set!` returns `.bool false` and the tower is unchanged.
A subsequent arithmetic call still works because it didn't depend on the
mutation.

The "admits with a real proof" demo lives in slice 5 (`Multn.lean`),
which actually constructs the multn `CE` witness.
-/

namespace LeanEmerald

/-! ## The CE predicate -/

/-- Conservative-extension predicate.

    Read this as: any successful call routed through the `bbApply`
    baseline is also a successful call routed through `new`, with the
    same final result and tower state. -/
def CE (callerLevel : Nat) (new : Val) : Prop :=
  ∀ (fuel : Nat) (op : Val) (args : List Val)
    (T : TowerState) (r : Val) (T_post : TowerState),
    applyDirect acceptAll fuel .bbApply [op, .list args]
      callerLevel T = some (r, T_post) →
    ∃ (fuel' : Nat) (r' : Val) (T_post' : TowerState),
      applyDirect acceptAll fuel' new [op, .list args]
        callerLevel T = some (r', T_post')
      ∧ r = r' ∧ T_post = T_post'

/-! ## Approved modifications -/

/-- A kernel-checked admission record. The `proof` field's type
    witnesses that installing `new` at the apply cell *one above*
    `callerLevel` does not disturb the call trace. -/
structure ApprovedModification where
  callerLevel : Nat
  new         : Val
  proof       : CE callerLevel new

/-- Structural match: does `(L, oldVal, newVal)` match this approval?
    The `_old` argument is unused — we match only on `callerLevel` and
    on the structural shape of `newVal`. -/
def ApprovedModification.matches (am : ApprovedModification)
    (L : Nat) (_old new : Val) : Bool :=
  am.callerLevel == L && Val.beq am.new new

/-- The runtime gate built from a list of approvals. Accepts iff some
    approval matches. -/
def mkGate (approvals : List ApprovedModification) : Gate :=
  fun L old new => approvals.any (·.matches L old new)

/-! ## Trivial gates from approval lists -/

example : mkGate [] = rejectAll := by
  funext L old new
  simp [mkGate, rejectAll]

end LeanEmerald

import LeanEmerald.Doubling
import LeanEmerald.SubstrateBehaviorFull

/-!
# Doubling is *not* a conservative extension

`Doubling.lean` notes in prose that `doublingClos` cannot carry a `CE 0`
witness — it changes `(+ 1 2)` from `3` to `6`. This file turns that
asymmetry into a theorem, giving the worked example a fully formal pair:

* `multnCE : CE 0 multnClos`            — certified conservative extension
* `not_CE_doublingClos : ¬ CE 0 doublingClos` — provably *not* one

The witness is the single call `(+ 1 2)`: the `bbApply` baseline yields
`3`, while `doublingClos` yields `6` at every fuel that succeeds. Because
`CE`'s conclusion existentially quantifies the wrapper's fuel, the refutation
routes through `applyDirect_fuel_add` (fuel monotonicity): any successful
doubling dispatch is lifted to a common fuel with the concrete `⇒ 6`
computation, and determinism forces `3 = 6`.
-/

namespace LeanEmerald

/-- The `bbApply` baseline succeeds on `(+ 1 2)` with `3`, tower unchanged. -/
theorem bbApply_add_baseline (T : TowerState) :
    applyDirect acceptAll 2 .bbApply [.prim .add, .list [.num 1, .num 2]] 0 T
      = some (.num 3, T) := by
  simp [applyDirect, applyPrim]

/-- `doublingClos` maps the same call to `6`, not `3` (tower unchanged). -/
theorem doublingClos_add_six (T : TowerState) :
    applyDirect acceptAll 20 doublingClos
        [.prim .add, .list [.num 1, .num 2]] 0 T
      = some (.num 6, T) := by
  simp [applyDirect, doublingClos, doublingBody, doublingCapEnv,
        multnClos, multnBody, multnCapEnv, Env.extend, Env.lookup,
        eval, evalList, applyPrim]

/-- `doublingClos` is not a conservative extension of the baseline: it
    changes `(+ 1 2)` from `3` to `6`, so no `CE 0` witness can exist. -/
theorem not_CE_doublingClos : ¬ CE 0 doublingClos := by
  intro h
  -- Baseline succeeds with `3` at the witness call.
  obtain ⟨fuel', r', T', hsucc, hr, _⟩ :=
    h 2 (.prim .add) [.num 1, .num 2] initTower (.num 3) initTower
      (bbApply_add_baseline initTower)
  -- Doubling concretely yields `6` at fuel 20.
  have hdbl := doublingClos_add_six initTower
  -- Lift both successes to the common fuel `fuel' + 20`.
  have hA := applyDirect_fuel_add acceptAll fuel' doublingClos
    [.prim .add, .list [.num 1, .num 2]] 0 initTower r' T' hsucc 20
  have hB := applyDirect_fuel_add acceptAll 20 doublingClos
    [.prim .add, .list [.num 1, .num 2]] 0 initTower (.num 6) initTower hdbl fuel'
  rw [Nat.add_comm 20 fuel'] at hB
  rw [hA] at hB
  -- `some (r', T') = some (.num 6, T6)` ⇒ `r' = .num 6`, contradicting `3 = r'`.
  rw [Option.some.injEq, Prod.mk.injEq] at hB
  have : (Val.num 3) = .num 6 := hr.trans hB.1
  simp at this

end LeanEmerald

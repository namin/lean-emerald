# lean-emerald

A clean-room rebuild of the reflective-tower-with-proof-bearing-CE
substrate from [lean-sage](https://github.com/namin/lean-sage), in ~3.6k LOC instead of ~19k,
prioritizing elegance and pedagogy.

## Status

* **Build:** `lake build` — clean. **Sorry-free across all 10 library files.**
* **Smoke:** `lake exe smoke` — 23/23 across 8 scenes.
* **Lean toolchain:** v4.30.0 (matches lean-sage).

## What's mechanized

| Theorem | What it says |
|---|---|
| `betaIdZero_gate_indep_keynote` | `evalProgram 10 ((λx.x) 0) G = evalProgram 10 0 G` for any `Gate` `G`. The canonical β-redex pair from the abstract, proved by direct reduction on the concrete initial state. Gate-independence of a *pure* pair: the gate is never reached. |
| `eval_pure_gate_indep` | The general statement: *every* pure expression evaluates the same under any pair of gates. Joint induction on fuel, bundled with `Pure` preservation across `eval` / `evalList` / `evalSeq` / `applyVia` / `applyDirect`. |
| `pure_pair_equality_gate_indep` | If a pair of pure terms `M`, `N` evaluates to the same value under *some* gate at any pure initial tower, they do so under *every* gate. A gate-transfer lemma for pure terms. |
| `multnCE 0 multnClos` | For every call the baseline `bbApply` succeeds on at level 0, the `multn` wrapper produces the same result. The conservative-extension witness for the worked example. |
| `multnApproval : ApprovedModification` | `multnCE` packaged into an admission record. Kernel-checked. |
| `not_CE_doublingClos` | `¬ CE 0 doublingClos`: the `doubling` wrapper changes `(+ 1 2)` from `3` to `6`, so no `CE 0` witness can exist. The negative half of the worked pair (with `multnCE`), proved via fuel monotonicity (`applyDirect_fuel_add`). |
| `jointInv` (**Theorem 1**) | For any `mkGate approvals` and any reachable state from a `CEInvariant`-holding tower, the resulting tower satisfies `CEInvariant`. The state-level substrate-CE invariant. |
| `applyVia_substrate_extends_baseline` (**Theorem 2 lite**) | At a pure, CE-invariant materialized tower, a baseline-direct dispatch's success implies the substrate's `applyVia` succeeds with the same value. The dispatch-level substrate-CE lift. |
| `substrate_behavioral_CE` (**Theorem 2 full**) | For pure-of-effects program `e`, pure `ρ`, `AllBbApply` baseline tower `T_base`, and `CEInvariant` substrate tower `T_subst`: a baseline success under `acceptAll` lifts to a substrate success under `mkGate approvals` with the same value. The eval-level substrate behavioral CE. |
| `substrate_behavioral_CE_initTower`, `..._initEnv`, `substrate_extends_baseline_evalProgram` | Specializations to `initTower` / `initEnv` / `evalProgram` form. |

## Scope

Two boundaries worth stating precisely, so the results are not over-read:

* **Dispatch, not governance.** The admission decision is taken by the
  `Gate` — an *external* parameter `Nat → Val → Val → Bool` threaded
  through `eval`. The per-level `policy` cell is reflectively writable via
  `.setPolicy`, but it is never consulted to govern an admission: the gate
  is fixed for a run, and `.setApply` decides on `G L oldApply vNew`
  alone. So Emerald demonstrates *reflectively modifiable dispatch under a
  fixed gate*, not a self-modifying admission policy. For the
  gates-the-gate (governance) theorem, see lean-keep.

* **Preservation is baseline-relative, not chain-relative.** `CE
  callerLevel new` and every `ApprovedModification` are stated against the
  fixed `bbApply` baseline (`ApprovedModification.matches` ignores the old
  dispatcher). Hence Theorem 1 (`jointInv`) guarantees that *every
  reachable dispatcher conservatively extends the original baseline* — it
  does **not** guarantee that each admission preserves the behavior added
  by its predecessors. A later baseline-CE dispatcher may drop an earlier
  extension while still extending `bbApply`. For selective, successor-
  relative chain composition, see lean-sage.

## File map

| File | LOC | Carries |
|---|---|---|
| `LeanEmerald/Syntax.lean` | 180 | `Val`/`Expr`/`Env`/`Prim`/`Level`/`TowerState` types; structural `Val.beq`/`Expr.beq`/`Env.beq` |
| `LeanEmerald/Eval.lean` | 323 | Tower helpers (`materialize`, `applyAt`, `setApplyAt`); the `Gate` abbreviation; the mutually-recursive evaluator (`eval`, `evalList`, `evalSeq`, `applyVia`, `applyDirect`); `evalProgram`; sample expressions for smoke |
| `LeanEmerald/CE.lean` | 97 | `CE` predicate; `ApprovedModification` structure; `mkGate`; equation `mkGate [] = rejectAll` |
| `LeanEmerald/Soundness.lean` | 770 | `Pure` predicates; side lemmas; the 10-conjunct `Joint` claim with `joint : ∀ n, Joint n`; `eval_pure_gate_indep`; `betaIdZero_gate_indep_keynote`; `pure_pair_equality_gate_indep` |
| `LeanEmerald/Multn.lean` | 225 | `multnClos`; three equations `multnClos_eq_{prim,clos,bbApply}`; `multnCE`; `multnApproval` |
| `LeanEmerald/Doubling.lean` | 83 | `doublingClos` (captures `multnClos` as `orig`); runtime composition demos |
| `LeanEmerald/Substrate.lean` | 637 | `Val.beq_eq` family; `CE_bbApply`; `TowerState.CEInvariant`; `initTower_CEInvariant`; `materialize_CEInvariant`; `setApplyAt_CEInvariant`; `setPolicyAt_CEInvariant`; `mkGate_admits_CE`; `JointInv` and `jointInv` (**Theorem 1**) |
| `LeanEmerald/SubstrateBehavior.lean` | 176 | `applyDirect_pure_gate_indep` (extracted from `Joint`); `CEInvariant_applyAt_CE`; `applyDirect_bbApply_unpack`; `applyVia_substrate_extends_baseline` (**Theorem 2 lite**) |
| `LeanEmerald/SubstrateBehaviorFull.lean` | 959 | `TowerState.AllBbApply` invariant + preservation; joint fuel monotonicity `jointFuelMono`; the 5-conjunct cross-tower `JointBeh` and proof `jointBeh`; `substrate_behavioral_CE` (**Theorem 2 full**) and its `initTower` / `initEnv` / `evalProgram` corollaries |
| `LeanEmerald/DoublingNotCE.lean` | 61 | `not_CE_doublingClos` — the formal negative result completing the `multn` (CE-certified) / `doubling` (not CE) pair, via `applyDirect_fuel_add` |
| `Smoke.lean` | 139 | Runtime test scenes (8 scenes, 23 assertions) |

## Smoke scenes

```
Scene 1 — pure language (slice 1)
Scene 2 — β-equivalence by direct evaluation
Scene 3 — tower mechanics (slice 2)
Scene 4 — proof-bearing gate (slice 3)
Scene 5 — multn under acceptAll (slice 5 runtime)
Scene 6 — multn under proof-bearing gate (slice 5 CE)
Scene 7 — runtime wrapper composition and proof-gate filtering (multn + doubling)
Scene 8 — substrate behavioral CE (Theorem 2 full runtime witness)
```

Scene 6 demonstrates the full proof-bearing path: `mkGate
[multnApproval]` admits `set! base-apply multnClos`, observes `(2 3 4)
⇒ 24`, preserves `(+ 1 2) ⇒ 3`, and refuses the install under `mkGate
[]`. Scene 7 separates runtime wrapper composition from proof-gate
filtering: under `acceptAll` both `multn` then `doubling` installs go
through (yielding `(2 3 4) ⇒ 48`, `(+ 1 2) ⇒ 6`) — this is the wrappers
composing operationally, *not* proof-bearing admission — while `mkGate
[multnApproval]` admits only `multn` and refuses the `doubling` install
(no matching approval — doubling does not conservatively extend
`bbApply`), leaving multn's behavior intact.

Scene 8 is the runtime witness for **Theorem 2 full**: build a
substrate tower `T_subst` by installing `multn` from `initTower` under
`mkGate [multnApproval]`, then run pure-of-effects programs from
`T_subst` and check they yield the same value as on `initTower`. The
multn wrapper sits in `T_subst[1].apply` but falls through to `bbApply`
on `+`/`λ`/`if` operators (since they're not `.num`), so `(+ 1 2) ⇒ 3`,
`((λx. x*x) 3) ⇒ 9`, and `if (= 1 1) then 42 else 0 ⇒ 42` all match
their baseline values.

## How to build and run

```bash
lake build         # type-check the whole library
lake exe smoke     # 23/23 across 8 scenes
```

## Design fundamentals

The choices that made this short:

1. **Substitution-style closures.** `.clos params body env` captures
   its env by value. No global heap, no shift apparatus. This
   eliminates lean-sage's `Bisim.lean` (4.5k) and `Frame.lean` (4.9k)
   entirely.

2. **Per-level mutable cells, not a general heap.** Each `Level` has
   just `apply : Val` and `policy : Val`. The "heap" of lean-sage's
   framing reduces to "the per-level cells."

3. **β as an operational rule.** `eval`'s `.app` rule on a closure
   operator extends the env and evaluates the body. β-equivalence on
   the canonical pair is then provable by direct reduction on the
   concrete initial state.

4. **Gate as a function parameter.** `Gate := Nat → Val → Val → Bool`.
   The evaluator threads it through `.setApply`/`.setPolicy`. `acceptAll`
   for the unconditional regime; `mkGate approvals` for the
   proof-bearing one.

5. **`.appDirect` as a wrapper-internal dispatch primitive.** Wrapper
   bodies use `.appDirect` (bypasses `applyVia`) for `isNum?`,
   `foldMul`, and `orig` fall-through. Avoids wrapper self-recursion
   without the `(em ...)` trick — and makes multn's CE proof tractable.

6. **`bbApply`-unpack case in `applyDirect`.** Pattern `applyDirect _
   _+1 .bbApply [op_val, .list args_val] L T = applyDirect _ _ op_val
   args_val L T`. Means "calling `bbApply` in the wrapper-invocation
   form unpacks to direct dispatch on the inner operator." Required
   for the `orig`-fall-through chain to terminate cleanly.

7. **Cross-tower CE via per-cell `CE` + fuel monotonicity.** Theorem 2
   full lifts the per-cell `CE` predicate (same-tower) up to a
   cross-tower behavioral claim via a 5-conjunct joint induction
   comparing two evaluations side-by-side. At the substrate's
   non-bbApply dispatcher, the proof routes through `CE` (which lives
   on `acceptAll`-form) via four gate/form swaps; pre-proved fuel
   monotonicity (`jointFuelMono`) aligns the existential sub-fuels
   produced at each `.app` site.

import LeanEmerald.Substrate
import LeanEmerald.Soundness

/-!
# Substrate behavioral CE at the dispatch level

The state-level claim is `TowerState.CEInvariant` (Theorem 1, in
`Substrate.lean`): every reachable tower has CE-related apply cells.

This file lifts the per-cell CE relation up to the *dispatch* level
(applyVia). The claim:

> Given a pure, CE-invariant tower `T` and a pure operator + args, if
> the baseline direct dispatch (`applyDirect` on `op` at `k`) at
> `T.materialize (k+1)` succeeds with value `r`, then the substrate
> dispatch via `applyVia` at level `k+1` on the same inputs also
> succeeds with value `r`, under any `mkGate approvals` whose
> approvals carry pure `new` values.

We parameterize by `k` (so dispatch level is `k+1 ≥ 1`) to avoid the
degenerate `dL = 0` case where the invariant has nothing to say
about `T[0]`.

This is the strongest behavioral claim directly derivable from the
per-cell CE primitive without additional infrastructure
(materialize-irrelevance, cross-tower CE primitives, or
wrapper-restriction predicates).

## Why it stops at the dispatch level

Lifting from `applyVia` to a full `eval`-level cross-tower CE claim
("substrate eval on pure-of-effects program lifts baseline eval")
runs into a structural obstacle: the existing `CE callerLevel new`
predicate gives *same-tower* CE — applyDirect at the same tower T
under two different dispatchers. Lifting to *cross-tower* CE
(baseline tower vs substrate tower) requires either:

- a stronger CE primitive that quantifies over compatible towers, or
- a tower-independence side condition on wrapper bodies (e.g., a
  predicate that forbids `.app` in wrapper closures), or
- a materialize-irrelevance lemma that applyDirect is invariant under
  appending default cells.

None of these is a packaging exercise. The dispatch-level claim
below sidesteps them by stating the premise on the same tower as the
substrate's materialized state — the user is responsible for
materializing first. -/

namespace LeanEmerald

/-! ## Extract `applyDirect` gate-independence from `Joint` -/

theorem applyDirect_pure_gate_indep (G G' : Gate) (n : Nat)
    (op : Val) (args : List Val) (L : Nat) (T : TowerState)
    (hOp : op.Pure = true) (hArgs : ValList.Pure args = true)
    (hT : T.Pure = true) :
    applyDirect G n op args L T = applyDirect G' n op args L T :=
  (joint n).2.2.2.2.2.2.2.2.1 G G' op args L T hOp hArgs hT

/-! ## CE extraction from `CEInvariant` -/

/-- The dispatcher at index `k+1` of an invariant tower is CE-related
    at level `k`. Whether the cell is populated or defaulted to
    `bbApply`, `CE` holds. -/
theorem CEInvariant_applyAt_CE
    (T : TowerState) (hT_inv : T.CEInvariant) (k : Nat) :
    CE k (T.applyAt (k + 1)) := by
  unfold TowerState.applyAt
  split
  case h_1 _ lvl heq => exact hT_inv k lvl heq
  case h_2 => show CE k .bbApply; exact CE_bbApply k

/-! ## bbApply unpack at applyDirect level -/

theorem applyDirect_bbApply_unpack
    (G : Gate) (fuel : Nat) (op : Val) (args : List Val)
    (L : Nat) (T : TowerState) (r : Val) (T_post : TowerState)
    (h : applyDirect G fuel op args L T = some (r, T_post)) :
    applyDirect G (fuel + 1) .bbApply [op, .list args] L T = some (r, T_post) := by
  simp [applyDirect]; exact h

/-! ## The headline dispatch-level theorem

If a baseline-style direct dispatch on `(op, args)` at level `k`
succeeds at a pure, CE-invariant materialized tower, then the
substrate's `applyVia` at level `k+1` on `(op, args)` also succeeds
with the same value `r`, under any `mkGate approvals` whose
approvals carry pure `new` values. -/

theorem applyVia_substrate_extends_baseline
    (approvals : List ApprovedModification)
    (_hPureA : ∀ am ∈ approvals, am.new.Pure = true)
    (k : Nat) (op : Val) (args : List Val) (T : TowerState)
    (hOp : op.Pure = true) (hArgs : ValList.Pure args = true)
    (hT : T.Pure = true) (hT_inv : T.CEInvariant)
    (fuel : Nat) (r : Val) (T_post : TowerState)
    (h : applyDirect acceptAll fuel op args k
           (T.materialize (k + 1)) = some (r, T_post)) :
    ∃ fuel' T_post',
      applyVia (mkGate approvals) fuel' (k + 1) op args T = some (r, T_post') := by
  -- Materialized tower is pure + invariant
  have hTmat_pure := TowerState.materialize_Pure T (k + 1) hT
  have hTmat_inv := materialize_CEInvariant T (k + 1) hT_inv
  -- The dispatcher value at index k+1 is pure
  have hDisp_pure : ((T.materialize (k + 1)).applyAt (k + 1)).Pure = true :=
    TowerState.applyAt_Pure hTmat_pure
  -- args wrapped as [op, .list args] is also pure
  have hArgs_wrapped : ValList.Pure [op, .list args] = true := by
    simp [ValList.Pure, Val.Pure]; exact ⟨hOp, hArgs⟩
  -- Get CE for the dispatcher
  have hCE_disp : CE k ((T.materialize (k + 1)).applyAt (k + 1)) :=
    CEInvariant_applyAt_CE (T.materialize (k + 1)) hTmat_inv k
  -- Case split on whether dispatcher is bbApply
  by_cases hbb : (T.materialize (k + 1)).applyAt (k + 1) = .bbApply
  · -- Dispatcher is bbApply → applyVia unpacks to applyDirect on (op, args)
    refine ⟨fuel + 1, T_post, ?_⟩
    simp only [applyVia, hbb, Nat.add_sub_cancel]
    -- Goal: applyDirect (mkGate approvals) fuel op args k T_mat = some (r, T_post)
    rw [applyDirect_pure_gate_indep (mkGate approvals) acceptAll fuel op args k
          (T.materialize (k + 1)) hOp hArgs hTmat_pure]
    exact h
  · -- Dispatcher is some v ≠ bbApply → applyVia routes via v [op, .list args]
    -- Derive the bbApply premise from h via the unpack rule
    have h_bb : applyDirect acceptAll (fuel + 1) .bbApply [op, .list args] k
                (T.materialize (k + 1)) = some (r, T_post) :=
      applyDirect_bbApply_unpack acceptAll fuel op args k
        (T.materialize (k + 1)) r T_post h
    -- Apply CE
    obtain ⟨fuel_v, r', T_post', h_v, hr_eq, hT_eq⟩ :=
      hCE_disp (fuel + 1) op args (T.materialize (k + 1)) r T_post h_bb
    -- h_v : applyDirect acceptAll fuel_v (T_mat.applyAt (k+1)) [op, .list args] k T_mat
    --       = some (r', T_post')
    refine ⟨fuel_v + 1, T_post', ?_⟩
    simp only [applyVia, Nat.add_sub_cancel]
    -- v ≠ bbApply, so the match goes to the second arm
    cases hv : (T.materialize (k + 1)).applyAt (k + 1) with
    | bbApply => exact absurd hv hbb
    | num n =>
      have hv_pure : (Val.num n).Pure = true := by simp [Val.Pure]
      rw [hv] at h_v
      rw [applyDirect_pure_gate_indep (mkGate approvals) acceptAll fuel_v (.num n)
            [op, .list args] k (T.materialize (k + 1))
            hv_pure hArgs_wrapped hTmat_pure]
      rw [hr_eq]; exact h_v
    | bool b =>
      have hv_pure : (Val.bool b).Pure = true := by simp [Val.Pure]
      rw [hv] at h_v
      rw [applyDirect_pure_gate_indep (mkGate approvals) acceptAll fuel_v (.bool b)
            [op, .list args] k (T.materialize (k + 1))
            hv_pure hArgs_wrapped hTmat_pure]
      rw [hr_eq]; exact h_v
    | prim p =>
      have hv_pure : (Val.prim p).Pure = true := by simp [Val.Pure]
      rw [hv] at h_v
      rw [applyDirect_pure_gate_indep (mkGate approvals) acceptAll fuel_v (.prim p)
            [op, .list args] k (T.materialize (k + 1))
            hv_pure hArgs_wrapped hTmat_pure]
      rw [hr_eq]; exact h_v
    | clos xs body env_c =>
      have hv_pure : (Val.clos xs body env_c).Pure = true := by
        rw [← hv]; exact hDisp_pure
      rw [hv] at h_v
      rw [applyDirect_pure_gate_indep (mkGate approvals) acceptAll fuel_v
            (.clos xs body env_c) [op, .list args] k (T.materialize (k + 1))
            hv_pure hArgs_wrapped hTmat_pure]
      rw [hr_eq]; exact h_v
    | list vs =>
      have hv_pure : (Val.list vs).Pure = true := by
        rw [← hv]; exact hDisp_pure
      rw [hv] at h_v
      rw [applyDirect_pure_gate_indep (mkGate approvals) acceptAll fuel_v (.list vs)
            [op, .list args] k (T.materialize (k + 1))
            hv_pure hArgs_wrapped hTmat_pure]
      rw [hr_eq]; exact h_v

end LeanEmerald

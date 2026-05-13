import LeanEmerald.CE

/-!
# Substrate invariant

The keynote-level claim "the substrate is always a conservative
extension of the base" interpreted at the *tower-state* level: every
apply cell at index `k+1` that gets written during gated execution
satisfies `CE k`. The gate enforces this per modification (each
approval carries a `CE` proof); this file lifts the per-modification
invariant to a substrate-wide claim that holds across the whole
program.

## Plan

1. `Val.beq_eq` and companions — bridge Boolean structural equality
   used by the runtime gate matcher to Lean propositional equality
   used by `CE`.
2. `CE_bbApply` — bbApply trivially CE-extends itself.
3. `TowerState.CEInvariant` — every consultable cell (index ≥ 1) is
   CE-related to bbApply at the appropriate level.
4. Sub-lemmas: `initTower_CEInvariant`, `materialize_CEInvariant`,
   `setApplyAt_CEInvariant`, `setPolicyAt_CEInvariant`.
5. `mkGate_admits_CE` — the gate-true premise extracts a `CE` witness.
6. Main joint induction: `eval` (and friends) preserve `CEInvariant`.
-/

namespace LeanEmerald

/-! ## Boolean beq reflects Lean equality

A mutual induction over `Val`, `Expr`, `Env` showing that the
runtime structural beq used at the gate matcher coincides with
propositional equality. -/

mutual

theorem Val.beq_eq : ∀ {v1 v2 : Val}, Val.beq v1 v2 = true → v1 = v2
  | .num _,     .num _,     h => by simp [Val.beq] at h; rw [h]
  | .bool _,    .bool _,    h => by simp [Val.beq] at h; rw [h]
  | .prim p,    .prim q,    h => by
      simp [Val.beq] at h
      cases p <;> cases q <;> simp [Prim.beq] at h <;> rfl
  | .bbApply,   .bbApply,   _ => rfl
  | .clos xs body env_c, .clos ys body' env_c', h => by
      simp [Val.beq] at h
      obtain ⟨⟨hxs, hbody⟩, henv⟩ := h
      rw [hxs, Expr.beq_eq hbody, Env.beq_eq henv]
  | .list l1,   .list l2,   h => by
      simp [Val.beq] at h
      rw [Val.listBeq_eq h]
  | .num _,     .bool _,    h => by simp [Val.beq] at h
  | .num _,     .prim _,    h => by simp [Val.beq] at h
  | .num _,     .bbApply,   h => by simp [Val.beq] at h
  | .num _,     .clos _ _ _, h => by simp [Val.beq] at h
  | .num _,     .list _,    h => by simp [Val.beq] at h
  | .bool _,    .num _,     h => by simp [Val.beq] at h
  | .bool _,    .prim _,    h => by simp [Val.beq] at h
  | .bool _,    .bbApply,   h => by simp [Val.beq] at h
  | .bool _,    .clos _ _ _, h => by simp [Val.beq] at h
  | .bool _,    .list _,    h => by simp [Val.beq] at h
  | .prim _,    .num _,     h => by simp [Val.beq] at h
  | .prim _,    .bool _,    h => by simp [Val.beq] at h
  | .prim _,    .bbApply,   h => by simp [Val.beq] at h
  | .prim _,    .clos _ _ _, h => by simp [Val.beq] at h
  | .prim _,    .list _,    h => by simp [Val.beq] at h
  | .bbApply,   .num _,     h => by simp [Val.beq] at h
  | .bbApply,   .bool _,    h => by simp [Val.beq] at h
  | .bbApply,   .prim _,    h => by simp [Val.beq] at h
  | .bbApply,   .clos _ _ _, h => by simp [Val.beq] at h
  | .bbApply,   .list _,    h => by simp [Val.beq] at h
  | .clos _ _ _, .num _,    h => by simp [Val.beq] at h
  | .clos _ _ _, .bool _,   h => by simp [Val.beq] at h
  | .clos _ _ _, .prim _,   h => by simp [Val.beq] at h
  | .clos _ _ _, .bbApply,  h => by simp [Val.beq] at h
  | .clos _ _ _, .list _,   h => by simp [Val.beq] at h
  | .list _,    .num _,     h => by simp [Val.beq] at h
  | .list _,    .bool _,    h => by simp [Val.beq] at h
  | .list _,    .prim _,    h => by simp [Val.beq] at h
  | .list _,    .bbApply,   h => by simp [Val.beq] at h
  | .list _,    .clos _ _ _, h => by simp [Val.beq] at h

theorem Val.listBeq_eq : ∀ {l1 l2 : List Val}, Val.listBeq l1 l2 = true → l1 = l2
  | [],        [],        _ => rfl
  | v1 :: l1', v2 :: l2', h => by
      simp [Val.listBeq] at h
      rw [Val.beq_eq h.1, Val.listBeq_eq h.2]
  | [],        _ :: _,    h => by simp [Val.listBeq] at h
  | _ :: _,    [],        h => by simp [Val.listBeq] at h

theorem Expr.beq_eq : ∀ {e1 e2 : Expr}, Expr.beq e1 e2 = true → e1 = e2
  | .lit v1,    .lit v2,    h => by
      simp [Expr.beq] at h; rw [Val.beq_eq h]
  | .var x,     .var y,     h => by simp [Expr.beq] at h; rw [h]
  | .lam xs b,  .lam ys b', h => by
      simp [Expr.beq] at h
      rw [h.1, Expr.beq_eq h.2]
  | .app f as,  .app g bs,  h => by
      simp [Expr.beq] at h
      rw [Expr.beq_eq h.1, Expr.listBeq_eq h.2]
  | .appDirect f as, .appDirect g bs, h => by
      simp [Expr.beq] at h
      rw [Expr.beq_eq h.1, Expr.listBeq_eq h.2]
  | .em e1,     .em e2,     h => by
      simp [Expr.beq] at h; rw [Expr.beq_eq h]
  | .setApply e1, .setApply e2, h => by
      simp [Expr.beq] at h; rw [Expr.beq_eq h]
  | .setPolicy e1, .setPolicy e2, h => by
      simp [Expr.beq] at h; rw [Expr.beq_eq h]
  | .ifte c1 t1 e1, .ifte c2 t2 e2, h => by
      simp [Expr.beq] at h
      rw [Expr.beq_eq h.1.1, Expr.beq_eq h.1.2, Expr.beq_eq h.2]
  | .seq es1,   .seq es2,   h => by
      simp [Expr.beq] at h; rw [Expr.listBeq_eq h]
  -- mismatched cases (vacuous)
  | .lit _,        .var _,         h => by simp [Expr.beq] at h
  | .lit _,        .lam _ _,       h => by simp [Expr.beq] at h
  | .lit _,        .app _ _,       h => by simp [Expr.beq] at h
  | .lit _,        .appDirect _ _, h => by simp [Expr.beq] at h
  | .lit _,        .em _,          h => by simp [Expr.beq] at h
  | .lit _,        .setApply _,    h => by simp [Expr.beq] at h
  | .lit _,        .setPolicy _,   h => by simp [Expr.beq] at h
  | .lit _,        .ifte _ _ _,    h => by simp [Expr.beq] at h
  | .lit _,        .seq _,         h => by simp [Expr.beq] at h
  | .var _,        .lit _,         h => by simp [Expr.beq] at h
  | .var _,        .lam _ _,       h => by simp [Expr.beq] at h
  | .var _,        .app _ _,       h => by simp [Expr.beq] at h
  | .var _,        .appDirect _ _, h => by simp [Expr.beq] at h
  | .var _,        .em _,          h => by simp [Expr.beq] at h
  | .var _,        .setApply _,    h => by simp [Expr.beq] at h
  | .var _,        .setPolicy _,   h => by simp [Expr.beq] at h
  | .var _,        .ifte _ _ _,    h => by simp [Expr.beq] at h
  | .var _,        .seq _,         h => by simp [Expr.beq] at h
  | .lam _ _,      .lit _,         h => by simp [Expr.beq] at h
  | .lam _ _,      .var _,         h => by simp [Expr.beq] at h
  | .lam _ _,      .app _ _,       h => by simp [Expr.beq] at h
  | .lam _ _,      .appDirect _ _, h => by simp [Expr.beq] at h
  | .lam _ _,      .em _,          h => by simp [Expr.beq] at h
  | .lam _ _,      .setApply _,    h => by simp [Expr.beq] at h
  | .lam _ _,      .setPolicy _,   h => by simp [Expr.beq] at h
  | .lam _ _,      .ifte _ _ _,    h => by simp [Expr.beq] at h
  | .lam _ _,      .seq _,         h => by simp [Expr.beq] at h
  | .app _ _,      .lit _,         h => by simp [Expr.beq] at h
  | .app _ _,      .var _,         h => by simp [Expr.beq] at h
  | .app _ _,      .lam _ _,       h => by simp [Expr.beq] at h
  | .app _ _,      .appDirect _ _, h => by simp [Expr.beq] at h
  | .app _ _,      .em _,          h => by simp [Expr.beq] at h
  | .app _ _,      .setApply _,    h => by simp [Expr.beq] at h
  | .app _ _,      .setPolicy _,   h => by simp [Expr.beq] at h
  | .app _ _,      .ifte _ _ _,    h => by simp [Expr.beq] at h
  | .app _ _,      .seq _,         h => by simp [Expr.beq] at h
  | .appDirect _ _, .lit _,        h => by simp [Expr.beq] at h
  | .appDirect _ _, .var _,        h => by simp [Expr.beq] at h
  | .appDirect _ _, .lam _ _,      h => by simp [Expr.beq] at h
  | .appDirect _ _, .app _ _,      h => by simp [Expr.beq] at h
  | .appDirect _ _, .em _,         h => by simp [Expr.beq] at h
  | .appDirect _ _, .setApply _,   h => by simp [Expr.beq] at h
  | .appDirect _ _, .setPolicy _,  h => by simp [Expr.beq] at h
  | .appDirect _ _, .ifte _ _ _,   h => by simp [Expr.beq] at h
  | .appDirect _ _, .seq _,        h => by simp [Expr.beq] at h
  | .em _,         .lit _,         h => by simp [Expr.beq] at h
  | .em _,         .var _,         h => by simp [Expr.beq] at h
  | .em _,         .lam _ _,       h => by simp [Expr.beq] at h
  | .em _,         .app _ _,       h => by simp [Expr.beq] at h
  | .em _,         .appDirect _ _, h => by simp [Expr.beq] at h
  | .em _,         .setApply _,    h => by simp [Expr.beq] at h
  | .em _,         .setPolicy _,   h => by simp [Expr.beq] at h
  | .em _,         .ifte _ _ _,    h => by simp [Expr.beq] at h
  | .em _,         .seq _,         h => by simp [Expr.beq] at h
  | .setApply _,   .lit _,         h => by simp [Expr.beq] at h
  | .setApply _,   .var _,         h => by simp [Expr.beq] at h
  | .setApply _,   .lam _ _,       h => by simp [Expr.beq] at h
  | .setApply _,   .app _ _,       h => by simp [Expr.beq] at h
  | .setApply _,   .appDirect _ _, h => by simp [Expr.beq] at h
  | .setApply _,   .em _,          h => by simp [Expr.beq] at h
  | .setApply _,   .setPolicy _,   h => by simp [Expr.beq] at h
  | .setApply _,   .ifte _ _ _,    h => by simp [Expr.beq] at h
  | .setApply _,   .seq _,         h => by simp [Expr.beq] at h
  | .setPolicy _,  .lit _,         h => by simp [Expr.beq] at h
  | .setPolicy _,  .var _,         h => by simp [Expr.beq] at h
  | .setPolicy _,  .lam _ _,       h => by simp [Expr.beq] at h
  | .setPolicy _,  .app _ _,       h => by simp [Expr.beq] at h
  | .setPolicy _,  .appDirect _ _, h => by simp [Expr.beq] at h
  | .setPolicy _,  .em _,          h => by simp [Expr.beq] at h
  | .setPolicy _,  .setApply _,    h => by simp [Expr.beq] at h
  | .setPolicy _,  .ifte _ _ _,    h => by simp [Expr.beq] at h
  | .setPolicy _,  .seq _,         h => by simp [Expr.beq] at h
  | .ifte _ _ _,   .lit _,         h => by simp [Expr.beq] at h
  | .ifte _ _ _,   .var _,         h => by simp [Expr.beq] at h
  | .ifte _ _ _,   .lam _ _,       h => by simp [Expr.beq] at h
  | .ifte _ _ _,   .app _ _,       h => by simp [Expr.beq] at h
  | .ifte _ _ _,   .appDirect _ _, h => by simp [Expr.beq] at h
  | .ifte _ _ _,   .em _,          h => by simp [Expr.beq] at h
  | .ifte _ _ _,   .setApply _,    h => by simp [Expr.beq] at h
  | .ifte _ _ _,   .setPolicy _,   h => by simp [Expr.beq] at h
  | .ifte _ _ _,   .seq _,         h => by simp [Expr.beq] at h
  | .seq _,        .lit _,         h => by simp [Expr.beq] at h
  | .seq _,        .var _,         h => by simp [Expr.beq] at h
  | .seq _,        .lam _ _,       h => by simp [Expr.beq] at h
  | .seq _,        .app _ _,       h => by simp [Expr.beq] at h
  | .seq _,        .appDirect _ _, h => by simp [Expr.beq] at h
  | .seq _,        .em _,          h => by simp [Expr.beq] at h
  | .seq _,        .setApply _,    h => by simp [Expr.beq] at h
  | .seq _,        .setPolicy _,   h => by simp [Expr.beq] at h
  | .seq _,        .ifte _ _ _,    h => by simp [Expr.beq] at h

theorem Expr.listBeq_eq : ∀ {l1 l2 : List Expr}, Expr.listBeq l1 l2 = true → l1 = l2
  | [],        [],        _ => rfl
  | e1 :: l1', e2 :: l2', h => by
      simp [Expr.listBeq] at h
      rw [Expr.beq_eq h.1, Expr.listBeq_eq h.2]
  | [],        _ :: _,    h => by simp [Expr.listBeq] at h
  | _ :: _,    [],        h => by simp [Expr.listBeq] at h

theorem Env.beq_eq : ∀ {ρ1 ρ2 : Env}, Env.beq ρ1 ρ2 = true → ρ1 = ρ2
  | .nil,          .nil,            _ => rfl
  | .cons x v ρ,   .cons y w ρ',    h => by
      simp [Env.beq] at h
      rw [h.1.1, Val.beq_eq h.1.2, Env.beq_eq h.2]
  | .nil,          .cons _ _ _,     h => by simp [Env.beq] at h
  | .cons _ _ _,   .nil,            h => by simp [Env.beq] at h

end

/-! ## CE of bbApply

`bbApply` trivially CE-extends itself: every `applyDirect bbApply
[op, .list args]` is its own witness. -/

theorem CE_bbApply (L : Nat) : CE L .bbApply := by
  intro fuel op args T r T_post h
  exact ⟨fuel, r, T_post, h, rfl, rfl⟩

/-! ## The substrate invariant

For every level `L`, the dispatcher cell consulted by level-`L` calls
(at tower index `L+1`) is CE-related to `bbApply` at caller level `L`.

Index 0 is irrelevant — no `setApply` writes there (writes go to
`L+1` for `L ≥ 0`), and no dispatch reads it. We leave it
unconstrained. -/

def TowerState.CEInvariant (T : TowerState) : Prop :=
  ∀ (L : Nat) (lvl : Level), T[L + 1]? = some lvl → CE L lvl.apply

/-! ## Initial tower satisfies the invariant -/

theorem initTower_CEInvariant : initTower.CEInvariant := by
  intro L lvl h
  -- initTower = [{ apply := .bbApply, policy := .bool true }]
  -- only index 0 is populated, so T[L+1]? = none for any L
  simp [initTower] at h

/-! ## Default level satisfies the invariant pointwise -/

theorem defaultLevel_CE (L : Nat) : CE L defaultLevel.apply := by
  show CE L .bbApply
  exact CE_bbApply L

/-! ## Materialization preserves the invariant

Materialize appends `defaultLevel` cells. Each new cell's apply is
`bbApply`, which is CE-related at every level. So the invariant is
preserved. -/

theorem materialize_CEInvariant (T : TowerState) (k : Nat) :
    T.CEInvariant → (T.materialize k).CEInvariant := by
  intro hT L lvl hLook
  unfold TowerState.materialize at hLook
  split at hLook
  · exact hT L lvl hLook
  · by_cases hL : L + 1 < T.length
    · rw [List.getElem?_append_left hL] at hLook
      exact hT L lvl hLook
    · have hL' : T.length ≤ L + 1 := Nat.le_of_not_lt hL
      rw [List.getElem?_append_right hL'] at hLook
      have : lvl = defaultLevel := by
        have := List.getElem?_eq_some_iff.mp hLook
        obtain ⟨_, h2⟩ := this
        rw [List.getElem_replicate] at h2
        exact h2.symm
      rw [this]
      exact defaultLevel_CE L

/-! ## setApplyAt preserves the invariant

If `T` is invariant and the new value `v` is CE-related at level
`L`, writing it to index `L+1` preserves the invariant. -/

theorem setApplyAt_CEInvariant (T : TowerState) (L : Nat) (v : Val)
    (hT : T.CEInvariant) (hv : CE L v) :
    (T.setApplyAt (L + 1) v).CEInvariant := by
  intro L' lvl hLook
  unfold TowerState.setApplyAt at hLook
  have hMat := materialize_CEInvariant T (L + 1) hT
  have hMatLen : L + 1 < (T.materialize (L + 1)).length := by
    unfold TowerState.materialize
    split
    · assumption
    · simp; omega
  rw [List.getElem?_set] at hLook
  by_cases heq : L + 1 = L' + 1
  · rw [if_pos heq, if_pos hMatLen] at hLook
    have hL : L = L' := by omega
    simp at hLook
    rw [← hLook]
    show CE L' v
    rw [← hL]; exact hv
  · rw [if_neg heq] at hLook
    exact hMat L' lvl hLook

/-! ## setPolicyAt preserves the invariant

`setPolicyAt` only writes the `policy` field, leaving `apply`
untouched. The invariant is on `apply` fields, so it's preserved. -/

theorem setPolicyAt_CEInvariant (T : TowerState) (k : Nat) (v : Val)
    (hT : T.CEInvariant) :
    (T.setPolicyAt k v).CEInvariant := by
  intro L' lvl hLook
  unfold TowerState.setPolicyAt at hLook
  have hMat := materialize_CEInvariant T k hT
  have hMatLen : k < (T.materialize k).length := by
    unfold TowerState.materialize
    split
    · assumption
    · simp; omega
  rw [List.getElem?_set] at hLook
  by_cases heq : k = L' + 1
  · -- Same index: apply field unchanged
    rw [if_pos heq, if_pos hMatLen] at hLook
    simp at hLook
    rw [← hLook]
    -- Goal: CE L' (old.apply) where old = (T.materialize k)[k]?.getD defaultLevel
    show CE L' ((T.materialize k)[k]?.getD defaultLevel).apply
    cases hMatLook : (T.materialize k)[k]? with
    | none =>
      simp
      exact defaultLevel_CE L'
    | some oldLvl =>
      simp
      have hMatLook' : (T.materialize k)[L' + 1]? = some oldLvl := by
        rw [← heq]; exact hMatLook
      exact hMat L' oldLvl hMatLook'
  · -- Different index: cell unchanged
    rw [if_neg heq] at hLook
    exact hMat L' lvl hLook

/-! ## The gate's true verdict yields a CE witness

When `mkGate approvals L oldVal newVal = true`, some approval's
`(callerLevel, new)` matches `(L, newVal)` structurally. Since
approvals carry `CE callerLevel new` proofs in their `proof` field,
we extract `CE L newVal` by rewriting along the matching equalities. -/

theorem mkGate_admits_CE
    (approvals : List ApprovedModification) (L : Nat)
    (oldVal newVal : Val) :
    mkGate approvals L oldVal newVal = true → CE L newVal := by
  intro h
  unfold mkGate at h
  rw [List.any_eq_true] at h
  obtain ⟨am, _, hmatch⟩ := h
  unfold ApprovedModification.matches at hmatch
  simp at hmatch
  obtain ⟨hL, hNew⟩ := hmatch
  have := am.proof
  rw [hL] at this
  rw [Val.beq_eq hNew] at this
  exact this

/-! ## Joint preservation of the substrate invariant

Define the five-conjunct claim, then prove by induction on fuel. -/

def EvalInv (approvals : List ApprovedModification) (n : Nat) : Prop :=
  ∀ (e : Expr) (ρ : Env) (L : Nat) (T : TowerState)
    (r : Val) (T' : TowerState),
    T.CEInvariant →
    eval (mkGate approvals) n e ρ L T = some (r, T') → T'.CEInvariant

def EvalListInv (approvals : List ApprovedModification) (n : Nat) : Prop :=
  ∀ (es : List Expr) (ρ : Env) (L : Nat) (T : TowerState)
    (vs : List Val) (T' : TowerState),
    T.CEInvariant →
    evalList (mkGate approvals) n es ρ L T = some (vs, T') → T'.CEInvariant

def EvalSeqInv (approvals : List ApprovedModification) (n : Nat) : Prop :=
  ∀ (es : List Expr) (ρ : Env) (L : Nat) (T : TowerState)
    (r : Val) (T' : TowerState),
    T.CEInvariant →
    evalSeq (mkGate approvals) n es ρ L T = some (r, T') → T'.CEInvariant

def ApplyViaInv (approvals : List ApprovedModification) (n : Nat) : Prop :=
  ∀ (dL : Nat) (op : Val) (args : List Val) (T : TowerState)
    (r : Val) (T' : TowerState),
    T.CEInvariant →
    applyVia (mkGate approvals) n dL op args T = some (r, T') → T'.CEInvariant

def ApplyDirectInv (approvals : List ApprovedModification) (n : Nat) : Prop :=
  ∀ (op : Val) (args : List Val) (L : Nat) (T : TowerState)
    (r : Val) (T' : TowerState),
    T.CEInvariant →
    applyDirect (mkGate approvals) n op args L T = some (r, T') → T'.CEInvariant

def JointInv (approvals : List ApprovedModification) (n : Nat) : Prop :=
  EvalInv approvals n ∧ EvalListInv approvals n ∧ EvalSeqInv approvals n
  ∧ ApplyViaInv approvals n ∧ ApplyDirectInv approvals n

theorem jointInv (approvals : List ApprovedModification) :
    ∀ n, JointInv approvals n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold EvalInv;       intro _ _ _ _ _ _ _ h; simp [eval] at h
    · unfold EvalListInv;   intro _ _ _ _ _ _ _ h; simp [evalList] at h
    · unfold EvalSeqInv;    intro _ _ _ _ _ _ _ h; simp [evalSeq] at h
    · unfold ApplyViaInv;   intro _ _ _ _ _ _ _ h; simp [applyVia] at h
    · unfold ApplyDirectInv; intro _ _ _ _ _ _ _ h; simp [applyDirect] at h
  | succ n ih =>
    obtain ⟨ihE, ihL, ihS, ihV, ihD⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    -- EvalInv at n+1
    · unfold EvalInv
      intro e ρ L T r T' hT h
      cases e with
      | lit v =>
        simp [eval] at h; obtain ⟨_, hT'⟩ := h; exact hT' ▸ hT
      | var x =>
        simp [eval] at h
        cases hl : ρ.lookup x with
        | none => rw [hl] at h; simp at h
        | some v =>
          rw [hl] at h; simp at h
          obtain ⟨_, hT'⟩ := h; exact hT' ▸ hT
      | lam xs body =>
        simp [eval] at h; obtain ⟨_, hT'⟩ := h; exact hT' ▸ hT
      | app f args =>
        simp [eval] at h
        cases h1 : eval (mkGate approvals) n f ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vf, T₁⟩ := pr; rw [h1] at h; simp at h
          have hT₁ := ihE f ρ L T vf T₁ hT h1
          cases h2 : evalList (mkGate approvals) n args ρ L T₁ with
          | none => rw [h2] at h; simp at h
          | some pr2 =>
            obtain ⟨vs, T₂⟩ := pr2; rw [h2] at h; simp at h
            have hT₂ := ihL args ρ L T₁ vs T₂ hT₁ h2
            exact ihV (L + 1) vf vs T₂ r T' hT₂ h
      | appDirect f args =>
        simp [eval] at h
        cases h1 : eval (mkGate approvals) n f ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vf, T₁⟩ := pr; rw [h1] at h; simp at h
          have hT₁ := ihE f ρ L T vf T₁ hT h1
          cases h2 : evalList (mkGate approvals) n args ρ L T₁ with
          | none => rw [h2] at h; simp at h
          | some pr2 =>
            obtain ⟨vs, T₂⟩ := pr2; rw [h2] at h; simp at h
            have hT₂ := ihL args ρ L T₁ vs T₂ hT₁ h2
            exact ihD vf vs L T₂ r T' hT₂ h
      | em e' =>
        simp [eval] at h
        have hMat := materialize_CEInvariant T (L + 1) hT
        exact ihE e' ρ (L + 1) (T.materialize (L + 1)) r T' hMat h
      | setApply e' =>
        simp [eval] at h
        cases h1 : eval (mkGate approvals) n e' ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vNew, T₁⟩ := pr; rw [h1] at h; simp at h
          have hT₁ := ihE e' ρ L T vNew T₁ hT h1
          split at h
          · rename_i hGate
            simp at h
            obtain ⟨_, hT'⟩ := h
            rw [← hT']
            have hCE := mkGate_admits_CE approvals L (T₁.applyAt (L + 1)) vNew hGate
            exact setApplyAt_CEInvariant T₁ L vNew hT₁ hCE
          · simp at h
            obtain ⟨_, hT'⟩ := h; exact hT' ▸ hT₁
      | setPolicy e' =>
        simp [eval] at h
        cases h1 : eval (mkGate approvals) n e' ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vNew, T₁⟩ := pr; rw [h1] at h; simp at h
          have hT₁ := ihE e' ρ L T vNew T₁ hT h1
          split at h
          · simp at h
            obtain ⟨_, hT'⟩ := h
            rw [← hT']
            exact setPolicyAt_CEInvariant T₁ (L + 1) vNew hT₁
          · simp at h
            obtain ⟨_, hT'⟩ := h; exact hT' ▸ hT₁
      | ifte c t e =>
        simp [eval] at h
        cases h1 : eval (mkGate approvals) n c ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vc, T₁⟩ := pr; rw [h1] at h; simp at h
          have hT₁ := ihE c ρ L T vc T₁ hT h1
          cases vc with
          | bool b =>
            cases b with
            | false => simp at h; exact ihE e ρ L T₁ r T' hT₁ h
            | true => simp at h; exact ihE t ρ L T₁ r T' hT₁ h
          | num _ => simp at h
          | prim _ => simp at h
          | bbApply => simp at h
          | clos _ _ _ => simp at h
          | list _ => simp at h
      | seq es =>
        simp [eval] at h
        exact ihS es ρ L T r T' hT h
    -- EvalListInv at n+1
    · unfold EvalListInv
      intro es ρ L T vs T' hT h
      cases es with
      | nil =>
        simp [evalList] at h; obtain ⟨_, hT'⟩ := h; exact hT' ▸ hT
      | cons e es =>
        simp [evalList] at h
        cases h1 : eval (mkGate approvals) n e ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨v, T₁⟩ := pr; rw [h1] at h; simp at h
          have hT₁ := ihE e ρ L T v T₁ hT h1
          cases h2 : evalList (mkGate approvals) n es ρ L T₁ with
          | none => rw [h2] at h; simp at h
          | some pr2 =>
            obtain ⟨vs', T₂⟩ := pr2; rw [h2] at h; simp at h
            obtain ⟨_, hT'⟩ := h
            rw [← hT']
            exact ihL es ρ L T₁ vs' T₂ hT₁ h2
    -- EvalSeqInv at n+1
    · unfold EvalSeqInv
      intro es ρ L T r T' hT h
      cases es with
      | nil =>
        simp [evalSeq] at h; obtain ⟨_, hT'⟩ := h; exact hT' ▸ hT
      | cons e es =>
        cases es with
        | nil =>
          simp [evalSeq] at h
          exact ihE e ρ L T r T' hT h
        | cons e' es' =>
          simp [evalSeq] at h
          cases h1 : eval (mkGate approvals) n e ρ L T with
          | none => rw [h1] at h; simp at h
          | some pr =>
            obtain ⟨v, T₁⟩ := pr; rw [h1] at h; simp at h
            have hT₁ := ihE e ρ L T v T₁ hT h1
            exact ihS (e' :: es') ρ L T₁ r T' hT₁ h
    -- ApplyViaInv at n+1
    · unfold ApplyViaInv
      intro dL op args T r T' hT h
      simp only [applyVia] at h
      have hTmat := materialize_CEInvariant T dL hT
      generalize hd : (T.materialize dL).applyAt dL = disp at h
      cases disp with
      | bbApply => exact ihD op args (dL - 1) (T.materialize dL) r T' hTmat h
      | num k => exact ihD (.num k) [op, .list args] (dL - 1) (T.materialize dL) r T' hTmat h
      | bool b => exact ihD (.bool b) [op, .list args] (dL - 1) (T.materialize dL) r T' hTmat h
      | prim p => exact ihD (.prim p) [op, .list args] (dL - 1) (T.materialize dL) r T' hTmat h
      | clos xs body env_c =>
        exact ihD (.clos xs body env_c) [op, .list args] (dL - 1) (T.materialize dL) r T' hTmat h
      | list vs => exact ihD (.list vs) [op, .list args] (dL - 1) (T.materialize dL) r T' hTmat h
    -- ApplyDirectInv at n+1
    · unfold ApplyDirectInv
      intro op args L T r T' hT h
      cases op with
      | num _ => simp [applyDirect] at h
      | bool _ => simp [applyDirect] at h
      | list _ => simp [applyDirect] at h
      | prim p =>
        simp [applyDirect] at h
        cases hp : applyPrim p args with
        | none => rw [hp] at h; simp at h
        | some v =>
          rw [hp] at h; simp at h
          obtain ⟨_, hT'⟩ := h; exact hT' ▸ hT
      | clos xs body env_c =>
        simp [applyDirect] at h
        cases hext : env_c.extend xs args with
        | none => rw [hext] at h; simp at h
        | some ρ' =>
          rw [hext] at h; simp at h
          exact ihE body ρ' L T r T' hT h
      | bbApply =>
        cases args with
        | nil => simp [applyDirect] at h
        | cons a tl =>
          cases tl with
          | nil => simp [applyDirect] at h
          | cons b tt =>
            cases tt with
            | nil =>
              cases b with
              | list args' =>
                simp [applyDirect] at h
                exact ihD a args' L T r T' hT h
              | num _ => simp [applyDirect] at h
              | bool _ => simp [applyDirect] at h
              | prim _ => simp [applyDirect] at h
              | bbApply => simp [applyDirect] at h
              | clos _ _ _ => simp [applyDirect] at h
            | cons _ _ => simp [applyDirect] at h

/-! ## Headline corollary: the substrate is always CE

For any program executed under a proof-bearing gate from an
invariant-holding tower (e.g., `initTower`), the resulting tower
state satisfies the CE invariant. -/

theorem eval_preserves_CEInvariant
    (approvals : List ApprovedModification)
    (n : Nat) (e : Expr) (ρ : Env) (L : Nat) (T : TowerState)
    (r : Val) (T' : TowerState)
    (hT : T.CEInvariant)
    (h : eval (mkGate approvals) n e ρ L T = some (r, T')) :
    T'.CEInvariant :=
  (jointInv approvals n).1 e ρ L T r T' hT h

/-- Specialization to `initTower`: every reachable state is CE-invariant. -/
theorem evalProgram_reaches_CEInvariant
    (approvals : List ApprovedModification)
    (n : Nat) (e : Expr) (r : Val) (T' : TowerState)
    (h : eval (mkGate approvals) n e initEnv 0 initTower = some (r, T')) :
    T'.CEInvariant :=
  eval_preserves_CEInvariant approvals n e initEnv 0 initTower r T'
    initTower_CEInvariant h

end LeanEmerald

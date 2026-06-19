import LeanEmerald.SubstrateBehavior

/-!
# Full eval-level substrate behavioral CE (Theorem 2 full)

For pure-of-effects programs evaluated on an `AllBbApply` baseline tower
and a `CEInvariant` substrate tower, the substrate evaluation succeeds
with the same value as the baseline:

> `eval acceptAll n e ρ L T_base = some (r, _) →`
> `∃ fuel' T', eval (mkGate approvals) fuel' e ρ L T_subst = some (r, T')`

This is the *eval-level* substrate behavioral CE — the lift of
`applyVia_substrate_extends_baseline` (the dispatch-level claim in
`SubstrateBehavior.lean`) up to the full evaluator.

## Proof technique — 5-conjunct joint induction with fuel monotonicity

The joint induction compares two evaluations side-by-side under the
same gate `mkGate approvals`:

* `T_base`: `AllBbApply` (every populated cell has `apply = .bbApply`).
* `T_subst`: `CEInvariant` (every populated cell at index `≥ 1` is
  CE-related to `bbApply` at the level below).

For pure-of-effects programs the gate is dead code, so the choice of
`(mkGate approvals)` over `acceptAll` doesn't matter; using `mkGate`
lets us reuse `jointInv` for substrate CEInvariant preservation
directly. The headline corollary swaps the baseline's `acceptAll` to
`mkGate approvals` via `eval_pure_gate_indep`.

### Fuel handling

The `CE` primitive introduces an existential fuel on the substrate's
wrapper invocation. To compose IHs that hand back different sub-fuels
(the three sub-evaluations of `.app`), we pre-prove fuel monotonicity
(joint induction on fuel) and take the max of IH-supplied sub-fuels in
each step.

### The bridge at `.app`'s wrapper case

When the substrate's dispatcher at the call site is not `.bbApply`:
1. IH on `applyDirect` gives substrate's `bbApply`-form trace on the
   substrate tower (via the IH's substrate result).
2. Convert from `mkGate`-form to `acceptAll`-form via
   `applyDirect_pure_gate_indep` (pure operand, args, tower).
3. Pack into wrapper-invocation form (`applyDirect _ .bbApply [op, .list args]`)
   via the bbApply unpack rule.
4. Apply the per-cell `CE` witness (from `CEInvariant_applyAt_CE`).
5. Convert back from `acceptAll`-form to `mkGate`-form.
-/

namespace LeanEmerald

/-! ## AllBbApply tower invariant

A baseline-style tower: every populated cell's `apply` field is the
default `.bbApply`. The initial tower satisfies this, and so does any
materialization (which only appends default cells). During pure-of-effects
execution no `.setApply` succeeds, so the invariant is preserved. -/

def TowerState.AllBbApply (T : TowerState) : Prop :=
  ∀ (k : Nat) (lvl : Level), T[k]? = some lvl → lvl.apply = .bbApply

theorem defaultLevel_AllBbApply_apply : defaultLevel.apply = .bbApply := rfl

theorem initTower_AllBbApply : initTower.AllBbApply := by
  intro k lvl h
  unfold initTower at h
  cases k with
  | zero => simp at h; rw [← h]
  | succ _ => simp at h

theorem TowerState.materialize_AllBbApply (T : TowerState) (k : Nat)
    (hT : T.AllBbApply) : (T.materialize k).AllBbApply := by
  intro idx lvl h
  unfold TowerState.materialize at h
  split at h
  · exact hT idx lvl h
  · by_cases hidx : idx < T.length
    · rw [List.getElem?_append_left hidx] at h
      exact hT idx lvl h
    · have hidx' : T.length ≤ idx := Nat.le_of_not_lt hidx
      rw [List.getElem?_append_right hidx'] at h
      have hsome := List.getElem?_eq_some_iff.mp h
      obtain ⟨_, hget⟩ := hsome
      rw [List.getElem_replicate] at hget
      rw [← hget]
      exact defaultLevel_AllBbApply_apply

/-- An `AllBbApply` tower's `applyAt` always yields `.bbApply`. -/
theorem TowerState.AllBbApply.applyAt (T : TowerState)
    (hT : T.AllBbApply) (k : Nat) : T.applyAt k = .bbApply := by
  unfold TowerState.applyAt
  split
  case h_1 _ lvl heq => exact hT k lvl heq
  case h_2 => rfl

/-! ## Fuel monotonicity

A standard property: success at fuel `n` implies success at fuel `n+1`
(and thus, by iteration, at any `m ≥ n`). Required because the `CE`
primitive's existential fuel forces us to compose IHs at different
sub-fuels in the main joint induction. Joint induction across the five
mutually-recursive functions. -/

def EvalFuelMono (n : Nat) : Prop :=
  ∀ (G : Gate) (e : Expr) (ρ : Env) (L : Nat) (T : TowerState)
    (r : Val) (T' : TowerState),
    eval G n e ρ L T = some (r, T') →
    eval G (n + 1) e ρ L T = some (r, T')

def EvalListFuelMono (n : Nat) : Prop :=
  ∀ (G : Gate) (es : List Expr) (ρ : Env) (L : Nat) (T : TowerState)
    (vs : List Val) (T' : TowerState),
    evalList G n es ρ L T = some (vs, T') →
    evalList G (n + 1) es ρ L T = some (vs, T')

def EvalSeqFuelMono (n : Nat) : Prop :=
  ∀ (G : Gate) (es : List Expr) (ρ : Env) (L : Nat) (T : TowerState)
    (r : Val) (T' : TowerState),
    evalSeq G n es ρ L T = some (r, T') →
    evalSeq G (n + 1) es ρ L T = some (r, T')

def ApplyViaFuelMono (n : Nat) : Prop :=
  ∀ (G : Gate) (dL : Nat) (op : Val) (args : List Val) (T : TowerState)
    (r : Val) (T' : TowerState),
    applyVia G n dL op args T = some (r, T') →
    applyVia G (n + 1) dL op args T = some (r, T')

def ApplyDirectFuelMono (n : Nat) : Prop :=
  ∀ (G : Gate) (op : Val) (args : List Val) (L : Nat) (T : TowerState)
    (r : Val) (T' : TowerState),
    applyDirect G n op args L T = some (r, T') →
    applyDirect G (n + 1) op args L T = some (r, T')

def JointFuelMono (n : Nat) : Prop :=
  EvalFuelMono n ∧ EvalListFuelMono n ∧ EvalSeqFuelMono n ∧
  ApplyViaFuelMono n ∧ ApplyDirectFuelMono n

theorem jointFuelMono : ∀ n, JointFuelMono n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold EvalFuelMono;        intro _ _ _ _ _ _ _ h;     simp [eval]       at h
    · unfold EvalListFuelMono;    intro _ _ _ _ _ _ _ h;     simp [evalList]   at h
    · unfold EvalSeqFuelMono;     intro _ _ _ _ _ _ _ h;     simp [evalSeq]    at h
    · unfold ApplyViaFuelMono;    intro _ _ _ _ _ _ _ h;     simp [applyVia]   at h
    · unfold ApplyDirectFuelMono; intro _ _ _ _ _ _ _ h;     simp [applyDirect] at h
  | succ n ih =>
    obtain ⟨ihE, ihL, ihS, ihV, ihD⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    -- EvalFuelMono at n+1
    · unfold EvalFuelMono
      intro G e ρ L T r T' h
      cases e with
      | lit v => simp [eval] at h ⊢; exact h
      | var x => simp [eval] at h ⊢; exact h
      | lam xs body => simp [eval] at h ⊢; exact h
      | app f args =>
        simp only [eval] at h ⊢
        cases h1 : eval G n f ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vf, T₁⟩ := pr
          rw [h1] at h; simp at h
          cases h2 : evalList G n args ρ L T₁ with
          | none => rw [h2] at h; simp at h
          | some pr2 =>
            obtain ⟨vs, T₂⟩ := pr2
            rw [h2] at h; simp at h
            rw [ihE G f ρ L T vf T₁ h1]; simp
            rw [ihL G args ρ L T₁ vs T₂ h2]; simp
            exact ihV G (L+1) vf vs T₂ r T' h
      | appDirect f args =>
        simp only [eval] at h ⊢
        cases h1 : eval G n f ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vf, T₁⟩ := pr
          rw [h1] at h; simp at h
          cases h2 : evalList G n args ρ L T₁ with
          | none => rw [h2] at h; simp at h
          | some pr2 =>
            obtain ⟨vs, T₂⟩ := pr2
            rw [h2] at h; simp at h
            rw [ihE G f ρ L T vf T₁ h1]; simp
            rw [ihL G args ρ L T₁ vs T₂ h2]; simp
            exact ihD G vf vs L T₂ r T' h
      | em e' =>
        simp only [eval] at h ⊢
        exact ihE G e' ρ (L+1) (T.materialize (L+1)) r T' h
      | setApply e' =>
        simp only [eval] at h ⊢
        cases h1 : eval G n e' ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vNew, T₁⟩ := pr
          rw [h1] at h; simp at h
          rw [ihE G e' ρ L T vNew T₁ h1]; simp
          exact h
      | setPolicy e' =>
        simp only [eval] at h ⊢
        cases h1 : eval G n e' ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vNew, T₁⟩ := pr
          rw [h1] at h; simp at h
          rw [ihE G e' ρ L T vNew T₁ h1]; simp
          exact h
      | ifte c t e =>
        simp only [eval] at h ⊢
        cases h1 : eval G n c ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vc, T₁⟩ := pr
          rw [h1] at h; simp at h
          rw [ihE G c ρ L T vc T₁ h1]; simp
          cases vc with
          | bool b => cases b with
                      | true => simp at h ⊢; exact ihE G t ρ L T₁ r T' h
                      | false => simp at h ⊢; exact ihE G e ρ L T₁ r T' h
          | num _ => simp at h
          | prim _ => simp at h
          | bbApply => simp at h
          | clos _ _ _ => simp at h
          | list _ => simp at h
      | seq es =>
        simp only [eval] at h ⊢
        exact ihS G es ρ L T r T' h
    -- EvalListFuelMono at n+1
    · unfold EvalListFuelMono
      intro G es ρ L T vs T' h
      cases es with
      | nil => simp [evalList] at h ⊢; exact h
      | cons e es =>
        simp only [evalList] at h ⊢
        cases h1 : eval G n e ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨v, T₁⟩ := pr
          rw [h1] at h; simp at h
          cases h2 : evalList G n es ρ L T₁ with
          | none => rw [h2] at h; simp at h
          | some pr2 =>
            obtain ⟨vs', T₂⟩ := pr2
            rw [h2] at h; simp at h
            rw [ihE G e ρ L T v T₁ h1]; simp
            rw [ihL G es ρ L T₁ vs' T₂ h2]; simp
            exact h
    -- EvalSeqFuelMono at n+1
    · unfold EvalSeqFuelMono
      intro G es ρ L T r T' h
      cases es with
      | nil => simp [evalSeq] at h ⊢; exact h
      | cons e es =>
        cases es with
        | nil =>
          simp only [evalSeq] at h ⊢
          exact ihE G e ρ L T r T' h
        | cons e' es' =>
          simp only [evalSeq] at h ⊢
          cases h1 : eval G n e ρ L T with
          | none => rw [h1] at h; simp at h
          | some pr =>
            obtain ⟨v, T₁⟩ := pr
            rw [h1] at h; simp at h
            rw [ihE G e ρ L T v T₁ h1]; simp
            exact ihS G (e' :: es') ρ L T₁ r T' h
    -- ApplyViaFuelMono at n+1
    · unfold ApplyViaFuelMono
      intro G dL op args T r T' h
      simp only [applyVia] at h ⊢
      generalize hd : (T.materialize dL).applyAt dL = disp at h ⊢
      cases disp with
      | bbApply => exact ihD G op args (dL-1) (T.materialize dL) r T' h
      | num k => exact ihD G (.num k) [op, .list args] (dL-1) (T.materialize dL) r T' h
      | bool b => exact ihD G (.bool b) [op, .list args] (dL-1) (T.materialize dL) r T' h
      | prim p => exact ihD G (.prim p) [op, .list args] (dL-1) (T.materialize dL) r T' h
      | clos xs body env_c =>
        exact ihD G (.clos xs body env_c) [op, .list args] (dL-1) (T.materialize dL) r T' h
      | list vs => exact ihD G (.list vs) [op, .list args] (dL-1) (T.materialize dL) r T' h
    -- ApplyDirectFuelMono at n+1
    · unfold ApplyDirectFuelMono
      intro G op args L T r T' h
      cases op with
      | num _ => simp [applyDirect] at h
      | bool _ => simp [applyDirect] at h
      | list _ => simp [applyDirect] at h
      | prim p =>
        simp only [applyDirect] at h ⊢
        exact h
      | clos xs body env_c =>
        simp only [applyDirect] at h ⊢
        cases hext : env_c.extend xs args with
        | none => rw [hext] at h; simp at h
        | some ρ' =>
          rw [hext] at h; simp at h
          exact ihE G body ρ' L T r T' h
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
                simp only [applyDirect] at h ⊢
                exact ihD G a args' L T r T' h
              | num _ => simp [applyDirect] at h
              | bool _ => simp [applyDirect] at h
              | prim _ => simp [applyDirect] at h
              | bbApply => simp [applyDirect] at h
              | clos _ _ _ => simp [applyDirect] at h
            | cons _ _ => simp [applyDirect] at h

/-- Derived: success at fuel `n` implies success at any fuel `n + m`. -/
theorem eval_fuel_add (G : Gate) (n : Nat) (e : Expr) (ρ : Env)
    (L : Nat) (T : TowerState) (r : Val) (T' : TowerState)
    (h : eval G n e ρ L T = some (r, T')) (m : Nat) :
    eval G (n + m) e ρ L T = some (r, T') := by
  induction m with
  | zero => exact h
  | succ m ih => exact (jointFuelMono (n + m)).1 G e ρ L T r T' ih

theorem evalList_fuel_add (G : Gate) (n : Nat) (es : List Expr) (ρ : Env)
    (L : Nat) (T : TowerState) (vs : List Val) (T' : TowerState)
    (h : evalList G n es ρ L T = some (vs, T')) (m : Nat) :
    evalList G (n + m) es ρ L T = some (vs, T') := by
  induction m with
  | zero => exact h
  | succ m ih => exact (jointFuelMono (n + m)).2.1 G es ρ L T vs T' ih

theorem evalSeq_fuel_add (G : Gate) (n : Nat) (es : List Expr) (ρ : Env)
    (L : Nat) (T : TowerState) (r : Val) (T' : TowerState)
    (h : evalSeq G n es ρ L T = some (r, T')) (m : Nat) :
    evalSeq G (n + m) es ρ L T = some (r, T') := by
  induction m with
  | zero => exact h
  | succ m ih => exact (jointFuelMono (n + m)).2.2.1 G es ρ L T r T' ih

theorem applyVia_fuel_add (G : Gate) (n : Nat) (dL : Nat) (op : Val)
    (args : List Val) (T : TowerState) (r : Val) (T' : TowerState)
    (h : applyVia G n dL op args T = some (r, T')) (m : Nat) :
    applyVia G (n + m) dL op args T = some (r, T') := by
  induction m with
  | zero => exact h
  | succ m ih => exact (jointFuelMono (n + m)).2.2.2.1 G dL op args T r T' ih

theorem applyDirect_fuel_add (G : Gate) (n : Nat) (op : Val) (args : List Val)
    (L : Nat) (T : TowerState) (r : Val) (T' : TowerState)
    (h : applyDirect G n op args L T = some (r, T')) (m : Nat) :
    applyDirect G (n + m) op args L T = some (r, T') := by
  induction m with
  | zero => exact h
  | succ m ih => exact (jointFuelMono (n + m)).2.2.2.2 G op args L T r T' ih

/-- `≤`-form of fuel monotonicity for `eval`. -/
theorem eval_fuel_le (G : Gate) (n m : Nat) (e : Expr) (ρ : Env)
    (L : Nat) (T : TowerState) (r : Val) (T' : TowerState)
    (hle : n ≤ m)
    (h : eval G n e ρ L T = some (r, T')) :
    eval G m e ρ L T = some (r, T') := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  exact eval_fuel_add G n e ρ L T r T' h k

theorem evalList_fuel_le (G : Gate) (n m : Nat) (es : List Expr) (ρ : Env)
    (L : Nat) (T : TowerState) (vs : List Val) (T' : TowerState)
    (hle : n ≤ m)
    (h : evalList G n es ρ L T = some (vs, T')) :
    evalList G m es ρ L T = some (vs, T') := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  exact evalList_fuel_add G n es ρ L T vs T' h k

theorem evalSeq_fuel_le (G : Gate) (n m : Nat) (es : List Expr) (ρ : Env)
    (L : Nat) (T : TowerState) (r : Val) (T' : TowerState)
    (hle : n ≤ m)
    (h : evalSeq G n es ρ L T = some (r, T')) :
    evalSeq G m es ρ L T = some (r, T') := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  exact evalSeq_fuel_add G n es ρ L T r T' h k

theorem applyVia_fuel_le (G : Gate) (n m : Nat) (dL : Nat) (op : Val)
    (args : List Val) (T : TowerState) (r : Val) (T' : TowerState)
    (hle : n ≤ m)
    (h : applyVia G n dL op args T = some (r, T')) :
    applyVia G m dL op args T = some (r, T') := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  exact applyVia_fuel_add G n dL op args T r T' h k

theorem applyDirect_fuel_le (G : Gate) (n m : Nat) (op : Val) (args : List Val)
    (L : Nat) (T : TowerState) (r : Val) (T' : TowerState)
    (hle : n ≤ m)
    (h : applyDirect G n op args L T = some (r, T')) :
    applyDirect G m op args L T = some (r, T') := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  exact applyDirect_fuel_add G n op args L T r T' h k

/-! ## Joint cross-tower behavioral CE

A 5-conjunct joint induction. Each conjunct says: under pure preconditions,
a baseline trace on an `AllBbApply` tower implies a substrate trace on a
`CEInvariant` tower with the same final value `r`. Preservation
(`AllBbApply`, `Pure`, `CEInvariant`) is threaded so the IH composes
across sub-evaluations. -/

def EvalCEBeh (approvals : List ApprovedModification) (n : Nat) : Prop :=
  ∀ (e : Expr) (ρ : Env) (L : Nat)
    (T_base T_subst : TowerState) (r : Val) (T_base' : TowerState),
    e.Pure = true → ρ.Pure = true →
    T_base.AllBbApply → T_base.Pure = true →
    T_subst.CEInvariant → T_subst.Pure = true →
    eval (mkGate approvals) n e ρ L T_base = some (r, T_base') →
    r.Pure = true ∧ T_base'.AllBbApply ∧ T_base'.Pure = true ∧
    ∃ fuel' T_subst',
      eval (mkGate approvals) fuel' e ρ L T_subst = some (r, T_subst') ∧
      T_subst'.CEInvariant ∧ T_subst'.Pure = true

def EvalListCEBeh (approvals : List ApprovedModification) (n : Nat) : Prop :=
  ∀ (es : List Expr) (ρ : Env) (L : Nat)
    (T_base T_subst : TowerState) (vs : List Val) (T_base' : TowerState),
    ExprList.Pure es = true → ρ.Pure = true →
    T_base.AllBbApply → T_base.Pure = true →
    T_subst.CEInvariant → T_subst.Pure = true →
    evalList (mkGate approvals) n es ρ L T_base = some (vs, T_base') →
    ValList.Pure vs = true ∧ T_base'.AllBbApply ∧ T_base'.Pure = true ∧
    ∃ fuel' T_subst',
      evalList (mkGate approvals) fuel' es ρ L T_subst = some (vs, T_subst') ∧
      T_subst'.CEInvariant ∧ T_subst'.Pure = true

def EvalSeqCEBeh (approvals : List ApprovedModification) (n : Nat) : Prop :=
  ∀ (es : List Expr) (ρ : Env) (L : Nat)
    (T_base T_subst : TowerState) (r : Val) (T_base' : TowerState),
    ExprList.Pure es = true → ρ.Pure = true →
    T_base.AllBbApply → T_base.Pure = true →
    T_subst.CEInvariant → T_subst.Pure = true →
    evalSeq (mkGate approvals) n es ρ L T_base = some (r, T_base') →
    r.Pure = true ∧ T_base'.AllBbApply ∧ T_base'.Pure = true ∧
    ∃ fuel' T_subst',
      evalSeq (mkGate approvals) fuel' es ρ L T_subst = some (r, T_subst') ∧
      T_subst'.CEInvariant ∧ T_subst'.Pure = true

/-- Restricted to `dL ≥ 1` because `CEInvariant` says nothing about
    index 0 of the tower; the only invocation site (`.app`) always
    uses `dL = L + 1 ≥ 1`. -/
def ApplyViaCEBeh (approvals : List ApprovedModification) (n : Nat) : Prop :=
  ∀ (dL : Nat) (op : Val) (args : List Val)
    (T_base T_subst : TowerState) (r : Val) (T_base' : TowerState),
    op.Pure = true → ValList.Pure args = true →
    T_base.AllBbApply → T_base.Pure = true →
    T_subst.CEInvariant → T_subst.Pure = true →
    dL ≥ 1 →
    applyVia (mkGate approvals) n dL op args T_base = some (r, T_base') →
    r.Pure = true ∧ T_base'.AllBbApply ∧ T_base'.Pure = true ∧
    ∃ fuel' T_subst',
      applyVia (mkGate approvals) fuel' dL op args T_subst = some (r, T_subst') ∧
      T_subst'.CEInvariant ∧ T_subst'.Pure = true

def ApplyDirectCEBeh (approvals : List ApprovedModification) (n : Nat) : Prop :=
  ∀ (op : Val) (args : List Val) (L : Nat)
    (T_base T_subst : TowerState) (r : Val) (T_base' : TowerState),
    op.Pure = true → ValList.Pure args = true →
    T_base.AllBbApply → T_base.Pure = true →
    T_subst.CEInvariant → T_subst.Pure = true →
    applyDirect (mkGate approvals) n op args L T_base = some (r, T_base') →
    r.Pure = true ∧ T_base'.AllBbApply ∧ T_base'.Pure = true ∧
    ∃ fuel' T_subst',
      applyDirect (mkGate approvals) fuel' op args L T_subst = some (r, T_subst') ∧
      T_subst'.CEInvariant ∧ T_subst'.Pure = true

def JointBeh (approvals : List ApprovedModification) (n : Nat) : Prop :=
  EvalCEBeh approvals n ∧ EvalListCEBeh approvals n ∧ EvalSeqCEBeh approvals n ∧
  ApplyViaCEBeh approvals n ∧ ApplyDirectCEBeh approvals n

/-! ## The joint induction

For brevity in the proof body, derive `joint`'s extracts (Pure
preservation) at the top, then case-split. -/

theorem jointBeh (approvals : List ApprovedModification) :
    ∀ n, JointBeh approvals n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold EvalCEBeh
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [eval] at h
    · unfold EvalListCEBeh
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [evalList] at h
    · unfold EvalSeqCEBeh
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [evalSeq] at h
    · unfold ApplyViaCEBeh
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [applyVia] at h
    · unfold ApplyDirectCEBeh
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [applyDirect] at h
  | succ n ih =>
    obtain ⟨ihE, ihL, ihS, ihV, ihD⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    -- ============================================================
    -- EvalCEBeh at n+1
    -- ============================================================
    · unfold EvalCEBeh
      intro e ρ L T_base T_subst r T_base'
      intro he hρ hbase hbase_pure hsubst hsubst_pure h
      cases e with
      | lit v =>
        simp [eval] at h
        obtain ⟨hr, hT'⟩ := h
        simp [Expr.Pure] at he
        refine ⟨hr ▸ he, hT' ▸ hbase, hT' ▸ hbase_pure,
                1, T_subst, ?_, hsubst, hsubst_pure⟩
        simp [eval]; exact hr
      | var x =>
        simp [eval] at h
        cases hl : ρ.lookup x with
        | none => rw [hl] at h; simp at h
        | some v =>
          rw [hl] at h; simp at h
          obtain ⟨hr, hT'⟩ := h
          have hv := Env.lookup_Pure ρ hρ hl
          refine ⟨hr ▸ hv, hT' ▸ hbase, hT' ▸ hbase_pure,
                  1, T_subst, ?_, hsubst, hsubst_pure⟩
          simp [eval, hl]; exact hr
      | lam xs body =>
        simp [eval] at h
        obtain ⟨hr, hT'⟩ := h
        simp [Expr.Pure] at he
        have hclos : (Val.clos xs body ρ).Pure = true := by
          simp [Val.Pure]; exact ⟨he, hρ⟩
        refine ⟨hr ▸ hclos, hT' ▸ hbase, hT' ▸ hbase_pure,
                1, T_subst, ?_, hsubst, hsubst_pure⟩
        simp [eval]; exact hr
      | app f args =>
        simp [Expr.Pure] at he
        obtain ⟨hf, hargs⟩ := he
        simp [eval] at h
        cases h1 : eval (mkGate approvals) n f ρ L T_base with
        | none => rw [h1] at h; simp at h
        | some pr1 =>
          obtain ⟨vf, T₁⟩ := pr1
          rw [h1] at h; simp at h
          obtain ⟨hvf, hT₁_all, hT₁_pure, fuel_f, T_s1, hs1, hT_s1_inv, hT_s1_pure⟩ :=
            ihE f ρ L T_base T_subst vf T₁ hf hρ hbase hbase_pure hsubst hsubst_pure h1
          cases h2 : evalList (mkGate approvals) n args ρ L T₁ with
          | none => rw [h2] at h; simp at h
          | some pr2 =>
            obtain ⟨vs, T₂⟩ := pr2
            rw [h2] at h; simp at h
            obtain ⟨hvs, hT₂_all, hT₂_pure, fuel_a, T_s2, hs2, hT_s2_inv, hT_s2_pure⟩ :=
              ihL args ρ L T₁ T_s1 vs T₂ hargs hρ hT₁_all hT₁_pure hT_s1_inv hT_s1_pure h2
            have hdL : L + 1 ≥ 1 := Nat.succ_le_succ (Nat.zero_le _)
            obtain ⟨hr, hT'_all, hT'_pure, fuel_v, T_s3, hs3, hT_s3_inv, hT_s3_pure⟩ :=
              ihV (L+1) vf vs T₂ T_s2 r T_base' hvf hvs hT₂_all hT₂_pure hT_s2_inv hT_s2_pure hdL h
            refine ⟨hr, hT'_all, hT'_pure,
                    max fuel_f (max fuel_a fuel_v) + 1, T_s3, ?_, hT_s3_inv, hT_s3_pure⟩
            have hfM : fuel_f ≤ max fuel_f (max fuel_a fuel_v) := Nat.le_max_left _ _
            have haM : fuel_a ≤ max fuel_f (max fuel_a fuel_v) :=
              Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
            have hvM : fuel_v ≤ max fuel_f (max fuel_a fuel_v) :=
              Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
            have hs1' := eval_fuel_le _ _ _ _ _ _ _ _ _ hfM hs1
            have hs2' := evalList_fuel_le _ _ _ _ _ _ _ _ _ haM hs2
            have hs3' := applyVia_fuel_le _ _ _ _ _ _ _ _ _ hvM hs3
            simp only [eval]
            rw [hs1']; simp
            rw [hs2']; simp
            exact hs3'
      | appDirect f args =>
        simp [Expr.Pure] at he
        obtain ⟨hf, hargs⟩ := he
        simp [eval] at h
        cases h1 : eval (mkGate approvals) n f ρ L T_base with
        | none => rw [h1] at h; simp at h
        | some pr1 =>
          obtain ⟨vf, T₁⟩ := pr1
          rw [h1] at h; simp at h
          obtain ⟨hvf, hT₁_all, hT₁_pure, fuel_f, T_s1, hs1, hT_s1_inv, hT_s1_pure⟩ :=
            ihE f ρ L T_base T_subst vf T₁ hf hρ hbase hbase_pure hsubst hsubst_pure h1
          cases h2 : evalList (mkGate approvals) n args ρ L T₁ with
          | none => rw [h2] at h; simp at h
          | some pr2 =>
            obtain ⟨vs, T₂⟩ := pr2
            rw [h2] at h; simp at h
            obtain ⟨hvs, hT₂_all, hT₂_pure, fuel_a, T_s2, hs2, hT_s2_inv, hT_s2_pure⟩ :=
              ihL args ρ L T₁ T_s1 vs T₂ hargs hρ hT₁_all hT₁_pure hT_s1_inv hT_s1_pure h2
            obtain ⟨hr, hT'_all, hT'_pure, fuel_d, T_s3, hs3, hT_s3_inv, hT_s3_pure⟩ :=
              ihD vf vs L T₂ T_s2 r T_base' hvf hvs hT₂_all hT₂_pure hT_s2_inv hT_s2_pure h
            refine ⟨hr, hT'_all, hT'_pure,
                    max fuel_f (max fuel_a fuel_d) + 1, T_s3, ?_, hT_s3_inv, hT_s3_pure⟩
            have hfM : fuel_f ≤ max fuel_f (max fuel_a fuel_d) := Nat.le_max_left _ _
            have haM : fuel_a ≤ max fuel_f (max fuel_a fuel_d) :=
              Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
            have hdM : fuel_d ≤ max fuel_f (max fuel_a fuel_d) :=
              Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
            have hs1' := eval_fuel_le _ _ _ _ _ _ _ _ _ hfM hs1
            have hs2' := evalList_fuel_le _ _ _ _ _ _ _ _ _ haM hs2
            have hs3' := applyDirect_fuel_le _ _ _ _ _ _ _ _ _ hdM hs3
            simp only [eval]
            rw [hs1']; simp
            rw [hs2']; simp
            exact hs3'
      | em e' =>
        simp [Expr.Pure] at he
        simp [eval] at h
        have hbase_mat := TowerState.materialize_AllBbApply T_base (L+1) hbase
        have hbase_mat_pure := TowerState.materialize_Pure T_base (L+1) hbase_pure
        have hsubst_mat := materialize_CEInvariant T_subst (L+1) hsubst
        have hsubst_mat_pure := TowerState.materialize_Pure T_subst (L+1) hsubst_pure
        obtain ⟨hr, hT'_all, hT'_pure, fuel_sub, T_s', hs, hT_s_inv, hT_s_pure⟩ :=
          ihE e' ρ (L+1) (T_base.materialize (L+1)) (T_subst.materialize (L+1)) r T_base'
              he hρ hbase_mat hbase_mat_pure hsubst_mat hsubst_mat_pure h
        refine ⟨hr, hT'_all, hT'_pure, fuel_sub + 1, T_s', ?_, hT_s_inv, hT_s_pure⟩
        simp only [eval]; exact hs
      | setApply _ => simp [Expr.Pure] at he
      | setPolicy _ => simp [Expr.Pure] at he
      | ifte c t eel =>
        simp [Expr.Pure] at he
        obtain ⟨⟨hc, ht⟩, hee⟩ := he
        simp [eval] at h
        cases h1 : eval (mkGate approvals) n c ρ L T_base with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vc, T₁⟩ := pr
          rw [h1] at h; simp at h
          obtain ⟨hvc, hT₁_all, hT₁_pure, fuel_c, T_s1, hs1, hT_s1_inv, hT_s1_pure⟩ :=
            ihE c ρ L T_base T_subst vc T₁ hc hρ hbase hbase_pure hsubst hsubst_pure h1
          cases vc with
          | bool b =>
            cases b with
            | true =>
              simp at h
              obtain ⟨hr, hT'_all, hT'_pure, fuel_b, T_s2, hs2, hT_s2_inv, hT_s2_pure⟩ :=
                ihE t ρ L T₁ T_s1 r T_base' ht hρ hT₁_all hT₁_pure hT_s1_inv hT_s1_pure h
              refine ⟨hr, hT'_all, hT'_pure,
                      max fuel_c fuel_b + 1, T_s2, ?_, hT_s2_inv, hT_s2_pure⟩
              have hcM : fuel_c ≤ max fuel_c fuel_b := Nat.le_max_left _ _
              have hbM : fuel_b ≤ max fuel_c fuel_b := Nat.le_max_right _ _
              have hs1' := eval_fuel_le _ _ _ _ _ _ _ _ _ hcM hs1
              have hs2' := eval_fuel_le _ _ _ _ _ _ _ _ _ hbM hs2
              simp only [eval]
              rw [hs1']; simp
              exact hs2'
            | false =>
              simp at h
              obtain ⟨hr, hT'_all, hT'_pure, fuel_b, T_s2, hs2, hT_s2_inv, hT_s2_pure⟩ :=
                ihE eel ρ L T₁ T_s1 r T_base' hee hρ hT₁_all hT₁_pure hT_s1_inv hT_s1_pure h
              refine ⟨hr, hT'_all, hT'_pure,
                      max fuel_c fuel_b + 1, T_s2, ?_, hT_s2_inv, hT_s2_pure⟩
              have hcM : fuel_c ≤ max fuel_c fuel_b := Nat.le_max_left _ _
              have hbM : fuel_b ≤ max fuel_c fuel_b := Nat.le_max_right _ _
              have hs1' := eval_fuel_le _ _ _ _ _ _ _ _ _ hcM hs1
              have hs2' := eval_fuel_le _ _ _ _ _ _ _ _ _ hbM hs2
              simp only [eval]
              rw [hs1']; simp
              exact hs2'
          | num _ => simp at h
          | prim _ => simp at h
          | bbApply => simp at h
          | clos _ _ _ => simp at h
          | list _ => simp at h
      | seq es =>
        simp [Expr.Pure] at he
        simp [eval] at h
        obtain ⟨hr, hT'_all, hT'_pure, fuel_s, T_s', hs, hT_s_inv, hT_s_pure⟩ :=
          ihS es ρ L T_base T_subst r T_base' he hρ hbase hbase_pure hsubst hsubst_pure h
        refine ⟨hr, hT'_all, hT'_pure, fuel_s + 1, T_s', ?_, hT_s_inv, hT_s_pure⟩
        simp only [eval]; exact hs
    -- ============================================================
    -- EvalListCEBeh at n+1
    -- ============================================================
    · unfold EvalListCEBeh
      intro es ρ L T_base T_subst vs T_base'
      intro hes hρ hbase hbase_pure hsubst hsubst_pure h
      cases es with
      | nil =>
        simp [evalList] at h
        obtain ⟨hr, hT'⟩ := h
        refine ⟨?_, hT' ▸ hbase, hT' ▸ hbase_pure,
                1, T_subst, ?_, hsubst, hsubst_pure⟩
        · rw [hr]; rfl
        · simp [evalList]; rw [hr]
      | cons e es' =>
        simp [ExprList.Pure] at hes
        obtain ⟨he, hes'⟩ := hes
        simp [evalList] at h
        cases h1 : eval (mkGate approvals) n e ρ L T_base with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨v, T₁⟩ := pr
          rw [h1] at h; simp at h
          obtain ⟨hv, hT₁_all, hT₁_pure, fuel_e, T_s1, hs1, hT_s1_inv, hT_s1_pure⟩ :=
            ihE e ρ L T_base T_subst v T₁ he hρ hbase hbase_pure hsubst hsubst_pure h1
          cases h2 : evalList (mkGate approvals) n es' ρ L T₁ with
          | none => rw [h2] at h; simp at h
          | some pr2 =>
            obtain ⟨vs', T₂⟩ := pr2
            rw [h2] at h; simp at h
            obtain ⟨hvs', hT₂_all, hT₂_pure, fuel_es, T_s2, hs2, hT_s2_inv, hT_s2_pure⟩ :=
              ihL es' ρ L T₁ T_s1 vs' T₂ hes' hρ hT₁_all hT₁_pure hT_s1_inv hT_s1_pure h2
            obtain ⟨hvs_eq, hT'_eq⟩ := h
            refine ⟨?_, ?_, ?_, max fuel_e fuel_es + 1, T_s2, ?_, hT_s2_inv, hT_s2_pure⟩
            · rw [← hvs_eq]; simp [ValList.Pure]; exact ⟨hv, hvs'⟩
            · exact hT'_eq ▸ hT₂_all
            · exact hT'_eq ▸ hT₂_pure
            · have heM : fuel_e ≤ max fuel_e fuel_es := Nat.le_max_left _ _
              have hesM : fuel_es ≤ max fuel_e fuel_es := Nat.le_max_right _ _
              have hs1' := eval_fuel_le _ _ _ _ _ _ _ _ _ heM hs1
              have hs2' := evalList_fuel_le _ _ _ _ _ _ _ _ _ hesM hs2
              simp only [evalList]
              rw [hs1']; simp
              rw [hs2']; simp
              exact hvs_eq
    -- ============================================================
    -- EvalSeqCEBeh at n+1
    -- ============================================================
    · unfold EvalSeqCEBeh
      intro es ρ L T_base T_subst r T_base'
      intro hes hρ hbase hbase_pure hsubst hsubst_pure h
      cases es with
      | nil =>
        simp [evalSeq] at h
        obtain ⟨hr, hT'⟩ := h
        refine ⟨?_, hT' ▸ hbase, hT' ▸ hbase_pure,
                1, T_subst, ?_, hsubst, hsubst_pure⟩
        · rw [← hr]; simp [Val.Pure]
        · simp [evalSeq]; exact hr
      | cons e tl =>
        cases tl with
        | nil =>
          simp [ExprList.Pure] at hes
          simp [evalSeq] at h
          obtain ⟨hr, hT'_all, hT'_pure, fuel_e, T_s', hs, hT_s_inv, hT_s_pure⟩ :=
            ihE e ρ L T_base T_subst r T_base' hes hρ hbase hbase_pure hsubst hsubst_pure h
          refine ⟨hr, hT'_all, hT'_pure, fuel_e + 1, T_s', ?_, hT_s_inv, hT_s_pure⟩
          simp only [evalSeq]; exact hs
        | cons e' es' =>
          simp [ExprList.Pure] at hes
          obtain ⟨he, hes'⟩ := hes
          simp [evalSeq] at h
          cases h1 : eval (mkGate approvals) n e ρ L T_base with
          | none => rw [h1] at h; simp at h
          | some pr =>
            obtain ⟨v, T₁⟩ := pr
            rw [h1] at h; simp at h
            obtain ⟨_, hT₁_all, hT₁_pure, fuel_e, T_s1, hs1, hT_s1_inv, hT_s1_pure⟩ :=
              ihE e ρ L T_base T_subst v T₁ he hρ hbase hbase_pure hsubst hsubst_pure h1
            have hes_all : ExprList.Pure (e' :: es') = true := by
              simp [ExprList.Pure]; exact hes'
            obtain ⟨hr, hT'_all, hT'_pure, fuel_r, T_s2, hs2, hT_s2_inv, hT_s2_pure⟩ :=
              ihS (e' :: es') ρ L T₁ T_s1 r T_base' hes_all hρ hT₁_all hT₁_pure hT_s1_inv hT_s1_pure h
            refine ⟨hr, hT'_all, hT'_pure,
                    max fuel_e fuel_r + 1, T_s2, ?_, hT_s2_inv, hT_s2_pure⟩
            have heM : fuel_e ≤ max fuel_e fuel_r := Nat.le_max_left _ _
            have hrM : fuel_r ≤ max fuel_e fuel_r := Nat.le_max_right _ _
            have hs1' := eval_fuel_le _ _ _ _ _ _ _ _ _ heM hs1
            have hs2' := evalSeq_fuel_le _ _ _ _ _ _ _ _ _ hrM hs2
            simp only [evalSeq]
            rw [hs1']; simp
            exact hs2'
    -- ============================================================
    -- ApplyViaCEBeh at n+1
    -- ============================================================
    · unfold ApplyViaCEBeh
      intro dL op args T_base T_subst r T_base'
      intro hop hargs hbase hbase_pure hsubst hsubst_pure hdL h
      simp only [applyVia] at h
      have hbase_mat_all := TowerState.materialize_AllBbApply T_base dL hbase
      have hbase_mat_pure := TowerState.materialize_Pure T_base dL hbase_pure
      have hsubst_mat_inv := materialize_CEInvariant T_subst dL hsubst
      have hsubst_mat_pure := TowerState.materialize_Pure T_subst dL hsubst_pure
      have hdisp_base : (T_base.materialize dL).applyAt dL = .bbApply :=
        TowerState.AllBbApply.applyAt _ hbase_mat_all dL
      rw [hdisp_base] at h
      -- h : applyDirect _ n op args (dL-1) (T_base.mat) = some (r, T_base')
      obtain ⟨hr, hT'_all, hT'_pure, fuel_d, T_subst', hsd, hT_s_inv, hT_s_pure⟩ :=
        ihD op args (dL-1) (T_base.materialize dL) (T_subst.materialize dL) r T_base'
            hop hargs hbase_mat_all hbase_mat_pure hsubst_mat_inv hsubst_mat_pure h
      have hdisp_pure : ((T_subst.materialize dL).applyAt dL).Pure = true :=
        TowerState.applyAt_Pure hsubst_mat_pure
      have hCE_disp : CE (dL - 1) ((T_subst.materialize dL).applyAt dL) := by
        have hCE := CEInvariant_applyAt_CE (T_subst.materialize dL) hsubst_mat_inv (dL - 1)
        rwa [Nat.sub_add_cancel hdL] at hCE
      by_cases hbb : (T_subst.materialize dL).applyAt dL = .bbApply
      · -- Substrate dispatcher is bbApply
        refine ⟨hr, hT'_all, hT'_pure, fuel_d + 1, T_subst', ?_, hT_s_inv, hT_s_pure⟩
        simp only [applyVia, hbb]
        exact hsd
      · -- Substrate dispatcher is some w ≠ bbApply: bridge via CE
        have hargs_w : ValList.Pure [op, .list args] = true := by
          simp [ValList.Pure, Val.Pure]; exact ⟨hop, hargs⟩
        -- Step 1: swap mkGate → acceptAll on bbApply-side dispatch result
        have hgi1 := applyDirect_pure_gate_indep (mkGate approvals) acceptAll fuel_d op args
                      (dL-1) (T_subst.materialize dL) hop hargs hsubst_mat_pure
        rw [hgi1] at hsd
        -- Step 2: pack into bbApply form
        have hsd_bb :=
          applyDirect_bbApply_unpack acceptAll fuel_d op args (dL-1)
            (T_subst.materialize dL) r T_subst' hsd
        -- Step 3: apply CE on the substrate's dispatcher
        obtain ⟨fuel_w, r', T_post', hsd_w, hr_eq, hT_eq⟩ :=
          hCE_disp (fuel_d + 1) op args (T_subst.materialize dL) r T_subst' hsd_bb
        rw [← hr_eq, ← hT_eq] at hsd_w
        -- Step 4: swap acceptAll → mkGate on wrapper-form
        have hgi2 := applyDirect_pure_gate_indep acceptAll (mkGate approvals) fuel_w
                      ((T_subst.materialize dL).applyAt dL) [op, .list args] (dL-1)
                      (T_subst.materialize dL) hdisp_pure hargs_w hsubst_mat_pure
        rw [hgi2] at hsd_w
        -- Substrate applyVia at fuel (fuel_w + 1): takes the second arm
        refine ⟨hr, hT'_all, hT'_pure, fuel_w + 1, T_subst', ?_, hT_s_inv, hT_s_pure⟩
        simp only [applyVia]
        cases hwd : (T_subst.materialize dL).applyAt dL with
        | bbApply => exact absurd hwd hbb
        | num k => rw [hwd] at hsd_w; exact hsd_w
        | bool b => rw [hwd] at hsd_w; exact hsd_w
        | prim p => rw [hwd] at hsd_w; exact hsd_w
        | clos xs body env_c => rw [hwd] at hsd_w; exact hsd_w
        | list vs => rw [hwd] at hsd_w; exact hsd_w
    -- ============================================================
    -- ApplyDirectCEBeh at n+1
    -- ============================================================
    · unfold ApplyDirectCEBeh
      intro op args L T_base T_subst r T_base'
      intro hop hargs hbase hbase_pure hsubst hsubst_pure h
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
          obtain ⟨hr, hT'⟩ := h
          refine ⟨?_, hT' ▸ hbase, hT' ▸ hbase_pure,
                  1, T_subst, ?_, hsubst, hsubst_pure⟩
          · rw [← hr]; exact applyPrim_Pure hp
          · simp [applyDirect, hp]; exact hr
      | clos xs body env_c =>
        simp [Val.Pure] at hop
        obtain ⟨hbody, henv⟩ := hop
        simp [applyDirect] at h
        cases hext : env_c.extend xs args with
        | none => rw [hext] at h; simp at h
        | some ρ' =>
          rw [hext] at h; simp at h
          have hρ' := Env.extend_Pure xs args henv hargs hext
          obtain ⟨hr, hT'_all, hT'_pure, fuel_b, T_s', hs, hT_s_inv, hT_s_pure⟩ :=
            ihE body ρ' L T_base T_subst r T_base' hbody hρ' hbase hbase_pure hsubst hsubst_pure h
          refine ⟨hr, hT'_all, hT'_pure, fuel_b + 1, T_s', ?_, hT_s_inv, hT_s_pure⟩
          simp only [applyDirect, hext]; exact hs
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
                simp [ValList.Pure, Val.Pure] at hargs
                obtain ⟨ha, hargs'⟩ := hargs
                obtain ⟨hr, hT'_all, hT'_pure, fuel_a, T_s', hs, hT_s_inv, hT_s_pure⟩ :=
                  ihD a args' L T_base T_subst r T_base'
                      ha hargs' hbase hbase_pure hsubst hsubst_pure h
                refine ⟨hr, hT'_all, hT'_pure, fuel_a + 1, T_s', ?_, hT_s_inv, hT_s_pure⟩
                simp only [applyDirect]; exact hs
              | num _ => simp [applyDirect] at h
              | bool _ => simp [applyDirect] at h
              | prim _ => simp [applyDirect] at h
              | bbApply => simp [applyDirect] at h
              | clos _ _ _ => simp [applyDirect] at h
            | cons _ _ => simp [applyDirect] at h

/-! ## Headline corollaries

`substrate_behavioral_CE` — for any pure-of-effects program `e`, pure env
`ρ`, pure `AllBbApply` baseline tower `T_base`, and pure `CEInvariant`
substrate tower `T_subst`: a baseline success under `acceptAll` lifts to
a substrate success under `mkGate approvals` with the same value.

The baseline gate is `acceptAll`. We swap to
`mkGate approvals` via `eval_pure_gate_indep` and then dispatch the
joint induction. -/

theorem substrate_behavioral_CE
    (approvals : List ApprovedModification)
    (e : Expr) (ρ : Env) (L : Nat)
    (T_base T_subst : TowerState)
    (he : e.Pure = true) (hρ : ρ.Pure = true)
    (hT_base : T_base.AllBbApply) (hT_base_pure : T_base.Pure = true)
    (hT_subst : T_subst.CEInvariant) (hT_subst_pure : T_subst.Pure = true)
    (n : Nat) (r : Val) (T_post_base : TowerState)
    (h : eval acceptAll n e ρ L T_base = some (r, T_post_base)) :
    ∃ fuel' T_post_subst,
      eval (mkGate approvals) fuel' e ρ L T_subst = some (r, T_post_subst) := by
  -- Gate-swap on the baseline trace: acceptAll → mkGate approvals
  have hgi :=
    eval_pure_gate_indep acceptAll (mkGate approvals) n e ρ L T_base he hρ hT_base_pure
  rw [hgi] at h
  -- Apply joint cross-tower CE
  obtain ⟨_, _, _, fuel', T_post_subst, hsubst, _, _⟩ :=
    (jointBeh approvals n).1 e ρ L T_base T_subst r T_post_base
      he hρ hT_base hT_base_pure hT_subst hT_subst_pure h
  exact ⟨fuel', T_post_subst, hsubst⟩

/-- Specialization to `initTower` — both `AllBbApply` and `CEInvariant`
    and `Pure`, so the side conditions collapse to `e.Pure` and `ρ.Pure`. -/
theorem substrate_behavioral_CE_initTower
    (approvals : List ApprovedModification)
    (e : Expr) (ρ : Env)
    (he : e.Pure = true) (hρ : ρ.Pure = true)
    (n : Nat) (r : Val) (T_post_base : TowerState)
    (h : eval acceptAll n e ρ 0 initTower = some (r, T_post_base)) :
    ∃ fuel' T_post_subst,
      eval (mkGate approvals) fuel' e ρ 0 initTower = some (r, T_post_subst) :=
  substrate_behavioral_CE approvals e ρ 0 initTower initTower
    he hρ initTower_AllBbApply initTower_Pure initTower_CEInvariant initTower_Pure
    n r T_post_base h

/-- Specialization to `initEnv`+`initTower`: the side conditions
    collapse to `e.Pure`. -/
theorem substrate_behavioral_CE_initEnv
    (approvals : List ApprovedModification)
    (e : Expr) (he : e.Pure = true)
    (n : Nat) (r : Val) (T_post_base : TowerState)
    (h : eval acceptAll n e initEnv 0 initTower = some (r, T_post_base)) :
    ∃ fuel' T_post_subst,
      eval (mkGate approvals) fuel' e initEnv 0 initTower = some (r, T_post_subst) :=
  substrate_behavioral_CE_initTower approvals e initEnv he initEnv_Pure
    n r T_post_base h

/-- Top-level form using `evalProgram`. -/
theorem substrate_extends_baseline_evalProgram
    (approvals : List ApprovedModification)
    (n : Nat) (e : Expr) (he : e.Pure = true) (r : Val)
    (h : evalProgram n e acceptAll = some r) :
    ∃ fuel', evalProgram fuel' e (mkGate approvals) = some r := by
  unfold evalProgram at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨pr, hp, hr⟩ := h
  obtain ⟨v, T'⟩ := pr
  simp at hr
  obtain ⟨fuel', T_subst, hsub⟩ :=
    substrate_behavioral_CE_initEnv approvals e he n v T' hp
  refine ⟨fuel', ?_⟩
  unfold evalProgram
  rw [hsub]
  simp
  exact hr

end LeanEmerald

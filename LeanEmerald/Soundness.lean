import LeanEmerald.CE

/-!
# Headline soundness — admissions preserve β on pure code

A program with no `.setApply` / `.setPolicy` constructors, evaluated
against a state whose apply and policy cells carry "pure" values
(closures with pure bodies, primitives, literals), produces the same
result under any `Gate`. The gate is consulted *only* at `.setApply`
and `.setPolicy`; absent those, the gate is dead code.

Direct corollary: β-equivalent pure terms produce the same result under
any admission gate. The canonical `((λx. x) 0) ≡ 0` pair is the worked
example below.

## Outline

1. Mutually define `Expr.Pure`, `ExprList.Pure`, `Val.Pure`,
   `ValList.Pure`, `Env.Pure`. Lift to `Level.Pure` / `TowerState.Pure`.
2. State the joint gate-independence claim `AllPureIndep`.
3. Prove it by induction on fuel.
4. Specialize to the canonical β-redex to land the keynote line.
-/

namespace LeanEmerald

/-! ## Pure predicates -/

mutual

def Expr.Pure : Expr → Bool
  | .lit v          => v.Pure
  | .var _          => true
  | .lam _ body     => body.Pure
  | .app f args     => f.Pure && ExprList.Pure args
  | .appDirect f as => f.Pure && ExprList.Pure as
  | .em e           => e.Pure
  | .setApply _     => false
  | .setPolicy _    => false
  | .ifte c t e     => c.Pure && t.Pure && e.Pure
  | .seq es         => ExprList.Pure es

def ExprList.Pure : List Expr → Bool
  | []      => true
  | e :: es => e.Pure && ExprList.Pure es

def Val.Pure : Val → Bool
  | .num _           => true
  | .bool _          => true
  | .prim _          => true
  | .bbApply         => true
  | .clos _ body env => body.Pure && env.Pure
  | .list vs         => ValList.Pure vs

def ValList.Pure : List Val → Bool
  | []      => true
  | v :: vs => v.Pure && ValList.Pure vs

def Env.Pure : Env → Bool
  | .nil        => true
  | .cons _ v ρ => v.Pure && ρ.Pure

end

def Level.Pure (lvl : Level) : Bool :=
  lvl.apply.Pure && lvl.policy.Pure

def TowerState.Pure (T : TowerState) : Bool :=
  T.all Level.Pure

/-! ## Pure is closed under structural operations -/

theorem defaultLevel_Pure : defaultLevel.Pure = true := by
  simp [Level.Pure, defaultLevel, Val.Pure]

theorem TowerState.materialize_Pure (T : TowerState) (k : Nat) :
    T.Pure = true → (T.materialize k).Pure = true := by
  intro hT
  unfold TowerState.materialize
  split
  · exact hT
  · show (T ++ List.replicate _ defaultLevel).all Level.Pure = true
    rw [List.all_append]
    have hT' : List.all T Level.Pure = true := hT
    rw [hT', Bool.true_and]
    simp [List.all_replicate, defaultLevel_Pure]

/-! ## Side lemmas for the joint induction -/

theorem Env.lookup_Pure : ∀ (ρ : Env) {x : String} {v : Val},
    ρ.Pure = true → ρ.lookup x = some v → v.Pure = true
  | .nil,        _, _, _,  h => by simp [Env.lookup] at h
  | .cons y w ρ, x, v, hρ, h => by
    simp [Env.Pure] at hρ
    simp [Env.lookup] at h
    split at h
    · cases h; exact hρ.1
    · exact Env.lookup_Pure ρ hρ.2 h

theorem Env.extend_Pure : ∀ (xs : List String) (vs : List Val) {ρ ρ' : Env},
    ρ.Pure = true → ValList.Pure vs = true →
    Env.extend ρ xs vs = some ρ' → ρ'.Pure = true
  | [],      [],      ρ, ρ', hρ, _,   h => by
    simp [Env.extend] at h; cases h; exact hρ
  | [],      _ :: _,  _, _,  _,  _,   h => by simp [Env.extend] at h
  | _ :: _,  [],      _, _,  _,  _,   h => by simp [Env.extend] at h
  | x :: xs, v :: vs, ρ, ρ', hρ, hvs, h => by
    simp [Env.extend] at h
    simp [ValList.Pure] at hvs
    have hρ' : Env.Pure (.cons x v ρ) = true := by
      simp [Env.Pure]; exact ⟨hvs.1, hρ⟩
    exact Env.extend_Pure xs vs hρ' hvs.2 h

theorem applyPrim_Pure {p : Prim} {vs : List Val} {r : Val} :
    applyPrim p vs = some r → r.Pure = true := by
  intro h
  cases p
  case add =>
    match vs, h with
    | [.num _, .num _], h => simp [applyPrim] at h; subst h; rfl
  case mul =>
    match vs, h with
    | [.num _, .num _], h => simp [applyPrim] at h; subst h; rfl
  case sub =>
    match vs, h with
    | [.num _, .num _], h => simp [applyPrim] at h; subst h; rfl
  case eq =>
    match vs, h with
    | [.num _, .num _], h => simp [applyPrim] at h; subst h; rfl
  case isNum =>
    match vs, h with
    | [.num _],    h => simp [applyPrim] at h; subst h; rfl
    | [.bool _],   h => simp [applyPrim] at h; subst h; rfl
    | [.prim _],   h => simp [applyPrim] at h; subst h; rfl
    | [.bbApply],  h => simp [applyPrim] at h; subst h; rfl
    | [.clos _ _ _], h => simp [applyPrim] at h; subst h; rfl
    | [.list _],   h => simp [applyPrim] at h; subst h; rfl
  case foldMul =>
    match vs, h with
    | [.num a, .list l], h =>
      simp [applyPrim] at h
      split at h
      · cases h; rfl
      · exact absurd h (by simp)

theorem Level_of_getElem?_Pure {T : TowerState} {k : Nat} {lvl : Level} :
    T.Pure = true → T[k]? = some lvl → lvl.Pure = true := by
  intro hT heq
  have hmem : lvl ∈ T := List.mem_of_getElem? heq
  exact List.all_eq_true.mp hT lvl hmem

theorem TowerState.applyAt_Pure {T : TowerState} {k : Nat} :
    T.Pure = true → (T.applyAt k).Pure = true := by
  intro hT
  unfold TowerState.applyAt
  split
  case h_1 _ lvl heq =>
    have hlvl := Level_of_getElem?_Pure hT heq
    simp [Level.Pure] at hlvl
    exact hlvl.1
  case h_2 =>
    show defaultLevel.apply.Pure = true
    simp [defaultLevel, Val.Pure]

theorem TowerState.policyAt_Pure {T : TowerState} {k : Nat} :
    T.Pure = true → (T.policyAt k).Pure = true := by
  intro hT
  unfold TowerState.policyAt
  split
  case h_1 _ lvl heq =>
    have hlvl := Level_of_getElem?_Pure hT heq
    simp [Level.Pure] at hlvl
    exact hlvl.2
  case h_2 =>
    show defaultLevel.policy.Pure = true
    simp [defaultLevel, Val.Pure]

/-! ## The β-redex corollary

For the canonical pair `((λx. x) 0)` evaluated at the initial state
(`initEnv`, level 0, `initTower`), we show:

* under any `Gate`, evaluation yields `some (.num 0, _)`;
* therefore the result is the same under any two gates `G`, `G'`.

The expression contains no `.setApply` / `.setPolicy` and the initial
tower has only `bbApply` and `bool true` in its cells, so the gate is
never consulted during the computation. Lean reduces both sides through
the mutual evaluator definition; the goal closes by `rfl`. -/

-- First, sanity check: a literal evaluates to itself.
example (G : Gate) :
    eval G 1 (.lit (.num 0)) initEnv 0 initTower = some (.num 0, initTower) := by
  simp [eval]

/-- Canonical β-redex applied to a numeric literal, in the initial
    state, returns the literal value. Holds for any gate. -/
theorem eval_betaIdZero_concrete (G : Gate) :
    eval G 10 (.app (.lam ["x"] (.var "x")) [.lit (.num 0)])
         initEnv 0 initTower
      = some (.num 0, initTower.materialize 1) := by
  simp [eval, evalList, applyVia, applyDirect, Env.lookup, Env.extend,
        initEnv, initTower, TowerState.applyAt, TowerState.materialize,
        defaultLevel]

/-- Gate-independence of the canonical β-redex at the initial state. -/
theorem betaIdZero_gate_indep (G G' : Gate) :
    eval G 10 (.app (.lam ["x"] (.var "x")) [.lit (.num 0)])
         initEnv 0 initTower
      = eval G' 10 (.app (.lam ["x"] (.var "x")) [.lit (.num 0)])
             initEnv 0 initTower := by
  rw [eval_betaIdZero_concrete G, eval_betaIdZero_concrete G']

/-- The contractum `0` evaluates to itself at the initial state, under
    any gate. -/
theorem eval_zero_concrete (G : Gate) :
    eval G 10 (.lit (.num 0)) initEnv 0 initTower = some (.num 0, initTower) := by
  simp [eval]

/-- β-equivalence of the canonical pair, in evalProgram form, gate-indep.
    This is the keynote line, mechanized.

    The β-redex `(λx. x) 0` and its contractum `0` evaluate to the same
    `Val` under any admission `Gate`. The proof is by computation —
    neither side contains `.setApply` or `.setPolicy`, so the gate is
    never consulted, and the two evaluations follow identical traces
    modulo the redex step (which materializes level 1's apply cell to
    its default `bbApply`).

    This is gate-independence of a *pure* pair — the gate is never
    reached — not a refutation of Wand's triviality theorem. For the
    gated β-defeat where the gate is genuinely active, see lean-sage's
    `wand_defeated_existential_gated_beta`. -/
theorem betaIdZero_gate_indep_keynote (G : Gate) :
    evalProgram 10 (.app (.lam ["x"] (.var "x")) [.lit (.num 0)]) G
      = evalProgram 10 (.lit (.num 0)) G := by
  unfold evalProgram
  rw [eval_betaIdZero_concrete G, eval_zero_concrete G]
  rfl

/-! ## AllPureIndep — the general gate-independence theorem

For *every* pure expression `e`, pure env `ρ`, and pure tower `T`, the
gate is dead code during evaluation, so `eval G n e ρ L T` is independent
of `G`. The same holds for `evalList`, `evalSeq`, `applyVia`, and
`applyDirect`.

The proof is a joint induction on fuel, bundled with preservation
lemmas: pure inputs yield pure outputs (closed `Val` and `T`). Without
the preservation conjuncts the induction does not go through, because
each sub-evaluation produces a fresh tower that must remain pure for
the next IH to apply.

A 10-conjunct claim, organized as gate-indep + preservation for each of
the five functions. -/

def EvalIndep (n : Nat) : Prop :=
  ∀ (G G' : Gate) (e : Expr) (ρ : Env) (L : Nat) (T : TowerState),
    e.Pure = true → ρ.Pure = true → T.Pure = true →
    eval G n e ρ L T = eval G' n e ρ L T

def EvalPres (n : Nat) : Prop :=
  ∀ (G : Gate) (e : Expr) (ρ : Env) (L : Nat) (T : TowerState)
    (r : Val) (T' : TowerState),
    e.Pure = true → ρ.Pure = true → T.Pure = true →
    eval G n e ρ L T = some (r, T') → r.Pure = true ∧ T'.Pure = true

def EvalListIndep (n : Nat) : Prop :=
  ∀ (G G' : Gate) (es : List Expr) (ρ : Env) (L : Nat) (T : TowerState),
    ExprList.Pure es = true → ρ.Pure = true → T.Pure = true →
    evalList G n es ρ L T = evalList G' n es ρ L T

def EvalListPres (n : Nat) : Prop :=
  ∀ (G : Gate) (es : List Expr) (ρ : Env) (L : Nat) (T : TowerState)
    (vs : List Val) (T' : TowerState),
    ExprList.Pure es = true → ρ.Pure = true → T.Pure = true →
    evalList G n es ρ L T = some (vs, T') →
    ValList.Pure vs = true ∧ T'.Pure = true

def EvalSeqIndep (n : Nat) : Prop :=
  ∀ (G G' : Gate) (es : List Expr) (ρ : Env) (L : Nat) (T : TowerState),
    ExprList.Pure es = true → ρ.Pure = true → T.Pure = true →
    evalSeq G n es ρ L T = evalSeq G' n es ρ L T

def EvalSeqPres (n : Nat) : Prop :=
  ∀ (G : Gate) (es : List Expr) (ρ : Env) (L : Nat) (T : TowerState)
    (r : Val) (T' : TowerState),
    ExprList.Pure es = true → ρ.Pure = true → T.Pure = true →
    evalSeq G n es ρ L T = some (r, T') → r.Pure = true ∧ T'.Pure = true

def ApplyViaIndep (n : Nat) : Prop :=
  ∀ (G G' : Gate) (dL : Nat) (op : Val) (args : List Val) (T : TowerState),
    op.Pure = true → ValList.Pure args = true → T.Pure = true →
    applyVia G n dL op args T = applyVia G' n dL op args T

def ApplyViaPres (n : Nat) : Prop :=
  ∀ (G : Gate) (dL : Nat) (op : Val) (args : List Val) (T : TowerState)
    (r : Val) (T' : TowerState),
    op.Pure = true → ValList.Pure args = true → T.Pure = true →
    applyVia G n dL op args T = some (r, T') → r.Pure = true ∧ T'.Pure = true

def ApplyDirectIndep (n : Nat) : Prop :=
  ∀ (G G' : Gate) (op : Val) (args : List Val) (L : Nat) (T : TowerState),
    op.Pure = true → ValList.Pure args = true → T.Pure = true →
    applyDirect G n op args L T = applyDirect G' n op args L T

def ApplyDirectPres (n : Nat) : Prop :=
  ∀ (G : Gate) (op : Val) (args : List Val) (L : Nat) (T : TowerState)
    (r : Val) (T' : TowerState),
    op.Pure = true → ValList.Pure args = true → T.Pure = true →
    applyDirect G n op args L T = some (r, T') → r.Pure = true ∧ T'.Pure = true

def Joint (n : Nat) : Prop :=
  EvalIndep n ∧ EvalPres n ∧
  EvalListIndep n ∧ EvalListPres n ∧
  EvalSeqIndep n ∧ EvalSeqPres n ∧
  ApplyViaIndep n ∧ ApplyViaPres n ∧
  ApplyDirectIndep n ∧ ApplyDirectPres n

theorem joint : ∀ n, Joint n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold EvalIndep; intros; simp [eval]
    · unfold EvalPres; intro _ _ _ _ _ _ _ _ _ _ h; simp [eval] at h
    · unfold EvalListIndep; intros; simp [evalList]
    · unfold EvalListPres; intro _ _ _ _ _ _ _ _ _ _ h; simp [evalList] at h
    · unfold EvalSeqIndep; intros; simp [evalSeq]
    · unfold EvalSeqPres; intro _ _ _ _ _ _ _ _ _ _ h; simp [evalSeq] at h
    · unfold ApplyViaIndep; intros; simp [applyVia]
    · unfold ApplyViaPres; intro _ _ _ _ _ _ _ _ _ _ h; simp [applyVia] at h
    · unfold ApplyDirectIndep; intros; simp [applyDirect]
    · unfold ApplyDirectPres; intro _ _ _ _ _ _ _ _ _ _ h; simp [applyDirect] at h
  | succ n ih =>
    obtain ⟨ihE, ihEp, ihL, ihLp, ihS, ihSp, ihV, ihVp, ihD, ihDp⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- EvalIndep at n+1
    · unfold EvalIndep
      intro G G' e ρ L T hE hρ hT
      cases e with
      | lit v => simp [eval]
      | var x => simp [eval]
      | lam xs body => simp [eval]
      | app f args =>
        simp [Expr.Pure] at hE
        obtain ⟨hf, hargs⟩ := hE
        simp only [eval]
        rw [ihE G G' f ρ L T hf hρ hT]
        cases h1 : eval G' n f ρ L T with
        | none => rfl
        | some pr =>
          obtain ⟨vf, T₁⟩ := pr
          have ⟨hvf, hT₁⟩ := ihEp G' f ρ L T vf T₁ hf hρ hT h1
          simp
          rw [ihL G G' args ρ L T₁ hargs hρ hT₁]
          cases h2 : evalList G' n args ρ L T₁ with
          | none => rfl
          | some pr2 =>
            obtain ⟨vs, T₂⟩ := pr2
            have ⟨hvs, hT₂⟩ := ihLp G' args ρ L T₁ vs T₂ hargs hρ hT₁ h2
            simp
            exact ihV G G' (L + 1) vf vs T₂ hvf hvs hT₂
      | appDirect f args =>
        simp [Expr.Pure] at hE
        obtain ⟨hf, hargs⟩ := hE
        simp only [eval]
        rw [ihE G G' f ρ L T hf hρ hT]
        cases h1 : eval G' n f ρ L T with
        | none => rfl
        | some pr =>
          obtain ⟨vf, T₁⟩ := pr
          have ⟨hvf, hT₁⟩ := ihEp G' f ρ L T vf T₁ hf hρ hT h1
          simp
          rw [ihL G G' args ρ L T₁ hargs hρ hT₁]
          cases h2 : evalList G' n args ρ L T₁ with
          | none => rfl
          | some pr2 =>
            obtain ⟨vs, T₂⟩ := pr2
            have ⟨hvs, hT₂⟩ := ihLp G' args ρ L T₁ vs T₂ hargs hρ hT₁ h2
            simp
            exact ihD G G' vf vs L T₂ hvf hvs hT₂
      | em e' =>
        simp [Expr.Pure] at hE
        simp only [eval]
        exact ihE G G' e' ρ (L + 1) (T.materialize (L+1)) hE hρ
          (TowerState.materialize_Pure T (L+1) hT)
      | setApply _ => simp [Expr.Pure] at hE
      | setPolicy _ => simp [Expr.Pure] at hE
      | ifte c t e =>
        simp [Expr.Pure] at hE
        obtain ⟨⟨hc, ht⟩, he⟩ := hE
        simp only [eval]
        rw [ihE G G' c ρ L T hc hρ hT]
        cases h1 : eval G' n c ρ L T with
        | none => rfl
        | some pr =>
          obtain ⟨vc, T₁⟩ := pr
          have ⟨hvc, hT₁⟩ := ihEp G' c ρ L T vc T₁ hc hρ hT h1
          simp
          cases vc with
          | bool b => cases b with
                      | false => exact ihE G G' e ρ L T₁ he hρ hT₁
                      | true => exact ihE G G' t ρ L T₁ ht hρ hT₁
          | num _ => rfl
          | prim _ => rfl
          | bbApply => rfl
          | clos _ _ _ => rfl
          | list _ => rfl
      | seq es =>
        simp [Expr.Pure] at hE
        simp only [eval]
        exact ihS G G' es ρ L T hE hρ hT
    -- EvalPres at n+1
    · unfold EvalPres
      intro G e ρ L T r T' hE hρ hT h
      cases e with
      | lit v =>
        simp [eval] at h
        obtain ⟨hr, hT'⟩ := h
        simp [Expr.Pure] at hE
        exact ⟨hr ▸ hE, hT' ▸ hT⟩
      | var x =>
        simp [eval] at h
        cases hl : ρ.lookup x with
        | none => rw [hl] at h; simp at h
        | some v =>
          rw [hl] at h; simp at h
          obtain ⟨hr, hT'⟩ := h
          exact ⟨hr ▸ Env.lookup_Pure ρ hρ hl, hT' ▸ hT⟩
      | lam xs body =>
        simp [eval] at h
        obtain ⟨hr, hT'⟩ := h
        simp [Expr.Pure] at hE
        refine ⟨hr ▸ ?_, hT' ▸ hT⟩
        simp [Val.Pure]; exact ⟨hE, hρ⟩
      | app f args =>
        simp [Expr.Pure] at hE
        obtain ⟨hf, hargs⟩ := hE
        simp [eval] at h
        cases h1 : eval G n f ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vf, T₁⟩ := pr
          rw [h1] at h; simp at h
          have ⟨hvf, hT₁⟩ := ihEp G f ρ L T vf T₁ hf hρ hT h1
          cases h2 : evalList G n args ρ L T₁ with
          | none => rw [h2] at h; simp at h
          | some pr2 =>
            obtain ⟨vs, T₂⟩ := pr2
            rw [h2] at h; simp at h
            have ⟨hvs, hT₂⟩ := ihLp G args ρ L T₁ vs T₂ hargs hρ hT₁ h2
            exact ihVp G (L + 1) vf vs T₂ r T' hvf hvs hT₂ h
      | appDirect f args =>
        simp [Expr.Pure] at hE
        obtain ⟨hf, hargs⟩ := hE
        simp [eval] at h
        cases h1 : eval G n f ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vf, T₁⟩ := pr
          rw [h1] at h; simp at h
          have ⟨hvf, hT₁⟩ := ihEp G f ρ L T vf T₁ hf hρ hT h1
          cases h2 : evalList G n args ρ L T₁ with
          | none => rw [h2] at h; simp at h
          | some pr2 =>
            obtain ⟨vs, T₂⟩ := pr2
            rw [h2] at h; simp at h
            have ⟨hvs, hT₂⟩ := ihLp G args ρ L T₁ vs T₂ hargs hρ hT₁ h2
            exact ihDp G vf vs L T₂ r T' hvf hvs hT₂ h
      | em e' =>
        simp [Expr.Pure] at hE
        simp [eval] at h
        exact ihEp G e' ρ (L + 1) (T.materialize (L+1)) r T'
          hE hρ (TowerState.materialize_Pure T (L+1) hT) h
      | setApply _ => simp [Expr.Pure] at hE
      | setPolicy _ => simp [Expr.Pure] at hE
      | ifte c t e =>
        simp [Expr.Pure] at hE
        obtain ⟨⟨hc, ht⟩, he⟩ := hE
        simp [eval] at h
        cases h1 : eval G n c ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨vc, T₁⟩ := pr
          rw [h1] at h; simp at h
          have ⟨hvc, hT₁⟩ := ihEp G c ρ L T vc T₁ hc hρ hT h1
          cases vc with
          | bool b =>
            cases b with
            | false => simp at h; exact ihEp G e ρ L T₁ r T' he hρ hT₁ h
            | true => simp at h; exact ihEp G t ρ L T₁ r T' ht hρ hT₁ h
          | num _ => simp at h
          | prim _ => simp at h
          | bbApply => simp at h
          | clos _ _ _ => simp at h
          | list _ => simp at h
      | seq es =>
        simp [Expr.Pure] at hE
        simp [eval] at h
        exact ihSp G es ρ L T r T' hE hρ hT h
    -- EvalListIndep at n+1
    · unfold EvalListIndep
      intro G G' es ρ L T hEs hρ hT
      cases es with
      | nil => simp [evalList]
      | cons e es =>
        simp [ExprList.Pure] at hEs
        obtain ⟨he, hes⟩ := hEs
        simp only [evalList]
        rw [ihE G G' e ρ L T he hρ hT]
        cases h1 : eval G' n e ρ L T with
        | none => rfl
        | some pr =>
          obtain ⟨v, T₁⟩ := pr
          have ⟨hv, hT₁⟩ := ihEp G' e ρ L T v T₁ he hρ hT h1
          simp
          rw [ihL G G' es ρ L T₁ hes hρ hT₁]
    -- EvalListPres at n+1
    · unfold EvalListPres
      intro G es ρ L T vs T' hEs hρ hT h
      cases es with
      | nil =>
        simp [evalList] at h; obtain ⟨hvs, hT'⟩ := h
        rw [hvs, ← hT']
        exact ⟨by simp [ValList.Pure], hT⟩
      | cons e es =>
        simp [ExprList.Pure] at hEs
        obtain ⟨he, hes⟩ := hEs
        simp [evalList] at h
        cases h1 : eval G n e ρ L T with
        | none => rw [h1] at h; simp at h
        | some pr =>
          obtain ⟨v, T₁⟩ := pr
          rw [h1] at h; simp at h
          have ⟨hv, hT₁⟩ := ihEp G e ρ L T v T₁ he hρ hT h1
          cases h2 : evalList G n es ρ L T₁ with
          | none => rw [h2] at h; simp at h
          | some pr2 =>
            obtain ⟨vs', T₂⟩ := pr2
            rw [h2] at h; simp at h
            obtain ⟨hvs, hT'⟩ := h
            have ⟨hvs', hT₂⟩ := ihLp G es ρ L T₁ vs' T₂ hes hρ hT₁ h2
            rw [← hvs, ← hT']
            refine ⟨?_, hT₂⟩
            simp [ValList.Pure]
            exact ⟨hv, hvs'⟩
    -- EvalSeqIndep at n+1
    · unfold EvalSeqIndep
      intro G G' es ρ L T hEs hρ hT
      cases es with
      | nil => simp [evalSeq]
      | cons e es =>
        cases es with
        | nil =>
          simp [ExprList.Pure] at hEs
          simp [evalSeq]
          exact ihE G G' e ρ L T hEs hρ hT
        | cons e' es' =>
          simp [ExprList.Pure] at hEs
          obtain ⟨he, hes⟩ := hEs
          simp [evalSeq]
          rw [ihE G G' e ρ L T he hρ hT]
          cases h1 : eval G' n e ρ L T with
          | none => rfl
          | some pr =>
            obtain ⟨v, T₁⟩ := pr
            have ⟨hv, hT₁⟩ := ihEp G' e ρ L T v T₁ he hρ hT h1
            simp
            exact ihS G G' (e' :: es') ρ L T₁ (by simp [ExprList.Pure]; exact hes) hρ hT₁
    -- EvalSeqPres at n+1
    · unfold EvalSeqPres
      intro G es ρ L T r T' hEs hρ hT h
      cases es with
      | nil =>
        simp [evalSeq] at h
        obtain ⟨hr, hT'⟩ := h
        refine ⟨?_, hT' ▸ hT⟩
        rw [← hr]; simp [Val.Pure]
      | cons e es =>
        cases es with
        | nil =>
          simp [ExprList.Pure] at hEs
          simp [evalSeq] at h
          exact ihEp G e ρ L T r T' hEs hρ hT h
        | cons e' es' =>
          simp [ExprList.Pure] at hEs
          obtain ⟨he, hes⟩ := hEs
          simp [evalSeq] at h
          cases h1 : eval G n e ρ L T with
          | none => rw [h1] at h; simp at h
          | some pr =>
            obtain ⟨v, T₁⟩ := pr
            rw [h1] at h; simp at h
            have ⟨hv, hT₁⟩ := ihEp G e ρ L T v T₁ he hρ hT h1
            exact ihSp G (e' :: es') ρ L T₁ r T'
              (by simp [ExprList.Pure]; exact hes) hρ hT₁ h
    -- ApplyViaIndep at n+1
    · unfold ApplyViaIndep
      intro G G' dL op args T hop hargs hT
      simp only [applyVia]
      have hTmat : (T.materialize dL).Pure = true :=
        TowerState.materialize_Pure T dL hT
      have hdisp : ((T.materialize dL).applyAt dL).Pure = true :=
        TowerState.applyAt_Pure hTmat
      have hargs2 : ValList.Pure [op, .list args] = true := by
        simp [ValList.Pure, Val.Pure]; exact ⟨hop, hargs⟩
      generalize hd : (T.materialize dL).applyAt dL = disp at hdisp
      cases disp with
      | bbApply => exact ihD G G' op args (dL - 1) (T.materialize dL) hop hargs hTmat
      | num k =>
        exact ihD G G' (.num k) [op, .list args] (dL - 1) (T.materialize dL) hdisp hargs2 hTmat
      | bool b =>
        exact ihD G G' (.bool b) [op, .list args] (dL - 1) (T.materialize dL) hdisp hargs2 hTmat
      | prim p =>
        exact ihD G G' (.prim p) [op, .list args] (dL - 1) (T.materialize dL) hdisp hargs2 hTmat
      | clos xs body env_c =>
        exact ihD G G' (.clos xs body env_c) [op, .list args] (dL - 1) (T.materialize dL) hdisp hargs2 hTmat
      | list vs =>
        exact ihD G G' (.list vs) [op, .list args] (dL - 1) (T.materialize dL) hdisp hargs2 hTmat
    -- ApplyViaPres at n+1
    · unfold ApplyViaPres
      intro G dL op args T r T' hop hargs hT h
      simp only [applyVia] at h
      have hTmat : (T.materialize dL).Pure = true :=
        TowerState.materialize_Pure T dL hT
      have hdisp : ((T.materialize dL).applyAt dL).Pure = true :=
        TowerState.applyAt_Pure hTmat
      have hargs2 : ValList.Pure [op, .list args] = true := by
        simp [ValList.Pure, Val.Pure]; exact ⟨hop, hargs⟩
      generalize hd : (T.materialize dL).applyAt dL = disp at h hdisp
      cases disp with
      | bbApply =>
        exact ihDp G op args (dL - 1) (T.materialize dL) r T' hop hargs hTmat h
      | num k =>
        exact ihDp G (.num k) [op, .list args] (dL - 1) (T.materialize dL) r T'
          hdisp hargs2 hTmat h
      | bool b =>
        exact ihDp G (.bool b) [op, .list args] (dL - 1) (T.materialize dL) r T'
          hdisp hargs2 hTmat h
      | prim p =>
        exact ihDp G (.prim p) [op, .list args] (dL - 1) (T.materialize dL) r T'
          hdisp hargs2 hTmat h
      | clos xs body env_c =>
        exact ihDp G (.clos xs body env_c) [op, .list args] (dL - 1) (T.materialize dL) r T'
          hdisp hargs2 hTmat h
      | list vs =>
        exact ihDp G (.list vs) [op, .list args] (dL - 1) (T.materialize dL) r T'
          hdisp hargs2 hTmat h
    -- ApplyDirectIndep at n+1
    · unfold ApplyDirectIndep
      intro G G' op args L T hop hargs hT
      cases op with
      | num _ => simp [applyDirect]
      | bool _ => simp [applyDirect]
      | list _ => simp [applyDirect]
      | prim p => simp [applyDirect]
      | clos xs body env_c =>
        simp [Val.Pure] at hop
        simp [applyDirect]
        cases h : env_c.extend xs args with
        | none => rfl
        | some ρ' =>
          simp
          have hρ' := Env.extend_Pure xs args hop.2 hargs h
          exact ihE G G' body ρ' L T hop.1 hρ' hT
      | bbApply =>
        cases args with
        | nil => simp [applyDirect]
        | cons a tl =>
          cases tl with
          | nil => simp [applyDirect]
          | cons b tt =>
            cases tt with
            | nil =>
              cases b with
              | list args' =>
                simp [applyDirect]
                simp [ValList.Pure] at hargs
                simp [Val.Pure] at hargs
                exact ihD G G' a args' L T hargs.1 hargs.2 hT
              | num _ => simp [applyDirect]
              | bool _ => simp [applyDirect]
              | prim _ => simp [applyDirect]
              | bbApply => simp [applyDirect]
              | clos _ _ _ => simp [applyDirect]
            | cons _ _ => simp [applyDirect]
    -- ApplyDirectPres at n+1
    · unfold ApplyDirectPres
      intro G op args L T r T' hop hargs hT h
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
          rw [← hr, ← hT']
          exact ⟨applyPrim_Pure hp, hT⟩
      | clos xs body env_c =>
        simp [Val.Pure] at hop
        simp [applyDirect] at h
        cases hext : env_c.extend xs args with
        | none => rw [hext] at h; simp at h
        | some ρ' =>
          rw [hext] at h; simp at h
          have hρ' := Env.extend_Pure xs args hop.2 hargs hext
          exact ihEp G body ρ' L T r T' hop.1 hρ' hT h
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
                simp [ValList.Pure] at hargs
                simp [Val.Pure] at hargs
                exact ihDp G a args' L T r T' hargs.1 hargs.2 hT h
              | num _ => simp [applyDirect] at h
              | bool _ => simp [applyDirect] at h
              | prim _ => simp [applyDirect] at h
              | bbApply => simp [applyDirect] at h
              | clos _ _ _ => simp [applyDirect] at h
            | cons _ _ => simp [applyDirect] at h

/-- The headline corollary: gate-independence for pure expressions. -/
theorem eval_pure_gate_indep (G G' : Gate) (n : Nat) (e : Expr) (ρ : Env)
    (L : Nat) (T : TowerState)
    (hE : e.Pure = true) (hρ : ρ.Pure = true) (hT : T.Pure = true) :
    eval G n e ρ L T = eval G' n e ρ L T :=
  (joint n).1 G G' e ρ L T hE hρ hT

/-- Pure inputs propagate through to outputs. -/
theorem eval_pure_preserve (G : Gate) (n : Nat) (e : Expr) (ρ : Env)
    (L : Nat) (T : TowerState) (r : Val) (T' : TowerState)
    (hE : e.Pure = true) (hρ : ρ.Pure = true) (hT : T.Pure = true)
    (h : eval G n e ρ L T = some (r, T')) :
    r.Pure = true ∧ T'.Pure = true :=
  (joint n).2.1 G e ρ L T r T' hE hρ hT h

/-! ## β-redex strengthening via AllPureIndep

Given any pair of pure terms `M`, `N` whose evaluations agree at some
gate `G` at the initial state, they agree at *every* gate. The proof
is immediate from `eval_pure_gate_indep`: each side of the equality is
gate-independent for pure inputs, so swapping `G` for `G'` preserves
both sides. -/

theorem initEnv_Pure : initEnv.Pure = true := by
  simp [initEnv, Env.Pure, Val.Pure]

theorem initTower_Pure : initTower.Pure = true := by
  simp [initTower, TowerState.Pure, Level.Pure, Val.Pure]

theorem pure_pair_equality_gate_indep (n : Nat) (M N : Expr)
    (hM : M.Pure = true) (hN : N.Pure = true) (G G' : Gate)
    (h : ∀ T₀, T₀.Pure = true →
         eval G n M initEnv 0 T₀ = eval G n N initEnv 0 T₀) :
    ∀ T₀, T₀.Pure = true →
      eval G' n M initEnv 0 T₀ = eval G' n N initEnv 0 T₀ := by
  intro T₀ hT₀
  rw [← eval_pure_gate_indep G G' n M initEnv 0 T₀ hM initEnv_Pure hT₀]
  rw [← eval_pure_gate_indep G G' n N initEnv 0 T₀ hN initEnv_Pure hT₀]
  exact h T₀ hT₀

end LeanEmerald

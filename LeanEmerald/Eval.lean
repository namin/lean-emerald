import LeanEmerald.Syntax

/-!
# Evaluator — fuel-indexed, big-step, tower-threading

`eval` takes:

* `fuel : Nat`
* `e    : Expr`
* `ρ    : Env`
* `L    : Nat` — the current reflective level
* `T    : TowerState`

and returns `Option (Val × TowerState)`. The tower threads through every
clause because `set!` mutations can happen inside any sub-evaluation.

## The dispatch story in one screen

* `.app f args` at level `L` evaluates `f` and `args`, then calls
  `applyVia` *at dispatch level* `L+1`.

* `applyVia (L+1) op args T` consults `T[L+1].apply`. If it's `.bbApply`,
  it falls through to `applyDirect op args` — the operator dispatches
  itself (closure body or primitive call). If it's any other value, that
  value is treated as a **wrapper closure** and invoked with the
  bundled call `(op, .list args)`.

* `.em e` at level `L` evaluates `e` at level `L+1`, materializing
  level `L+1` on the way in if it doesn't exist yet.

* `.setApply e` at level `L` evaluates `e` to `vNew` and stores it in
  `T[L+1].apply`. (Slice 2 admits unconditionally; slice 3 consults the
  policy.)

This is the Black convention. A wrapper installed at level 1 (via a
`setApply` at level 0) handles applications coming from level 0. The
wrapper's body, executing at level 0, must use `(em ...)` to escape its
own dispatcher when it wants to delegate to a more-fundamental rule —
otherwise it loops.
-/

namespace LeanEmerald

/-! ## Environment helpers -/

def Env.lookup : Env → String → Option Val
  | .nil,        _ => none
  | .cons y v ρ, x => if x = y then some v else ρ.lookup x

/-- Extend an env by zipping a parameter list with an argument list. -/
def Env.extend : Env → List String → List Val → Option Env
  | ρ, [],      []      => some ρ
  | ρ, x :: xs, v :: vs => Env.extend (.cons x v ρ) xs vs
  | _, _ :: _,  []      => none
  | _, [],      _ :: _  => none

/-! ## Primitive application

Primitives are pure value-level functions. -/

def applyPrim : Prim → List Val → Option Val
  | .add,     [.num a, .num b]  => some (.num (a + b))
  | .mul,     [.num a, .num b]  => some (.num (a * b))
  | .sub,     [.num a, .num b]  => some (.num (a - b))
  | .eq,      [.num a, .num b]  => some (.bool (a = b))
  | .isNum,   [.num _]          => some (.bool true)
  | .isNum,   [_]               => some (.bool false)
  | .foldMul, [.num a, .list l] =>
      -- multiply `a` by every `.num` element of `l`;
      -- fail if any element isn't a `.num`.
      match l.foldlM (fun acc v => match v with
                                    | .num k => some (acc * k)
                                    | _      => none) a with
      | some n => some (.num n)
      | none   => none
  | _,        _                 => none

/-! ## Initial env — primitives by name

`+`, `*`, `-`, `=` bind to primitive Vals. `isNum?` and `foldMul` are
exposed for use inside user-written wrappers (e.g., multn). -/

def initEnv : Env :=
  .cons "+"       (.prim .add)     <|
  .cons "*"       (.prim .mul)     <|
  .cons "-"       (.prim .sub)     <|
  .cons "="       (.prim .eq)      <|
  .cons "isNum?"  (.prim .isNum)   <|
  .cons "foldMul" (.prim .foldMul) <|
  .nil

/-! ## Tower helpers

We use `Option`-returning lookups and a default cell, so no index-bounds
proof obligations leak into the evaluator. -/

/-- The fresh-level default. -/
def defaultLevel : Level := { apply := .bbApply, policy := .bool true }

/-- Materialize the tower up to (and including) index `k`. -/
def TowerState.materialize (T : TowerState) (k : Nat) : TowerState :=
  if T.length > k then T
  else T ++ List.replicate (k + 1 - T.length) defaultLevel

/-- Read level `k`'s apply cell, with default if absent. -/
def TowerState.applyAt (T : TowerState) (k : Nat) : Val :=
  match T[k]? with
  | some lvl => lvl.apply
  | none     => defaultLevel.apply

/-- Read level `k`'s policy cell, with default if absent. -/
def TowerState.policyAt (T : TowerState) (k : Nat) : Val :=
  match T[k]? with
  | some lvl => lvl.policy
  | none     => defaultLevel.policy

/-- Update a single level's apply cell. Materializes first. -/
def TowerState.setApplyAt (T : TowerState) (k : Nat) (v : Val) : TowerState :=
  let T' := T.materialize k
  T'.set k { (T'[k]?.getD defaultLevel) with apply := v }

/-- Update a single level's policy cell. Materializes first. -/
def TowerState.setPolicyAt (T : TowerState) (k : Nat) (v : Val) : TowerState :=
  let T' := T.materialize k
  T'.set k { (T'[k]?.getD defaultLevel) with policy := v }

/-- The initial tower has level 0 materialized with default cells. -/
def initTower : TowerState :=
  [{ apply := .bbApply, policy := .bool true }]

/-! ## The gate

The evaluator carries a `Gate` — a Boolean decision function consulted at
every `.setApply` and `.setPolicy`. The signature is

    Gate := callerLevel → oldVal → newVal → Bool

where `callerLevel` is the source level of the `set!` (the dispatcher cell
modified sits at `callerLevel + 1`). Slice 2's smoke uses `acceptAll`,
which is unconditional. Slice 3's `mkGate` (in `CE.lean`) constructs a
gate from a list of `ApprovedModification`s. -/

abbrev Gate : Type := Nat → Val → Val → Bool

def acceptAll : Gate := fun _ _ _ => true
def rejectAll : Gate := fun _ _ _ => false

/-! ## The evaluator

Parameterized by the gate. The `.setApply` and `.setPolicy` rules read the
current cell value, consult `gate callerLevel oldVal newVal`, and only
commit the mutation if the gate returns `true`. A refused modification
returns `.bool false` and leaves the tower unchanged. -/

mutual

def eval (G : Gate) : Nat → Expr → Env → Nat → TowerState
                       → Option (Val × TowerState)
  | 0,   _,             _, _, _ => none
  | _+1, .lit v,        _, _, T => some (v, T)
  | _+1, .var x,        ρ, _, T => (ρ.lookup x).map (·, T)
  | _+1, .lam xs body,  ρ, _, T => some (.clos xs body ρ, T)
  | n+1, .app f args,   ρ, L, T => do
      let (vf, T₁) ← eval G n f ρ L T
      let (vs, T₂) ← evalList G n args ρ L T₁
      applyVia G n (L + 1) vf vs T₂
  | n+1, .appDirect f args, ρ, L, T => do
      let (vf, T₁) ← eval G n f ρ L T
      let (vs, T₂) ← evalList G n args ρ L T₁
      applyDirect G n vf vs L T₂
  | n+1, .em e,         ρ, L, T => do
      let T_mat := T.materialize (L + 1)
      eval G n e ρ (L + 1) T_mat
  | n+1, .setApply e,   ρ, L, T => do
      let (vNew, T₁) ← eval G n e ρ L T
      let oldVal := T₁.applyAt (L + 1)
      if G L oldVal vNew then
        some (.bool true,  T₁.setApplyAt (L + 1) vNew)
      else
        some (.bool false, T₁)
  | n+1, .setPolicy e,  ρ, L, T => do
      let (vNew, T₁) ← eval G n e ρ L T
      let oldVal := T₁.policyAt (L + 1)
      if G L oldVal vNew then
        some (.bool true,  T₁.setPolicyAt (L + 1) vNew)
      else
        some (.bool false, T₁)
  | n+1, .ifte c t e,   ρ, L, T => do
      let (vc, T₁) ← eval G n c ρ L T
      match vc with
      | .bool true  => eval G n t ρ L T₁
      | .bool false => eval G n e ρ L T₁
      | _           => none
  | n+1, .seq es,       ρ, L, T => evalSeq G n es ρ L T

def evalList (G : Gate) : Nat → List Expr → Env → Nat → TowerState
                           → Option (List Val × TowerState)
  | 0,   _,       _, _, _ => none
  | _+1, [],      _, _, T => some ([], T)
  | n+1, e :: es, ρ, L, T => do
      let (v,  T₁) ← eval G n e ρ L T
      let (vs, T₂) ← evalList G n es ρ L T₁
      some (v :: vs, T₂)

def evalSeq (G : Gate) : Nat → List Expr → Env → Nat → TowerState
                          → Option (Val × TowerState)
  | 0,   _,       _, _, _ => none
  | _+1, [],      _, _, T => some (.bool true, T)
  | n+1, [e],     ρ, L, T => eval G n e ρ L T
  | n+1, e :: es, ρ, L, T => do
      let (_, T₁) ← eval G n e ρ L T
      evalSeq G n es ρ L T₁

def applyVia (G : Gate) : Nat → Nat → Val → List Val → TowerState
                            → Option (Val × TowerState)
  | 0,   _,        _,  _,  _ => none
  | n+1, dispLevel, op, args, T =>
      let T_mat := T.materialize dispLevel
      let dispatcher := T_mat.applyAt dispLevel
      match dispatcher with
      | .bbApply =>
          applyDirect G n op args (dispLevel - 1) T_mat
      | _ =>
          applyDirect G n dispatcher [op, .list args] (dispLevel - 1) T_mat

def applyDirect (G : Gate) : Nat → Val → List Val → Nat → TowerState
                              → Option (Val × TowerState)
  | 0,   _,                  _,  _, _ => none
  | n+1, .clos xs body ρ_cap, vs, L, T => do
      let ρ' ← ρ_cap.extend xs vs
      eval G n body ρ' L T
  | _+1, .prim p,             vs, _, T => do
      let v ← applyPrim p vs
      some (v, T)
  -- bbApply called in the wrapper-invocation convention
  -- `bbApply [op, .list args]` means "default-dispatch op on args".
  -- This is the form a wrapper's `orig` use takes when `orig = bbApply`.
  | n+1, .bbApply, [op_val, .list args_val], L, T =>
      applyDirect G n op_val args_val L T
  | _+1, _,                   _,  _, _ => none

end

/-! ## Convenience: run a closed expression in the initial state.

Defaults to `acceptAll` for the gate; callers can pass an explicit gate. -/

def evalProgram (n : Nat) (e : Expr) (G : Gate := acceptAll) : Option Val :=
  (eval G n e initEnv 0 initTower).map (·.1)

def evalProgramFull (n : Nat) (e : Expr) (G : Gate := acceptAll)
    : Option (Val × TowerState) :=
  eval G n e initEnv 0 initTower

/-! ## Smoke scenes — sample programs used by the runtime smoke runner

Static `rfl` checks aren't free for a fuel-indexed mutually-recursive
evaluator (well-founded recursion in Lean doesn't unfold by definition).
Instead we expose the sample programs as named `def`s here, and the runtime
smoke executable in `Smoke.lean` evaluates them and checks results. -/

namespace Sample

-- Slice 1: pure subset.

/-- `(+ 1 2)` -/
def add12 : Expr := .app (.var "+") [.lit (.num 1), .lit (.num 2)]

/-- `((λx. x) 0)` — the canonical β-redex. -/
def betaIdZero : Expr :=
  .app (.lam ["x"] (.var "x")) [.lit (.num 0)]

/-- `((λx. x*x) 3)` -/
def squareOf3 : Expr :=
  .app (.lam ["x"] (.app (.var "*") [.var "x", .var "x"]))
       [.lit (.num 3)]

/-- `if (= 1 1) then 42 else 0` -/
def ifEq : Expr :=
  .ifte (.app (.var "=") [.lit (.num 1), .lit (.num 1)])
        (.lit (.num 42))
        (.lit (.num 0))

-- Slice 2: tower.

/-- `(em (+ 1 2))` — em shifts up but pure code is unaffected. -/
def em_add : Expr := .em (.app (.var "+") [.lit (.num 1), .lit (.num 2)])

/-- `λ(op args). 42` — a constant wrapper. -/
def const42Wrapper : Expr :=
  .lam ["op", "args"] (.lit (.num 42))

/-- Install the const-42 wrapper at level 1, then evaluate `(+ 5 6)` at
    level 0 — should now dispatch via the wrapper and return 42. -/
def installAndCall : Expr :=
  .seq [.setApply const42Wrapper,
        .app (.var "+") [.lit (.num 5), .lit (.num 6)]]

/-- Same install, but the call is wrapped in `(em ...)` — escapes the
    wrapper, dispatches via level 2 (bbApply, lazily materialized),
    returns 11. -/
def installThenEm : Expr :=
  .seq [.setApply const42Wrapper,
        .em (.app (.var "+") [.lit (.num 5), .lit (.num 6)])]

-- Slice 3: refused setApply under empty-approval gate.

/-- Attempt to install the const-42 wrapper, then call `(+ 5 6)`.
    With `rejectAll` (or `mkGate []`), the setApply is refused — it
    returns `.bool false` and leaves the tower unchanged. The
    subsequent `(+ 5 6)` then takes the unmodified path and yields 11. -/
def refusedInstallThenAdd : Expr :=
  .seq [.setApply const42Wrapper,
        .app (.var "+") [.lit (.num 5), .lit (.num 6)]]

/-- Same but observe the setApply's return value to verify refusal
    explicitly: returns `.bool false`. -/
def refusedSetApplyReturns : Expr :=
  .setApply const42Wrapper

end Sample

end LeanEmerald

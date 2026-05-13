/-!
# Syntax — values, expressions, environments, tower states

Everything-typed in one place. The data definitions in this file are the full
substrate; the evaluator in `Eval.lean` interprets them.

## Design notes

* **Closures capture by value.** A `.clos params body env` carries its capture
  environment as data, not as heap indices. No global heap, no re-indexing,
  no shift apparatus.

* **The reflective tower is a list of levels.** Each `Level` carries an
  `apply` cell (the base-apply rule for that level) and a `policy` cell
  (the admission gate, used from slice 3 onward). Both cells are ordinary
  `Val`s — mutability comes from the evaluator updating the list, not from
  any in-place state.

* **Application dispatches via the apply cell *one level up*.** A call
  `(op args)` at level `L` consults `tower[L+1].apply`. To modify how level
  `L` dispatches, you `set! base-apply ...` at level `L`, which writes to
  `tower[L+1].apply`. To modify how level `L+1` dispatches, you wrap that in
  `(em ...)`. This is the Black convention, with the meta-env of level `L`
  understood as level `L+1`'s data.

* **β is operational.** The `.app` rule, when its operator evaluates to a
  closure, extends the closure's captured env with the argument bindings and
  evaluates the body. β-equivalence on closed pure terms then follows from
  `eval` agreement, not from a separate bisim relation.
-/

namespace LeanEmerald

mutual

/-- Runtime values. -/
inductive Val : Type where
  /-- Integer literal. -/
  | num     : Int → Val
  /-- Boolean literal. -/
  | bool    : Bool → Val
  /-- Built-in primitive, identified by tag. -/
  | prim    : Prim → Val
  /-- Closure: formal parameters, body, captured environment. -/
  | clos    : List String → Expr → Env → Val
  /-- The default base-apply rule. Sits in every freshly-materialized
      `Level.apply` cell; semantically, dispatches the operator directly
      (closure body or primitive call). -/
  | bbApply : Val
  /-- A heterogeneous list of values. Used to package a call's argument
      list as a single value when invoking a user-installed apply wrapper:
      a wrapper has signature `(op, args)` where `args : Val` is a
      `.list`-packaged list. -/
  | list    : List Val → Val

/-- Expressions. -/
inductive Expr : Type where
  /-- Literal value. -/
  | lit       : Val → Expr
  /-- Variable reference. -/
  | var       : String → Expr
  /-- Lambda abstraction. -/
  | lam       : List String → Expr → Expr
  /-- Application `(f a₁ … aₙ)`. Dispatches via the tower's apply cell. -/
  | app       : Expr → List Expr → Expr
  /-- Direct application: skips the tower's apply cell entirely and
      invokes `applyDirect` on `f`'s value. Used inside wrapper bodies
      to call sub-operations (`isNum?`, the captured `orig`, etc.)
      without recursing through the wrapper itself. -/
  | appDirect : Expr → List Expr → Expr
  /-- Reflective shift: `(em e)` at level `L` evaluates `e` at level `L+1`. -/
  | em        : Expr → Expr
  /-- `set! base-apply e` at level `L` writes the result of `e` into
      `tower[L+1].apply`. -/
  | setApply  : Expr → Expr
  /-- `set! policy e` at level `L` writes the result of `e` into
      `tower[L+1].policy`. Used from slice 3. -/
  | setPolicy : Expr → Expr
  /-- Conditional. -/
  | ifte      : Expr → Expr → Expr → Expr
  /-- Sequence: evaluate each in order, return the last value. The tower
      threads through, so this is how you write "install then call"
      without an enclosing application that would be caught by the
      newly-installed wrapper. -/
  | seq       : List Expr → Expr

/-- Value environments. -/
inductive Env : Type where
  | nil  : Env
  | cons : String → Val → Env → Env

/-- Primitive operations. -/
inductive Prim : Type where
  /-- Integer addition. -/
  | add
  /-- Integer multiplication. -/
  | mul
  /-- Integer subtraction. -/
  | sub
  /-- Integer equality (returns a `.bool`). -/
  | eq
  /-- Test whether a value is `.num`. -/
  | isNum
  /-- Fold-multiply: `(foldMul x xs)` multiplies `x` by every element of
      the `.list`-packaged `xs`, returning a `.num`. Used by the multn
      worked example. -/
  | foldMul

end

/-! ## Structural `beq` over `Val`, `Expr`, `Env`

A mutually-recursive Boolean equality. Used at the admission gate to
compare a runtime modification's `newVal` against an approval's recorded
`new`. Conservative: closures compare structurally on params + body + env. -/

def Prim.beq : Prim → Prim → Bool
  | .add,     .add     => true
  | .mul,     .mul     => true
  | .sub,     .sub     => true
  | .eq,      .eq      => true
  | .isNum,   .isNum   => true
  | .foldMul, .foldMul => true
  | _,        _        => false

mutual

def Val.beq : Val → Val → Bool
  | .num a,           .num b           => a == b
  | .bool a,          .bool b          => a == b
  | .prim p,          .prim q          => Prim.beq p q
  | .bbApply,         .bbApply         => true
  | .clos xs b ρ,     .clos ys b' ρ'   => xs == ys && Expr.beq b b' && Env.beq ρ ρ'
  | .list l1,         .list l2         => Val.listBeq l1 l2
  | _,                _                => false

def Val.listBeq : List Val → List Val → Bool
  | [],       []       => true
  | v1 :: l1, v2 :: l2 => Val.beq v1 v2 && Val.listBeq l1 l2
  | _,        _        => false

def Expr.beq : Expr → Expr → Bool
  | .lit v1,        .lit v2        => Val.beq v1 v2
  | .var x,         .var y         => x == y
  | .lam xs1 b1,    .lam xs2 b2    => xs1 == xs2 && Expr.beq b1 b2
  | .app f1 as1,    .app f2 as2    => Expr.beq f1 f2 && Expr.listBeq as1 as2
  | .appDirect f1 as1, .appDirect f2 as2 => Expr.beq f1 f2 && Expr.listBeq as1 as2
  | .em e1,         .em e2         => Expr.beq e1 e2
  | .setApply e1,   .setApply e2   => Expr.beq e1 e2
  | .setPolicy e1,  .setPolicy e2  => Expr.beq e1 e2
  | .ifte c1 t1 e1, .ifte c2 t2 e2 => Expr.beq c1 c2 && Expr.beq t1 t2 && Expr.beq e1 e2
  | .seq es1,       .seq es2       => Expr.listBeq es1 es2
  | _,              _              => false

def Expr.listBeq : List Expr → List Expr → Bool
  | [],       []       => true
  | e1 :: l1, e2 :: l2 => Expr.beq e1 e2 && Expr.listBeq l1 l2
  | _,        _        => false

def Env.beq : Env → Env → Bool
  | .nil,           .nil           => true
  | .cons x1 v1 ρ1, .cons x2 v2 ρ2 => x1 == x2 && Val.beq v1 v2 && Env.beq ρ1 ρ2
  | _,              _              => false

end

/-! ## Per-level state and tower -/

/-- One level of the reflective tower. Both fields are ordinary `Val`s. -/
structure Level where
  /-- The base-apply rule. `.bbApply` is the default. -/
  apply  : Val
  /-- The admission policy. From slice 3; in earlier slices it is
      unused. The default is `.bool true` (accept-all). -/
  policy : Val

/-- The tower state is just a list of levels. `abbrev` so List ops resolve. -/
abbrev TowerState : Type := List Level

end LeanEmerald

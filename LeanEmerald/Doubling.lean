import LeanEmerald.Multn

/-!
# Doubling — runtime wrapper composition on top of multn

A `doubling` wrapper that captures `multn` as its `orig` cell, then
doubles numeric results. Demonstrates that wrappers compose at the
*runtime* level: two `set! base-apply` modifications in sequence,
each producing observable behavior in the final program. This is
operational composition, not proof-bearing admission — under the
proof gate, doubling is filtered out (see below).

Under `acceptAll`, both installs are admitted unconditionally; under
the proof-bearing gate built from `[multnApproval]`, the doubling
install is refused (no approval matches its structural shape), but
the multn install still succeeds.

## What this is *not*

Doubling does not conservatively extend `bbApply`: `(+ 1 2) ⇒ 3`
under baseline but `(+ 1 2) ⇒ 6` under doubling. So no `CE 0 doublingClos`
proof can exist — this is the theorem `not_CE_doublingClos` in
`DoublingNotCE.lean` — and doubling can only be admitted under `acceptAll`
(or a custom gate that doesn't demand CE).

## Wrapper body

The doubling body, written informally:

```
λ(op, args).
  let result = (orig op args) in
  if (isNum? result) then (+ result result) else result
```

We don't have `let` directly, so we use the closure-as-let idiom
`((λresult. body) (orig op args))`, dispatched via `.appDirect` to
avoid wrapper self-recursion. -/

namespace LeanEmerald

/-! ## The doubling closure -/

/-- Captured environment for doubling: `orig = multnClos` (capture the
    previously-installed wrapper), plus `+` and `isNum?` for the body. -/
def doublingCapEnv : Env :=
  .cons "+"      (.prim .add)    <|
  .cons "isNum?" (.prim .isNum)  <|
  .cons "orig"   multnClos       <|
  .nil

/-- Doubling body. `((λresult. ifte (isNum? result) (+ result result) result)
    (orig op args))`, dispatched via `.appDirect` everywhere. -/
def doublingBody : Expr :=
  .appDirect
    (.lam ["result"]
      (.ifte (.appDirect (.var "isNum?") [.var "result"])
             (.appDirect (.var "+") [.var "result", .var "result"])
             (.var "result")))
    [.appDirect (.var "orig") [.var "op", .var "args"]]

def doublingClos : Val :=
  .clos ["op", "args"] doublingBody doublingCapEnv

/-! ## Demos -/

namespace Demo

/-- Install multn at level 0, then install doubling at level 0 (which
    captures multn as orig in its env). Then call `(2 3 4)`. Expected
    under `acceptAll`: 48 — multn yields 24, doubling yields 48. -/
def composeMultnThenDouble_nums : Expr :=
  .seq [.setApply (.lit multnClos),
        .setApply (.lit doublingClos),
        .app (.lit (.num 2)) [.lit (.num 3), .lit (.num 4)]]

/-- Same composition; call `(+ 1 2)`. Expected: 6 — multn falls through
    `orig=bbApply` to `+`, giving 3; doubling doubles to 6. -/
def composeMultnThenDouble_add : Expr :=
  .seq [.setApply (.lit multnClos),
        .setApply (.lit doublingClos),
        .app (.var "+") [.lit (.num 1), .lit (.num 2)]]

end Demo

end LeanEmerald

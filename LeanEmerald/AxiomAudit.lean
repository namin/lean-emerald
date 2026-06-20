import LeanEmerald.Substrate
import LeanEmerald.Soundness
import LeanEmerald.Multn
import LeanEmerald.SubstrateBehaviorFull
import LeanEmerald.DoublingNotCE

/-!
# Axiom audit

Machine-witnesses that lean-emerald's headline results rest only on the Lean
kernel plus the standard classical axioms — crucially, **no `Lean.ofReduceBool`**
(the axiom `native_decide` injects to trust the compiler instead of the kernel)
and no `sorryAx`. Each `#guard_msgs in #print axioms …` pins the exact footprint,
so the build fails the moment any audited theorem acquires a new axiom.
-/

namespace LeanEmerald

/-- info: 'LeanEmerald.CE_bbApply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CE_bbApply

/-- info: 'LeanEmerald.mkGate_admits_CE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mkGate_admits_CE

/-- info: 'LeanEmerald.multnCE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms multnCE

/-- info: 'LeanEmerald.betaIdZero_gate_indep_keynote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms betaIdZero_gate_indep_keynote

/-- info: 'LeanEmerald.eval_pure_gate_indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_pure_gate_indep

/-- info: 'LeanEmerald.substrate_behavioral_CE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms substrate_behavioral_CE

/-- info: 'LeanEmerald.jointInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms jointInv

/-- info: 'LeanEmerald.applyVia_substrate_extends_baseline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms applyVia_substrate_extends_baseline

/-- info: 'LeanEmerald.not_CE_doublingClos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_CE_doublingClos

end LeanEmerald

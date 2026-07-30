import TwoControl.Clifford.Universal.GateSets

namespace TwoControl
namespace Clifford
namespace Lemma12

open Universal

/-!
Shared `{H,T}` one-qubit circuit type for the Lemma 12 `G₁/G₂` chain.

`G1G2/RzApprox.lean` constructs concrete `HTCircuit`s and the final Lemma 12
wrapper reads their matrix semantics through `HTCircuit.eval`.

This file stays small: it depends only on the project's
`OneQubitHTPrimitive` alphabet.
-/

/-- `{H,T}` circuits for the Lemma 12 branch. -/
abbrev HTCircuit := List OneQubitHTPrimitive

namespace HTCircuit

/-- Matrix semantics of an `{H,T}` circuit. -/
noncomputable def eval (gates : HTCircuit) : Square 2 :=
  oneQubitHTCircuitMatrix gates

@[simp] theorem eval_nil : eval [] = (1 : Square 2) := by
  rfl

@[simp] theorem eval_cons (gate : OneQubitHTPrimitive) (gates : HTCircuit) :
    eval (gate :: gates) = OneQubitHTPrimitive.eval gate * eval gates := by
  rfl

end HTCircuit

/-- Each one-qubit `{H,T}` primitive is unitary. -/
theorem oneQubitHTPrimitive_eval_mem_unitaryGroup
    (gate : OneQubitHTPrimitive) :
    OneQubitHTPrimitive.eval gate ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  cases gate
  · exact hadamard2_mem_unitaryGroup
  · exact phaseT_mem_unitaryGroup

/-- Every `{H,T}` circuit evaluates to a unitary matrix. -/
theorem HTCircuit_eval_mem_unitaryGroup
    (gates : HTCircuit) :
    HTCircuit.eval gates ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  induction gates with
  | nil =>
      simpa [HTCircuit.eval] using
        (Submonoid.one_mem (Matrix.unitaryGroup (Fin 2) ℂ))
  | cons gate gates ih =>
      simpa [HTCircuit.eval, oneQubitHTCircuitMatrix] using
        (Submonoid.mul_mem (Matrix.unitaryGroup (Fin 2) ℂ)
          (oneQubitHTPrimitive_eval_mem_unitaryGroup gate) ih)

end Lemma12
end Clifford
end TwoControl

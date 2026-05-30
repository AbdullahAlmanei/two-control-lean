import TwoControl.RossSelinger.Algorithm

namespace TwoControl.RossSelinger

/-!
Conditional correctness for the Ross-Selinger Rz-approximation algorithm:

> *If the algorithm returns a circuit, that circuit ε-approximates `Rz θ` in
> operator norm.*

The proof composes:

* candidate batches return `RSCandidate` certificates, so the selected `u`
  lies in Ross-Selinger's epsilon region;
* `RSCompletionSolver.sound` turns a returned `t` into the norm-equation
  certificate used by completion;
* `CompletedCandidate.synthesize` is the returned Ross/KMM branch circuit
  whose evaluation is certified to be the completion matrix;
* `MatrixCompletion.opDist_rz_completion_le_of_region` gives the operator
  norm bound.
-/

/-- **Conditional correctness** of the Ross-Selinger search: any circuit it
returns ε-approximates the requested `Rz` rotation in operator norm. -/
theorem rossSelingerSearch_sound_if_returns
    (solver : RSCompletionSolver)
    (fuel : ℕ)
    (input : RSInput) {C : CliffordTCircuit}
    (hrun : rossSelingerSearch solver fuel input = some C) :
    IsRzApproxCircuit input.θ input.ε C :=
  rossSelingerSearch_sound_if_returns' solver fuel input hrun

/-- **Conditional correctness** of the oracle variant: any circuit it returns
ε-approximates the requested `Rz` rotation in operator norm.  (Optimality is
proved separately in `Optimality.lean`.) -/
theorem rossSelingerOracleSearch_sound_if_returns
    (oracle : RSOracleSolver)
    (fuel : ℕ)
    (input : RSInput) {C : CliffordTCircuit}
    (hrun : rossSelingerOracleSearch oracle fuel input = some C) :
    IsRzApproxCircuit input.θ input.ε C := by
  exact rossSelingerSearch_sound_if_returns oracle.completionSolver fuel input hrun

end RossSelinger
end TwoControl

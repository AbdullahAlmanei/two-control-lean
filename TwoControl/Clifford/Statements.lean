import TwoControl.Clifford.Definitions
import TwoControl.CosineSine.Statements

open Matrix

namespace TwoControl
namespace Clifford

/-- Clifford-paper Lemma 3. -/
theorem lemma3_ry_via_rz (θ : ℝ) :
  CosineSine.ry θ = phaseSdagger * hadamard2 * rz (-θ) * hadamard2 * phaseS := by
  sorry

/-- Two-qubit specialization of Clifford-paper Lemma 4. -/
theorem lemma4_demultiplex_two_qubit (V₀ V₁ : Square 2)
    (hV₀ : V₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hV₁ : V₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (P Q : Square 2) (α₀ α₁ : ℝ),
      P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      CosineSine.blockDiag2 V₀ V₁ =
        localOnSecond Q * controlledRzPair α₀ α₁ * localOnSecond P := by
  sorry

/-- Exact one-qubit diagonalization, reusing the repo's existing helper theorem. -/
theorem one_qubit_diagonalization (U : Square 2)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (u₀ u₁ : ℂ) (V : Square 2),
      ‖u₀‖ = 1 ∧
      ‖u₁‖ = 1 ∧
      V ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      U = V * diag2 u₀ u₁ * V† := by
  simpa using unitary_diag2_exists U hU

/-- Paper-facing controlled-diagonal factorization from `lemmadiag`. -/
theorem controlled_diag_via_phase_and_controlled_rz (d₀ d₁ : ℂ)
    (hd₀ : ‖d₀‖ = 1) (hd₁ : ‖d₁‖ = 1) :
    ∃ (φ α : ℝ),
      controlledGate (diag2 d₀ d₁) =
        controlledGate (rz α) * localOnFirst (phaseShift φ) := by
  sorry

/-- Exact-synthesis corollary for the special controlled-`R_z` pairs used in Lemma 11. -/
theorem controlled_rz_pair_uses_standard_gates (α₀ α₁ : ℝ) :
    ∃ gates : List TwoQubitPrimitive,
      twoQubitCircuitMatrix gates = controlledRzPair α₀ α₁ := by
  sorry

/-- Derived one-qubit exact-synthesis corollary over `{H, T, R_z(θ)}`. -/
theorem one_qubit_exact_h_t_rz (U : Square 2)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ gates : List OneQubitPrimitive,
      oneQubitCircuitMatrix gates = U := by
  sorry

/-- Target theorem for the first Clifford-paper blueprint track. -/
theorem lemma11_two_qubit_synthesis (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ gates : List TwoQubitPrimitive,
      twoQubitCircuitMatrix gates = U := by
  sorry

end Clifford
end TwoControl

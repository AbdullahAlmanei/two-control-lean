import TwoControl.Section6

open scoped Matrix ComplexOrder
open Matrix

namespace TwoControl

/-- **Lemma 7.1** (Change a diagonal element to one.)
If `CC(Diag(u₀, u₁)) = W^{AB} · U` for a 2-qubit unitary `W` and a 3-qubit unitary `U`,
then there exists a 2-qubit unitary `V` such that `CC(Diag(1, u₀⋆ u₁)) = V^{AB} · U`. -/
lemma section7_lemma_7_1 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (W : Square 4) (hW : W ∈ unitaryGroup (Fin 4) ℂ)
    (U : Square 8) (hU : U ∈ unitaryGroup (Fin 8) ℂ)
    (h : ccu (diag2 u₀ u₁) = abgate W * U) :
    ∃ V : Square 4, V ∈ unitaryGroup (Fin 4) ℂ ∧
      ccu (diag2 1 (starRingEnd ℂ u₀ * u₁)) = abgate V * U := by
  sorry

/-- **Lemma 7.2** (Reduction to canonical forms.)
If a product of four `TwoQubitGate`s equals `CC(Diag(u₀, u₁))`, then there exist
2-qubit unitaries and parameters `(u₂, u₃) ∈ R(u₀, u₁)` achieving one of two
canonical gate-ordering patterns. -/
lemma section7_lemma_7_2 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (V₁ V₂ V₃ V₄ : Square 8)
    (hV₁ : TwoQubitGate V₁) (hV₂ : TwoQubitGate V₂)
    (hV₃ : TwoQubitGate V₃) (hV₄ : TwoQubitGate V₄)
    (h : V₁ * V₂ * V₃ * V₄ = ccu (diag2 u₀ u₁)) :
    ∃ u₂ u₃ : ℂ, ∃ U₁ U₂ U₃ U₄ : Square 4,
      inCanonicalPair u₀ u₁ u₂ u₃ ∧
      U₁ ∈ unitaryGroup (Fin 4) ℂ ∧
      U₂ ∈ unitaryGroup (Fin 4) ℂ ∧
      U₃ ∈ unitaryGroup (Fin 4) ℂ ∧
      U₄ ∈ unitaryGroup (Fin 4) ℂ ∧
      (bcgate U₁ * acgate U₂ * abgate U₃ * bcgate U₄ = ccu (diag2 u₂ u₃) ∨
       acgate U₁ * bcgate U₂ * acgate U₃ * bcgate U₄ = ccu (diag2 u₂ u₃)) := by
  sorry

/-- **Lemma 7.3** (Lifting the eigenvalue condition through `R`.)
If `(u₂, u₃) ∈ R(u₀, u₁)` and `u₂ = u₃ ∨ u₂ u₃ = 1`,
then `u₀ = u₁ ∨ u₀ u₁ = 1`. -/
lemma section7_lemma_7_3 (u₀ u₁ u₂ u₃ : ℂ)
    (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (hR : inCanonicalPair u₀ u₁ u₂ u₃)
    (h : u₂ = u₃ ∨ u₂ * u₃ = 1) :
    u₀ = u₁ ∨ u₀ * u₁ = 1 := by
  sorry

/-- **Theorem 7.4** (Main result for a diagonal matrix.)
A product of four `TwoQubitGate`s equals `CC(Diag(u₀, u₁))`
if and only if `u₀ = u₁` or `u₀ u₁ = 1`. -/
theorem section7_theorem_7_4 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ V₁ V₂ V₃ V₄ : Square 8,
      TwoQubitGate V₁ ∧ TwoQubitGate V₂ ∧ TwoQubitGate V₃ ∧ TwoQubitGate V₄ ∧
      V₁ * V₂ * V₃ * V₄ = ccu (diag2 u₀ u₁)) ↔
    (u₀ = u₁ ∨ u₀ * u₁ = 1) := by
  sorry

/-- **Corollary 7.5** (Main result for a gate with two controls.)
A product of four `TwoQubitGate`s equals `CC(U)` for a 1-qubit unitary `U`
if and only if `U` is a scalar matrix or `det U = 1`. -/
theorem section7_corollary_7_5 (U : Square 2) (hU : U ∈ unitaryGroup (Fin 2) ℂ) :
    (∃ V₁ V₂ V₃ V₄ : Square 8,
      TwoQubitGate V₁ ∧ TwoQubitGate V₂ ∧ TwoQubitGate V₃ ∧ TwoQubitGate V₄ ∧
      V₁ * V₂ * V₃ * V₄ = ccu U) ↔
    ((∃ c : ℂ, U = c • (1 : Square 2)) ∨ det U = 1) := by
  sorry

end TwoControl

import TwoControl.Definitions

open scoped Matrix ComplexOrder
open Matrix

namespace TwoControl

/-- **Lemma 3.1** (Commutativity characterization).
    Suppose `u₀, u₁` are unit complex numbers.
    An 8×8 unitary `U` commutes with `Diag(u₀, u₁) ⊗ I₂ ⊗ I₂`
    if and only if either `u₀ = u₁` or
    `U = |0⟩⟨0| ⊗ V₀₀ + |1⟩⟨1| ⊗ V₁₁`
    for some 4×4 unitaries `V₀₀, V₁₁`. -/
lemma section3_lemma_3_1 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (U : Square 8) (hU : U ∈ Matrix.unitaryGroup (Fin 8) ℂ) :
    (U * (diag2 u₀ u₁ ⊗ₖ (1 : Square 2) ⊗ₖ (1 : Square 2)) =
     (diag2 u₀ u₁ ⊗ₖ (1 : Square 2) ⊗ₖ (1 : Square 2)) * U)
    ↔ u₀ = u₁ ∨
      (∃ (V₀₀ V₁₁ : Square 4),
        V₀₀ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
        V₁₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
        U = proj0 ⊗ₖ V₀₀ + proj1 ⊗ₖ V₁₁) := by sorry

/-- **Lemma 3.2** (Eigenvalue condition for tensor product).
    Suppose `u₀, u₁` are unit complex numbers.
    There exist 2×2 unitaries `P, Q` such that the eigenvalues
    of `P ⊗ Q` are `{1, 1, u₀, u₁}` (via explicit diagonalization)
    if and only if either `u₀ = u₁` or `u₀ * u₁ = 1`. -/
lemma section3_lemma_3_2 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (P Q : Square 2) (V : Square 4),
      P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      V ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      P ⊗ₖ Q = V * diag4 1 1 u₀ u₁ * V†)
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by sorry

/-- **Lemma 3.3** (Eigenvalue condition for controlled gate).
    Suppose `u₀, u₁` are unit complex numbers.
    There exist a 2×2 unitary `P` and complex numbers `c, d`
    such that the eigenvalues of `(I₂ ⊗ P) · C(Diag(u₀, u₁))`
    are `{c, c, d, d}` (via explicit diagonalization)
    if and only if either `u₀ = u₁` or `u₀ * u₁ = 1`. -/
lemma section3_lemma_3_3 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (P : Square 2), P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      ∃ (U : Square 4), U ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
        ∃ (c d : ℂ),
          (1 : Square 2) ⊗ₖ P * controlledGate (diag2 u₀ u₁) =
          U * diag4 c d c d * U†)
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by sorry

end TwoControl

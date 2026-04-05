import TwoControl.Section4

namespace TwoControl

/-- **Lemma 5.1** (The first main lemma).
    Suppose `u₀, u₁` are complex numbers with `‖u₀‖ = 1` and `‖u₁‖ = 1`.
    There exist 2-qubit unitaries `U₁, U₂, U₃, U₄` such that
    `U₁^{BC} U₂^{AC} U₃^{AB} U₄^{BC} = CC(Diag(u₀, u₁))`
    if and only if either `u₀ = u₁` or `u₀ * u₁ = 1`. -/
lemma section5_lemma_5_1 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (U₁ U₂ U₃ U₄ : Square 4),
      U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      bcgate U₁ * acgate U₂ * abgate U₃ * bcgate U₄ = ccu (diag2 u₀ u₁))
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by sorry

end TwoControl

import TwoControl.Section3

namespace TwoControl

/-- **Lemma 4.1** (First building block).
    Suppose `u₀, u₁` are complex numbers with `‖u₀‖ = 1` and `‖u₁‖ = 1`.
    There exist 4×4 unitaries `U, V` and 2×2 unitaries `P₀, P₁, Q₀, Q₁` such that
    `|0⟩⟨0| ⊗ U(P₀ ⊗ Q₀)V + |1⟩⟨1| ⊗ U(P₁ ⊗ Q₁)V = CC(Diag(u₀, u₁))`
    if and only if either `u₀ = u₁` or `u₀ * u₁ = 1`. -/
lemma section4_lemma_4_1 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (U V : Square 4) (P₀ P₁ Q₀ Q₁ : Square 2),
      U ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      proj0 ⊗ₖ (U * (P₀ ⊗ₖ Q₀) * V) + proj1 ⊗ₖ (U * (P₁ ⊗ₖ Q₁) * V)
        = ccu (diag2 u₀ u₁))
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by sorry

/-- **Lemma 4.2** (Second building block).
    Suppose `u₀, u₁` are complex numbers with `‖u₀‖ = 1` and `‖u₁‖ = 1`.
    Suppose `Q` is a 2×2 unitary and let `β = Q * ket0` and `β⊥ = Q * ket1`.
    There exist 2×2 unitaries `P₀, P₁` such that
    `I ⊗ I ⊗ |β⟩⟨β| + P₀ ⊗ P₁ ⊗ |β⊥⟩⟨β⊥| = CC(Diag(u₀, u₁))`
    if and only if `u₀ = 1` and `u₁ = 1`. -/
lemma section4_lemma_4_2 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (Q : Square 2) (hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    let β := Q.mulVec ket0
    let β_perp := Q.mulVec ket1
    (∃ (P₀ P₁ : Square 2),
      P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      (1 : Square 2) ⊗ₖ (1 : Square 2) ⊗ₖ ketbra β β
        + P₀ ⊗ₖ P₁ ⊗ₖ ketbra β_perp β_perp
        = ccu (diag2 u₀ u₁))
    ↔ u₀ = 1 ∧ u₁ = 1 := by sorry

/-- **Lemma 4.3** (Third building block).
    Suppose `u₀, u₁` are complex numbers with `‖u₀‖ = 1` and `‖u₁‖ = 1`.
    There exist 4×4 unitaries `V₁, V₂, V₃, V₄` and 2×2 unitaries `P₀, P₁`,
    where `V₁ = |0⟩⟨0| ⊗ P₀ + |1⟩⟨1| ⊗ P₁`,
    such that `(V₁)_{AC} · (V₂)_{BC} · (V₃)_{AC} · (V₄)_{BC} = CC(Diag(u₀, u₁))`
    if and only if either `u₀ = u₁` or `u₀ * u₁ = 1`. -/
lemma section4_lemma_4_3 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (V₁ V₂ V₃ V₄ : Square 4),
      V₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      ∃ (P₀ P₁ : Square 2),
        P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        V₁ = proj0 ⊗ₖ P₀ + proj1 ⊗ₖ P₁ ∧
        acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ = ccu (diag2 u₀ u₁))
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by sorry

/-- **Lemma 4.4** (Fourth building block).
    Suppose `u₀, u₁` are complex numbers with `‖u₀‖ = 1` and `‖u₁‖ = 1`.
    There exist 4×4 unitaries `V₁, V₂, V₃, V₄` and 2×2 unitaries `P₀, P₁`,
    where `V₄ = |0⟩⟨0| ⊗ P₀ + |1⟩⟨1| ⊗ P₁`,
    such that `(V₁)_{AC} · (V₂)_{BC} · (V₃)_{AC} · (V₄)_{BC} = CC(Diag(u₀, u₁))`
    if and only if either `u₀ = u₁` or `u₀ * u₁ = 1`. -/
lemma section4_lemma_4_4 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (V₁ V₂ V₃ V₄ : Square 4),
      V₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      ∃ (P₀ P₁ : Square 2),
        P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        V₄ = proj0 ⊗ₖ P₀ + proj1 ⊗ₖ P₁ ∧
        acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ = ccu (diag2 u₀ u₁))
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by sorry

end TwoControl

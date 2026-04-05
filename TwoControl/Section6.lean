import TwoControl.Section5

open scoped Matrix ComplexOrder
open Matrix

namespace TwoControl

/-! # Section 6: The second main lemma -/

/-- **Lemma 6.1** (Case analysis of a unitary).
For a 2-qubit unitary `V`, either
  (1) there exists a qubit `x` such that `V(x ⊗ |0⟩)` is entangled, or
  (2) there exists a qubit `ψ` such that for all qubits `x`,
      `V(x ⊗ |0⟩) = z ⊗ ψ` for some qubit `z`, or
  (3) there exists a qubit `ψ` such that for all qubits `x`,
      `V(x ⊗ |0⟩) = ψ ⊗ z` for some qubit `z`. -/
lemma section6_lemma_6_1
    (V : Square 4) (hV : V ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    (∃ x : Vec 2, IsQubit x ∧ IsEntangled (V.mulVec (kronVec x ket0))) ∨
    (∃ ψ : Vec 2, IsQubit ψ ∧
      ∀ x : Vec 2, IsQubit x →
        ∃ z : Vec 2, IsQubit z ∧ V.mulVec (kronVec x ket0) = kronVec z ψ) ∨
    (∃ ψ : Vec 2, IsQubit ψ ∧
      ∀ x : Vec 2, IsQubit x →
        ∃ z : Vec 2, IsQubit z ∧ V.mulVec (kronVec x ket0) = kronVec ψ z) := by
  sorry

/-- **Lemma 6.2**.
Suppose `|u₀| = |u₁| = 1`. For 2-qubit unitaries `U₁, W₂, V₃, U₄`, if
  `U₁^{AC} W₂^{BC} V₃^{AC} U₄^{BC} = CC(Diag(u₀, u₁))`,
  `V₃(|0⟩ ⊗ |0⟩) = |0⟩ ⊗ |0⟩`, and
  `∀ x, U₁^{AC}(x ⊗ |0⟩ ⊗ |0⟩) = U₄^{BC†} V₃^{AC†}(x ⊗ |0⟩ ⊗ |0⟩)`,
then either `u₀ = u₁` or `u₀ u₁ = 1` or there exist unitaries `W₁, W₃, W₄, P₃`
such that `U₁^{AC} W₂^{BC} V₃^{AC} U₄^{BC} = W₁^{AC} W₂^{BC} W₃^{AC} W₄^{BC}`
and `W₃ = I ⊗ |0⟩⟨0| + P₃ ⊗ |1⟩⟨1|`. -/
lemma section6_lemma_6_2
    (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (U₁ W₂ V₃ U₄ : Square 4)
    (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hW₂ : W₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₃ : V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hU₄ : U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (heq : acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄ = ccu (diag2 u₀ u₁))
    (hV₃_fix : V₃.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0)
    (hident : ∀ x : Vec 2, IsQubit x →
      (acgate U₁).mulVec (kronVec (kronVec x ket0) ket0) =
      (bcgate U₄† * acgate V₃†).mulVec (kronVec (kronVec x ket0) ket0)) :
    u₀ = u₁ ∨ u₀ * u₁ = 1 ∨
    ∃ (W₁ W₃ W₄ : Square 4),
      W₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      W₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      W₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      ∃ (P₃ : Square 2), P₃ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄ =
          acgate W₁ * bcgate W₂ * acgate W₃ * bcgate W₄ ∧
        W₃ = (1 : Square 2) ⊗ₖ proj0 + P₃ ⊗ₖ proj1 := by
  sorry

/-- **Lemma 6.3**.
Suppose `|u₀| = |u₁| = 1`. For 2-qubit unitaries `V₁, V₂, V₃, V₄`, if
  `V₁^{AC} V₂^{BC} V₃^{AC} V₄^{BC} = CC(Diag(u₀, u₁))`,
  `∃ ψ, ∀ x, ∃ z, V₂(x ⊗ |0⟩) = z ⊗ ψ`, and
  `V₃(|0⟩ ⊗ |0⟩) = |0⟩ ⊗ |0⟩`,
then either `u₀ = u₁` or `u₀ u₁ = 1` or there exist unitaries
`W₁, W₂, W₃, W₄, P₁, P₂, P₃, P₄, Q` such that
  `W₁^{AC} W₂^{BC} W₃^{AC} W₄^{BC} = CC(Diag(u₀, u₁))`,
  `W₁ = I ⊗ (Q · |0⟩⟨0|) + P₁ ⊗ (Q · |1⟩⟨1|)`,
  `W₂ = I ⊗ |0⟩⟨0| + P₂ ⊗ |1⟩⟨1|`,
  `W₃ = I ⊗ |0⟩⟨0| + P₃ ⊗ |1⟩⟨1|`,
  `W₄ = I ⊗ (|0⟩⟨0| · Q†) + P₄ ⊗ (|1⟩⟨1| · Q†)`. -/
lemma section6_lemma_6_3
    (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (V₁ V₂ V₃ V₄ : Square 4)
    (hV₁ : V₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₂ : V₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₃ : V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₄ : V₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (heq : acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ = ccu (diag2 u₀ u₁))
    (hV₂_struct : ∃ ψ : Vec 2, IsQubit ψ ∧
      ∀ x : Vec 2, IsQubit x →
        ∃ z : Vec 2, IsQubit z ∧ V₂.mulVec (kronVec x ket0) = kronVec z ψ)
    (hV₃_fix : V₃.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0) :
    u₀ = u₁ ∨ u₀ * u₁ = 1 ∨
    ∃ (W₁ W₂ W₃ W₄ : Square 4),
      W₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      W₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      W₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      W₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      ∃ (P₁ P₂ P₃ P₄ Q : Square 2),
        P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        P₂ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        P₃ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        P₄ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        Q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        acgate W₁ * bcgate W₂ * acgate W₃ * bcgate W₄ = ccu (diag2 u₀ u₁) ∧
        W₁ = (1 : Square 2) ⊗ₖ (Q * proj0) + P₁ ⊗ₖ (Q * proj1) ∧
        W₂ = (1 : Square 2) ⊗ₖ proj0 + P₂ ⊗ₖ proj1 ∧
        W₃ = (1 : Square 2) ⊗ₖ proj0 + P₃ ⊗ₖ proj1 ∧
        W₄ = (1 : Square 2) ⊗ₖ (proj0 * Q†) + P₄ ⊗ₖ (proj1 * Q†) := by
  sorry

/-- **Lemma 6.4** (The second main lemma).
Suppose `|u₀| = |u₁| = 1`. There exist 2-qubit unitaries `U₁, U₂, U₃, U₄`
such that `U₁^{AC} U₂^{BC} U₃^{AC} U₄^{BC} = CC(Diag(u₀, u₁))`
if and only if either `u₀ = u₁` or `u₀ u₁ = 1`. -/
lemma section6_lemma_6_4
    (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (U₁ U₂ U₃ U₄ : Square 4),
      U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      acgate U₁ * bcgate U₂ * acgate U₃ * bcgate U₄ = ccu (diag2 u₀ u₁))
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by
  sorry

end TwoControl

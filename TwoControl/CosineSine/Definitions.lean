import TwoControl.BlockHelpers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped ComplexOrder
open Matrix

namespace TwoControl
namespace CosineSine

noncomputable def blockDiag2 (A B : Square 2) : Square 4 :=
  proj0 ⊗ₖ A + proj1 ⊗ₖ B

/-- Real diagonal block promoted to a complex `2 × 2` matrix. -/
def realDiag2 (x y : ℝ) : Square 2 :=
  diag2 (x : ℂ) (y : ℂ)

/-- The `4 × 4` square-block cosine-sine core attached to a `2 + 2` block decomposition. -/
noncomputable def csBlockCore (c₀ c₁ s₀ s₁ : ℝ) : Square 4 :=
  unblockify (n := 2)
    (Matrix.fromBlocks
      (realDiag2 c₀ c₁)
      (- realDiag2 s₀ s₁)
      (realDiag2 s₀ s₁)
      (realDiag2 c₀ c₁))

/-- The one-qubit `R_y` rotation, using the half-angle matrix convention from the packet. -/
noncomputable def ry (θ : ℝ) : Square 2 :=
  Matrix.of <|
    ![![((Real.cos (θ / 2)) : ℂ), ((- Real.sin (θ / 2)) : ℂ)],
      ![((Real.sin (θ / 2)) : ℂ), ((Real.cos (θ / 2)) : ℂ)]]

/-- The paper-facing middle factor for the appendix lemma:
`R_y(θ₀) ⊗ |0⟩⟨0| + R_y(θ₁) ⊗ |1⟩⟨1|`. -/
noncomputable def conditionalRy (θ₀ θ₁ : ℝ) : Square 4 :=
  ry θ₀ ⊗ₖ proj0 + ry θ₁ ⊗ₖ proj1

end CosineSine
end TwoControl

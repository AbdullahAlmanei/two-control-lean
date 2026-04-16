import TwoControl.BlockHelpers
import TwoControl.DiagonalizationHelpers

open scoped Matrix ComplexOrder
open Matrix

namespace TwoControl

/-! ### Kronecker helper lemmas -/

namespace KronHelpers

lemma kron_one_assoc (A : Square 2) :
    (A ⊗ₖ (1 : Square 2)) ⊗ₖ (1 : Square 2) = A ⊗ₖ (1 : Square 4) := by
  ext i j
  obtain ⟨⟨i12, i3⟩, rfl⟩ := (@finProdFinEquiv 4 2).surjective i
  obtain ⟨⟨j12, j3⟩, rfl⟩ := (@finProdFinEquiv 4 2).surjective j
  obtain ⟨⟨i1, i2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective i12
  obtain ⟨⟨j1, j2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective j12
  rw [TwoControl.kron_apply, TwoControl.kron_apply]
  rw [BlockHelpers.finProd_assoc_222 i1 i2 i3, BlockHelpers.finProd_assoc_222 j1 j2 j3,
    TwoControl.kron_apply]
  rw [← TwoControl.one_kron_one 2 2, TwoControl.kron_apply]
  simp [mul_assoc]

lemma kron_smul_right (A : Square m) (c : ℂ) (B : Square n) :
    A ⊗ₖ (c • B) = c • (A ⊗ₖ B) := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (@finProdFinEquiv m n).surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (@finProdFinEquiv m n).surjective j
  simp [TwoControl.kron_apply, mul_left_comm]

end KronHelpers

end TwoControl

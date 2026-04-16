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

lemma kron_add_right (A : Square m) (B₁ B₂ : Square n) :
    A ⊗ₖ (B₁ + B₂) = A ⊗ₖ B₁ + A ⊗ₖ B₂ := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (@finProdFinEquiv m n).surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (@finProdFinEquiv m n).surjective j
  simp [TwoControl.kron_apply, mul_add]

lemma kron_mul_reindex {m n : ℕ} (A B : Square m) (C D : Square n) :
    (A * B) ⊗ₖ (C * D) = (A ⊗ₖ C) * (B ⊗ₖ D) := by
  simpa [TwoControl.kron, Matrix.reindexAlgEquiv_apply] using
    congrArg (Matrix.reindexAlgEquiv ℂ ℂ (@finProdFinEquiv m n))
      (Matrix.mul_kronecker_mul A B C D)

lemma kron_assoc_222 (X A B : Square 2) :
    (X ⊗ₖ A) ⊗ₖ B = X ⊗ₖ (A ⊗ₖ B) := by
  ext i j
  obtain ⟨⟨i12, i3⟩, rfl⟩ := (@finProdFinEquiv 4 2).surjective i
  obtain ⟨⟨j12, j3⟩, rfl⟩ := (@finProdFinEquiv 4 2).surjective j
  obtain ⟨⟨i1, i2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective i12
  obtain ⟨⟨j1, j2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective j12
  rw [TwoControl.kron_apply, TwoControl.kron_apply]
  rw [BlockHelpers.finProd_assoc_222 i1 i2 i3, BlockHelpers.finProd_assoc_222 j1 j2 j3,
    TwoControl.kron_apply, TwoControl.kron_apply]
  simp [mul_assoc]

lemma split_one_kron_terms {n : ℕ} (P Q R : Square n) :
    (1 : Square 2) ⊗ₖ P + proj0 ⊗ₖ Q + proj1 ⊗ₖ R =
      proj0 ⊗ₖ (P + Q) + proj1 ⊗ₖ (P + R) := by
  rw [← BlockHelpers.proj0_add_proj1, kron_add_left]
  calc
    proj0 ⊗ₖ P + proj1 ⊗ₖ P + proj0 ⊗ₖ Q + proj1 ⊗ₖ R
        = (proj0 ⊗ₖ P + proj0 ⊗ₖ Q) + (proj1 ⊗ₖ P + proj1 ⊗ₖ R) := by
          ac_rfl
    _ = proj0 ⊗ₖ (P + Q) + proj1 ⊗ₖ (P + R) := by
          rw [← kron_add_right, ← kron_add_right]

lemma eq_zero_of_one_kron_eq_zero (A : Square 2) (h : (1 : Square 2) ⊗ₖ A = 0) :
    A = 0 := by
  ext i j
  have hij := congrFun (congrFun h (@finProdFinEquiv 2 2 (0, i))) (@finProdFinEquiv 2 2 (0, j))
  have hEntry :
      ((1 : Square 2) ⊗ₖ A) (@finProdFinEquiv 2 2 (0, i)) (@finProdFinEquiv 2 2 (0, j)) = A i j := by
    simpa using (TwoControl.kron_apply (A := (1 : Square 2)) (B := A) 0 i 0 j)
  simpa [hEntry] using hij

lemma conjTranspose_kron_reindex {m n : ℕ} (A : Square m) (B : Square n) :
    (A ⊗ₖ B)† = A† ⊗ₖ B† := by
  simpa [TwoControl.kron, Matrix.reindexAlgEquiv_apply, Matrix.star_eq_conjTranspose] using
    congrArg (Matrix.reindexAlgEquiv ℂ ℂ (@finProdFinEquiv m n))
      (Matrix.conjTranspose_kronecker A B)

end KronHelpers

end TwoControl

import TwoControl.Definitions
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

open scoped Matrix ComplexOrder
open Matrix

namespace TwoControl

/-! ### Reindexed Kronecker helper lemmas -/

@[simp] theorem kron_apply (A : Square m) (B : Square n)
    (i₁ : Fin m) (i₂ : Fin n) (j₁ : Fin m) (j₂ : Fin n) :
    (A ⊗ₖ B) (finProdFinEquiv (i₁, i₂)) (finProdFinEquiv (j₁, j₂)) = A i₁ j₁ * B i₂ j₂ := by
  simp [TwoControl.kron, Matrix.reindex_apply, Matrix.kroneckerMap_apply]

theorem kron_add_left (A₁ A₂ : Square m) (B : Square n) :
    (A₁ + A₂) ⊗ₖ B = A₁ ⊗ₖ B + A₂ ⊗ₖ B := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp [add_mul]

theorem kron_smul_left (c : ℂ) (A : Square m) (B : Square n) :
    (c • A) ⊗ₖ B = c • (A ⊗ₖ B) := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp [mul_assoc]

theorem zero_kron_left (B : Square n) :
    (0 : Square m) ⊗ₖ B = 0 := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp

theorem zero_kron_right (A : Square m) :
    A ⊗ₖ (0 : Square n) = 0 := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp

theorem one_kron_one (m n : ℕ) :
    (1 : Square m) ⊗ₖ (1 : Square n) = (1 : Square (m * n)) := by
  unfold TwoControl.kron
  rw [Matrix.one_kronecker_one]
  exact Matrix.submatrix_one_equiv
    (finProdFinEquiv.symm : Fin (m * n) ≃ Fin m × Fin n)

/-! ### Matrix units on the first qubit -/

/-- The matrix unit `|0⟩⟨1|`. -/
noncomputable def proj01 : Square 2 := ketbra ket0 ket1

/-- The matrix unit `|1⟩⟨0|`. -/
noncomputable def proj10 : Square 2 := ketbra ket1 ket0

/-! ### Block reindexing from `Fin (2 * n)` to `Fin n ⊕ Fin n` -/

/-- Reindex `Fin 2 × Fin n` as a two-block sum type. -/
def finTwoProdSumEquiv (n : ℕ) : Fin 2 × Fin n ≃ Fin n ⊕ Fin n where
  toFun x := Fin.cases (Sum.inl x.2) (fun _ => Sum.inr x.2) x.1
  invFun
    | Sum.inl i => (0, i)
    | Sum.inr i => (1, i)
  left_inv := by
    rintro ⟨b, i⟩
    fin_cases b <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

/-- Reindex `Fin (2 * n)` as `Fin n ⊕ Fin n`. -/
def finTwoBlockEquiv (n : ℕ) : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
  (@finProdFinEquiv 2 n).symm.trans (finTwoProdSumEquiv n)

@[simp] theorem finTwoBlockEquiv_symm_apply_inl (i : Fin n) :
    (finTwoBlockEquiv n).symm (Sum.inl i) = @finProdFinEquiv 2 n (0, i) := by
  rfl

@[simp] theorem finTwoBlockEquiv_symm_apply_inr (i : Fin n) :
    (finTwoBlockEquiv n).symm (Sum.inr i) = @finProdFinEquiv 2 n (1, i) := by
  rfl

@[simp] theorem finTwoBlockEquiv_apply_zero (i : Fin n) :
    finTwoBlockEquiv n (@finProdFinEquiv 2 n (0, i)) = Sum.inl i := by
  simpa using (finTwoBlockEquiv n).apply_symm_apply (Sum.inl i)

@[simp] theorem finTwoBlockEquiv_apply_one (i : Fin n) :
    finTwoBlockEquiv n (@finProdFinEquiv 2 n (1, i)) = Sum.inr i := by
  simpa using (finTwoBlockEquiv n).apply_symm_apply (Sum.inr i)

abbrev BlockMatrix (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ

/-- Algebra equivalence between `Square (2 * n)` and 2-by-2 block matrices over `Square n`. -/
noncomputable def blockAlgEquiv (n : ℕ) : Square (2 * n) ≃ₐ[ℂ] BlockMatrix n :=
  Matrix.reindexAlgEquiv ℂ ℂ (finTwoBlockEquiv n)

/-- Reindex a `2n × 2n` matrix into 2-by-2 block form. -/
noncomputable def blockify (M : Square (2 * n)) : BlockMatrix n :=
  Matrix.reindex (finTwoBlockEquiv n) (finTwoBlockEquiv n) M

/-- Return from 2-by-2 block form to the original `Fin (2 * n)` indexing. -/
noncomputable def unblockify (M : BlockMatrix n) : Square (2 * n) :=
  Matrix.reindex (finTwoBlockEquiv n).symm (finTwoBlockEquiv n).symm M

theorem blockify_injective : Function.Injective (blockify (n := n)) :=
  (Matrix.reindex (finTwoBlockEquiv n) (finTwoBlockEquiv n)).injective

@[simp] theorem blockify_zero : blockify (n := n) (0 : Square (2 * n)) = 0 := by
  ext i j
  simp [blockify]

@[simp] theorem blockify_one : blockify (n := n) (1 : Square (2 * n)) = 1 := by
  unfold blockify
  exact Matrix.submatrix_one_equiv
    ((finTwoBlockEquiv n).symm : Fin n ⊕ Fin n ≃ Fin (2 * n))

@[simp] theorem blockify_add (M N : Square (2 * n)) :
    blockify (M + N) = blockify M + blockify N := by
  ext i j
  rfl

@[simp] theorem blockify_smul (c : ℂ) (M : Square (2 * n)) :
    blockify (c • M) = c • blockify M := by
  ext i j
  rfl

@[simp] theorem blockify_mul (M N : Square (2 * n)) :
    blockify (M * N) = blockify M * blockify N := by
  unfold blockify
  exact (Matrix.submatrix_mul_equiv M N (finTwoBlockEquiv n).symm (finTwoBlockEquiv n).symm
    (finTwoBlockEquiv n).symm).symm

@[simp] theorem unblockify_blockify (M : Square (2 * n)) :
    unblockify (blockify M) = M := by
  ext i j
  simp [blockify, unblockify, Matrix.reindex_apply]

@[simp] theorem blockify_unblockify (M : BlockMatrix n) :
    blockify (unblockify M) = M := by
  ext i j
  simp [blockify, unblockify, Matrix.reindex_apply]

@[simp] theorem blockify_conjTranspose (M : Square (2 * n)) :
    blockify M† = (blockify M)† := by
  ext i j
  simp [blockify, Matrix.reindex_apply,
    Matrix.conjTranspose_apply]

theorem blockify_mem_unitaryGroup_iff (U : Square (2 * n)) :
    blockify U ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ ↔ U ∈ Matrix.unitaryGroup (Fin (2 * n)) ℂ := by
  constructor
  · intro h
    rcases h with ⟨hleft, hright⟩
    constructor
    · apply blockify_injective (n := n)
      simpa [blockify_conjTranspose] using hleft
    · apply blockify_injective (n := n)
      simpa [blockify_conjTranspose] using hright
  · intro h
    rcases h with ⟨hleft, hright⟩
    constructor
    · simpa [blockify_conjTranspose] using congrArg (blockify (n := n)) hleft
    · simpa [blockify_conjTranspose] using congrArg (blockify (n := n)) hright

/-! ### Bridge lemmas between block matrices and `proj`/`kron` syntax -/

theorem blockify_proj0_kron (A : Square n) :
    blockify (proj0 ⊗ₖ A) = Matrix.fromBlocks A 0 0 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockify, proj0, ketbra, ket0]

theorem blockify_proj01_kron (A : Square n) :
    blockify (proj01 ⊗ₖ A) = Matrix.fromBlocks 0 A 0 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockify, proj01, ketbra, ket0, ket1]

theorem blockify_proj10_kron (A : Square n) :
    blockify (proj10 ⊗ₖ A) = Matrix.fromBlocks 0 0 A 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockify, proj10, ketbra, ket0, ket1]

theorem blockify_proj1_kron (A : Square n) :
    blockify (proj1 ⊗ₖ A) = Matrix.fromBlocks 0 0 0 A := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockify, proj1, ketbra, ket1]

theorem blockify_blockExpansion (A B C D : Square n) :
    blockify (proj0 ⊗ₖ A + proj01 ⊗ₖ B + proj10 ⊗ₖ C + proj1 ⊗ₖ D) =
      Matrix.fromBlocks A B C D := by
  rw [blockify_add, blockify_add, blockify_add]
  rw [blockify_proj0_kron, blockify_proj01_kron, blockify_proj10_kron, blockify_proj1_kron]
  simp [Matrix.fromBlocks_add]

theorem unblockify_fromBlocks (A B C D : Square n) :
    unblockify (Matrix.fromBlocks A B C D) =
      proj0 ⊗ₖ A + proj01 ⊗ₖ B + proj10 ⊗ₖ C + proj1 ⊗ₖ D := by
  apply blockify_injective (n := n)
  calc
    blockify (unblockify (Matrix.fromBlocks A B C D)) = Matrix.fromBlocks A B C D := by
      simp [blockify, unblockify]
    _ = blockify (proj0 ⊗ₖ A + proj01 ⊗ₖ B + proj10 ⊗ₖ C + proj1 ⊗ₖ D) := by
      symm
      exact blockify_blockExpansion A B C D

theorem blockDecomposition (U : Square (2 * n)) :
    U =
      proj0 ⊗ₖ (blockify U).toBlocks₁₁ +
      proj01 ⊗ₖ (blockify U).toBlocks₁₂ +
      proj10 ⊗ₖ (blockify U).toBlocks₂₁ +
      proj1 ⊗ₖ (blockify U).toBlocks₂₂ := by
  calc
    U = unblockify (blockify U) := by simp
    _ = unblockify (Matrix.fromBlocks (blockify U).toBlocks₁₁ (blockify U).toBlocks₁₂
          (blockify U).toBlocks₂₁ (blockify U).toBlocks₂₂) := by
          rw [Matrix.fromBlocks_toBlocks]
    _ =
      proj0 ⊗ₖ (blockify U).toBlocks₁₁ +
      proj01 ⊗ₖ (blockify U).toBlocks₁₂ +
      proj10 ⊗ₖ (blockify U).toBlocks₂₁ +
      proj1 ⊗ₖ (blockify U).toBlocks₂₂ :=
      unblockify_fromBlocks _ _ _ _

/-! ### Diagonal blocks -/

theorem diag2_decomp (u₀ u₁ : ℂ) :
    diag2 u₀ u₁ = u₀ • proj0 + u₁ • proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag2, proj0, proj1, ketbra, ket0, ket1]

theorem blockify_diag2_kron_one (u₀ u₁ : ℂ) :
    blockify (diag2 u₀ u₁ ⊗ₖ (1 : Square n)) =
      Matrix.fromBlocks (u₀ • (1 : Square n)) 0 0 (u₁ • (1 : Square n)) := by
  rw [diag2_decomp, kron_add_left, kron_smul_left, kron_smul_left]
  simp [blockify_proj0_kron, blockify_proj1_kron, Matrix.fromBlocks_smul,
    Matrix.fromBlocks_add]

end TwoControl

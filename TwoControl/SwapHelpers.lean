import TwoControl.KronHelpers
import TwoControl.StateHelpers

open scoped Matrix ComplexOrder
open Matrix

namespace TwoControl

/-! ### SWAP helper lemmas -/

namespace SwapHelpers

lemma swap2_conjTranspose : swap2† = swap2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2]

lemma swap2_mul_swap2 : swap2 * swap2 = (1 : Square 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2]

lemma swap2_unitary : swap2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, show star swap2 = swap2 by
    simpa [star_eq_conjTranspose] using swap2_conjTranspose, swap2_mul_swap2]

lemma swap2_conj_unitary {U : Square 4}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    swap2 * U * swap2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ swap2_unitary hU) swap2_unitary

lemma swap2_conj_diag4 (a b c d : ℂ) :
    swap2 * diag4 a b c d * swap2† = diag4 a c b d := by
  rw [swap2_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ, swap2, diag4]

lemma swap_index_prod (i : Fin 4) :
    ((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)) =
      Prod.swap ((@finProdFinEquiv 2 2).symm i) := by
  fin_cases i <;> decide

lemma swap2_left_mul_apply (M : Square 4) (i j : Fin 4) :
    (swap2 * M) i j = M ((Equiv.swap (1 : Fin 4) 2) i) j := by
  fin_cases i <;>
    simp [swap2, Matrix.mul_apply, Fin.sum_univ_succ, Equiv.swap_apply_def]

lemma swap2_right_mul_apply (M : Square 4) (i j : Fin 4) :
    (M * swap2) i j = M i ((Equiv.swap (1 : Fin 4) 2) j) := by
  fin_cases j <;>
    simp [swap2, Matrix.mul_apply, Fin.sum_univ_succ, Equiv.swap_apply_def]

lemma swap2_conj_apply (M : Square 4) (i j : Fin 4) :
    (swap2 * M * swap2) i j =
      M ((Equiv.swap (1 : Fin 4) 2) i) ((Equiv.swap (1 : Fin 4) 2) j) := by
  rw [swap2_right_mul_apply, swap2_left_mul_apply]

lemma swap2_conj_kron_right (A : Square 2) :
    swap2 * (A ⊗ₖ (1 : Square 2)) * swap2 = (1 : Square 2) ⊗ₖ A := by
  ext i j
  calc
    (swap2 * (A ⊗ₖ (1 : Square 2)) * swap2) i j
        = (A ⊗ₖ (1 : Square 2)) ((Equiv.swap (1 : Fin 4) 2) i) ((Equiv.swap (1 : Fin 4) 2) j) := by
          rw [swap2_conj_apply]
    _ = A (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).1)
          (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).1) *
          (1 : Square 2) (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).2)
            (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).2) := by
          simpa using
            (TwoControl.kron_apply (A := A) (B := (1 : Square 2))
              (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).1)
              (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).2)
              (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).1)
              (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).2))
    _ = A ((@finProdFinEquiv 2 2).symm i).2 ((@finProdFinEquiv 2 2).symm j).2 *
          (1 : Square 2) ((@finProdFinEquiv 2 2).symm i).1 ((@finProdFinEquiv 2 2).symm j).1 := by
          rw [swap_index_prod i, swap_index_prod j]
          rfl
    _ = ((1 : Square 2) ⊗ₖ A) i j := by
      simpa [mul_comm] using
        (TwoControl.kron_apply (A := (1 : Square 2)) (B := A)
          ((@finProdFinEquiv 2 2).symm i).1
          ((@finProdFinEquiv 2 2).symm i).2
          ((@finProdFinEquiv 2 2).symm j).1
          ((@finProdFinEquiv 2 2).symm j).2).symm

lemma swap2_conj_kron_left (A : Square 2) :
    swap2 * ((1 : Square 2) ⊗ₖ A) * swap2 = A ⊗ₖ (1 : Square 2) := by
  calc
    swap2 * ((1 : Square 2) ⊗ₖ A) * swap2
        = swap2 * (swap2 * (A ⊗ₖ (1 : Square 2)) * swap2) * swap2 := by
          rw [swap2_conj_kron_right]
    _ = (swap2 * (swap2 * (A ⊗ₖ (1 : Square 2)))) * (swap2 * swap2) := by
          simp [mul_assoc]
    _ = (swap2 * (swap2 * (A ⊗ₖ (1 : Square 2)))) * 1 := by
          rw [swap2_mul_swap2]
    _ = (swap2 * swap2) * (A ⊗ₖ (1 : Square 2)) := by
          simp [mul_assoc]
    _ = A ⊗ₖ (1 : Square 2) := by
          rw [swap2_mul_swap2]
          simp

lemma swap2_conj_kron (X Y : Square 2) :
    swap2 * (X ⊗ₖ Y) * swap2 = Y ⊗ₖ X := by
  ext i j
  calc
    (swap2 * (X ⊗ₖ Y) * swap2) i j
        = (X ⊗ₖ Y) ((Equiv.swap (1 : Fin 4) 2) i) ((Equiv.swap (1 : Fin 4) 2) j) := by
          rw [swap2_conj_apply]
    _ = X (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).1)
          (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).1) *
          Y (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).2)
            (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).2) := by
          simpa using
            (TwoControl.kron_apply (A := X) (B := Y)
              (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).1)
              (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).2)
              (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).1)
              (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).2))
    _ = Y ((@finProdFinEquiv 2 2).symm i).1 ((@finProdFinEquiv 2 2).symm j).1 *
          X ((@finProdFinEquiv 2 2).symm i).2 ((@finProdFinEquiv 2 2).symm j).2 := by
          rw [swap_index_prod i, swap_index_prod j]
          simp [Prod.swap, mul_comm]
    _ = (Y ⊗ₖ X) i j := by
      simpa using
        (TwoControl.kron_apply (A := Y) (B := X)
          ((@finProdFinEquiv 2 2).symm i).1
          ((@finProdFinEquiv 2 2).symm i).2
          ((@finProdFinEquiv 2 2).symm j).1
          ((@finProdFinEquiv 2 2).symm j).2).symm

lemma swap2_mulVec_kronVec (x y : Vec 2) :
    swap2.mulVec (kronVec x y) = kronVec y x := by
  ext i
  fin_cases i <;>
    simp [swap2, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      StateHelpers.kronVec_vec2_apply_0, StateHelpers.kronVec_vec2_apply_1,
      StateHelpers.kronVec_vec2_apply_2, StateHelpers.kronVec_vec2_apply_3, mul_comm]

lemma swapab_mul_swapab : swapab * swapab = (1 : Square 8) := by
  unfold swapab
  rw [← KronHelpers.kron_mul_reindex]
  simpa [swap2_mul_swap2] using (TwoControl.one_kron_one 4 2)

lemma swapab_mulVec_kronVec (a b c : Vec 2) :
    swapab.mulVec (kronVec (kronVec a b) c : Vec 8) = kronVec (kronVec b a) c := by
  unfold swapab
  calc
    (swap2 ⊗ₖ (1 : Square 2)).mulVec (kronVec (kronVec a b) c : Vec 8)
        = kronVec (swap2.mulVec (kronVec a b)) ((1 : Square 2).mulVec c) := by
            simpa using
              (StateHelpers.kron_mulVec_reindexed (A := swap2) (B := (1 : Square 2))
                (x := kronVec a b) (y := c))
    _ = kronVec (kronVec b a) c := by rw [swap2_mulVec_kronVec]; simp

lemma swapbc_mul_swapbc : swapbc * swapbc = (1 : Square 8) := by
  unfold swapbc
  calc
    ((1 : Square 2) ⊗ₖ swap2) * ((1 : Square 2) ⊗ₖ swap2)
        = ((1 : Square 2) * (1 : Square 2)) ⊗ₖ (swap2 * swap2) := by
            rw [← KronHelpers.kron_mul_reindex (1 : Square 2) (1 : Square 2) swap2 swap2]
    _ = (1 : Square 2) ⊗ₖ (1 : Square 4) := by rw [swap2_mul_swap2]; simp
    _ = (1 : Square 8) := by simpa using (TwoControl.one_kron_one 2 4)

noncomputable def swapac : Square 8 := swapbc * swapab * swapbc

lemma swapac_mul_swapac : swapac * swapac = (1 : Square 8) := by
  unfold swapac
  calc
    swapbc * swapab * swapbc * (swapbc * swapab * swapbc)
        = swapbc * swapab * (swapbc * swapbc) * swapab * swapbc := by simp [mul_assoc]
    _ = swapbc * swapab * swapab * swapbc := by rw [swapbc_mul_swapbc]; simp [mul_assoc]
    _ = swapbc * (swapab * swapab) * swapbc := by simp [mul_assoc]
    _ = swapbc * swapbc := by rw [swapab_mul_swapab]; simp
    _ = (1 : Square 8) := swapbc_mul_swapbc

lemma swapab_conj_kron_three (X Y Z : Square 2) :
    swapab * (X ⊗ₖ (Y ⊗ₖ Z)) * swapab = Y ⊗ₖ (X ⊗ₖ Z) := by
  unfold swapab
  calc
    (swap2 ⊗ₖ (1 : Square 2)) * (X ⊗ₖ (Y ⊗ₖ Z)) * (swap2 ⊗ₖ (1 : Square 2))
    = (swap2 ⊗ₖ (1 : Square 2)) * ((X ⊗ₖ Y) ⊗ₖ Z) * (swap2 ⊗ₖ (1 : Square 2)) := by
      rw [← KronHelpers.kron_assoc_222 X Y Z]
    _ = ((swap2 * (X ⊗ₖ Y)) ⊗ₖ Z) * (swap2 ⊗ₖ (1 : Square 2)) := by
      rw [← KronHelpers.kron_mul_reindex swap2 (X ⊗ₖ Y) (1 : Square 2) Z]
      simp
    _ = ((swap2 * (X ⊗ₖ Y)) * swap2) ⊗ₖ (Z * (1 : Square 2)) := by
      rw [← KronHelpers.kron_mul_reindex (swap2 * (X ⊗ₖ Y)) swap2 Z (1 : Square 2)]
    _ = (Y ⊗ₖ X) ⊗ₖ Z := by
      rw [swap2_conj_kron]
      simp
    _ = Y ⊗ₖ (X ⊗ₖ Z) := by
      rw [KronHelpers.kron_assoc_222 Y X Z]

lemma swapbc_conj_kron (A : Square 2) (B : Square 4) :
    swapbc * (A ⊗ₖ B) * swapbc = A ⊗ₖ (swap2 * B * swap2) := by
  unfold swapbc
  calc
    ((1 : Square 2) ⊗ₖ swap2) * (A ⊗ₖ B) * ((1 : Square 2) ⊗ₖ swap2)
        = (((1 : Square 2) * A) ⊗ₖ (swap2 * B)) * ((1 : Square 2) ⊗ₖ swap2) := by
            rw [← KronHelpers.kron_mul_reindex (1 : Square 2) A swap2 B]
    _ = ((((1 : Square 2) * A) * (1 : Square 2)) ⊗ₖ ((swap2 * B) * swap2)) := by
          rw [← KronHelpers.kron_mul_reindex ((1 : Square 2) * A) (1 : Square 2)
            (swap2 * B) swap2]
    _ = A ⊗ₖ (swap2 * B * swap2) := by
          simp [mul_assoc]

end SwapHelpers

end TwoControl

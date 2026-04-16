import TwoControl.KronHelpers

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

lemma swap2_conj_diag4 (a b c d : ℂ) :
    swap2 * diag4 a b c d * swap2† = diag4 a c b d := by
  rw [swap2_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ, swap2, diag4]

end SwapHelpers

end TwoControl

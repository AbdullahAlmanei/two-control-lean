import TwoControl.SwapHelpers

open scoped Matrix ComplexOrder
open Matrix

namespace TwoControl

/-! ### Gate transport helper lemmas -/

namespace GateHelpers

def notc : Square 4 :=
  Matrix.of ![![1, 0, 0, 0],
              ![0, 0, 0, 1],
              ![0, 0, 1, 0],
              ![0, 1, 0, 0]]

lemma notc_conjTranspose : notc† = notc := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [notc]

lemma notc_mul_notc : notc * notc = (1 : Square 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [notc]

lemma notc_unitary : notc ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, show star notc = notc by
    simpa [star_eq_conjTranspose] using notc_conjTranspose, notc_mul_notc]

lemma notc_conj_diag4 (a b c d : ℂ) :
    notc * diag4 a b c d * notc† = diag4 a d c b := by
  rw [notc_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ, notc, diag4]

end GateHelpers

end TwoControl

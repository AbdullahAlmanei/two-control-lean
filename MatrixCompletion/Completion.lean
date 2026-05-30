import DyadicCyclotomic.Basic
import TwoControl.Clifford.Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace MatrixCompletion

open TwoControl
open TwoControl.Clifford
open DyadicCyclotomic
open scoped Matrix.Norms.L2Operator

/-- Operator norm distance between two 2×2 matrices. -/
noncomputable def opDist (U V : Square 2) : ℝ := ‖U - V‖

/-!
The completion matrix used by Ross-Selinger:

`U(u,t) = [[u, -t†], [t, u†]]`.

This file isolates the algebraic and metric facts about this matrix.  It is the
smallest local target for replacing the earlier broad `exists_dyadic_completion`
placeholder.
-/

/-- The upper-left phase of `Rz θ`. -/
noncomputable def rzPhase (θ : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (θ / 2))

theorem rzPhase_norm (θ : ℝ) :
    ‖rzPhase θ‖ = 1 := by
  unfold rzPhase
  rw [show -Complex.I * (θ / 2) = (-(θ / 2) : ℂ) * Complex.I by ring]
  simpa using Complex.norm_exp_ofReal_mul_I (-(θ / 2))

/-- The norm equation `u†u + t†t = 1`. -/
def NormEquation (u t : ℂ) : Prop :=
  star u * u + star t * t = 1

/-- The standard Ross-Selinger unitary completion. -/
noncomputable def completionMatrix (u t : ℂ) : Square 2 :=
  Matrix.of ![![u, -star t], ![t, star u]]

/-- The closed unit disk, viewed inside `ℂ`. -/
def InClosedUnitDisk (z : ℂ) : Prop :=
  ‖z‖ ≤ 1

/-- Ross-Selinger's epsilon region for the target phase `rzPhase θ`. -/
def InEpsilonRegion (θ ε : ℝ) (u : ℂ) : Prop :=
  InClosedUnitDisk u ∧
    1 - ε ^ 2 / 2 ≤ (star (rzPhase θ) * u).re

theorem normEquation_of_diophantine {u t : ℂ}
    (h : star t * t = 1 - star u * u) :
    NormEquation u t := by
  unfold NormEquation
  rw [h]
  ring

/-- Completing `u,t` satisfying the norm equation gives a unitary matrix. -/
theorem completionMatrix_mem_unitaryGroup {u t : ℂ}
    (hNorm : NormEquation u t) :
    completionMatrix u t ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [completionMatrix, Matrix.mul_apply, Fin.sum_univ_two, NormEquation] at hNorm ⊢
  · exact hNorm
  · ring
  · ring
  · simpa [add_comm, mul_comm] using hNorm

/-- If `u,t ∈ D[ω]`, then the completion matrix has entries in `D[ω]`. -/
theorem completionMatrix_entries_in_dyadic {u t : ℂ}
    (hu : InDyadicCyclotomic u)
    (ht : InDyadicCyclotomic t) :
    MatrixEntriesInDyadicCyclotomic (completionMatrix u t) := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [completionMatrix] using hu
  · simpa [completionMatrix] using (InDyadicCyclotomic.neg (InDyadicCyclotomic.star ht))
  · simpa [completionMatrix] using ht
  · simpa [completionMatrix] using (InDyadicCyclotomic.star hu)

private lemma star_exp_neg_div (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(Complex.I * (↑θ / 2)))) =
      Complex.exp (Complex.I * (↑θ / 2)) := by
  change star (Complex.exp (-(Complex.I * (↑θ / 2)))) =
    Complex.exp (Complex.I * (↑θ / 2))
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I]
  rw [show ((starRingEnd ℂ) 2) = (2 : ℂ) by exact map_ofNat (starRingEnd ℂ) 2]

private lemma star_exp_pos_div (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * (↑θ / 2))) =
      Complex.exp (-(Complex.I * (↑θ / 2))) := by
  change star (Complex.exp (Complex.I * (↑θ / 2))) =
    Complex.exp (-(Complex.I * (↑θ / 2)))
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I]
  rw [show ((starRingEnd ℂ) 2) = (2 : ℂ) by exact map_ofNat (starRingEnd ℂ) 2]

private lemma completion_error_gram (θ : ℝ) (u t : ℂ) :
    (rz θ - completionMatrix u t)† * (rz θ - completionMatrix u t) =
      (((‖rzPhase θ - u‖ ^ 2 + ‖t‖ ^ 2 : ℝ) : ℂ) • (1 : Square 2)) := by
  have hnormSq :
      ((‖rzPhase θ - u‖ ^ 2 + ‖t‖ ^ 2 : ℝ) : ℂ) =
        star (rzPhase θ - u) * (rzPhase θ - u) + star t * t := by
    rw [Complex.ofReal_add]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    simp
  rw [hnormSq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, rz, diag2, completionMatrix,
      rzPhase, star_exp_neg_div, star_exp_pos_div]
  all_goals ring

private lemma completion_error_radius (θ : ℝ) {u t : ℂ}
    (hNorm : NormEquation u t) :
    ‖rzPhase θ - u‖ ^ 2 + ‖t‖ ^ 2 =
      2 - 2 * (star (rzPhase θ) * u).re := by
  have hzNorm : Complex.normSq (rzPhase θ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, rzPhase_norm]
    norm_num
  have hnormEqReal : Complex.normSq u + Complex.normSq t = 1 := by
    have hNormC : ((Complex.normSq u + Complex.normSq t : ℝ) : ℂ) = (1 : ℂ) := by
      rw [Complex.ofReal_add]
      rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
      simpa [NormEquation] using hNorm
    exact Complex.ofReal_injective hNormC
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_sub]
  have hre :
      (rzPhase θ * (starRingEnd ℂ) u).re = (star (rzPhase θ) * u).re := by
    rw [← Complex.conj_re (star (rzPhase θ) * u)]
    congr 1
    simp [map_mul, mul_comm]
  rw [hre]
  nlinarith

private lemma opNorm_sq_completion_error (θ : ℝ) (u t : ℂ) :
    ‖rz θ - completionMatrix u t‖ ^ 2 =
      ‖rzPhase θ - u‖ ^ 2 + ‖t‖ ^ 2 := by
  let r : ℝ := ‖rzPhase θ - u‖ ^ 2 + ‖t‖ ^ 2
  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have hAA :
      (rz θ - completionMatrix u t)† * (rz θ - completionMatrix u t) =
        (r : ℂ) • (1 : Square 2) := by
    simpa [r] using completion_error_gram θ u t
  have hmul : ‖rz θ - completionMatrix u t‖ * ‖rz θ - completionMatrix u t‖ = r := by
    calc
      ‖rz θ - completionMatrix u t‖ * ‖rz θ - completionMatrix u t‖
          = ‖(rz θ - completionMatrix u t)† * (rz θ - completionMatrix u t)‖ := by
              rw [Matrix.l2_opNorm_conjTranspose_mul_self]
      _ = ‖(r : ℂ) • (1 : Square 2)‖ := by rw [hAA]
      _ = r := by simp [norm_smul, abs_of_nonneg hr]
  simpa [pow_two, r] using hmul

/-- Ross-Selinger's key metric calculation:
`‖Rz θ - U(u,t)‖² = |u-z|² + |t|²`, hence membership in the epsilon
region and the norm equation give an operator-norm approximation. -/
theorem opDist_rz_completion_le_of_region
    (θ : ℝ) {u t : ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hRegion : InEpsilonRegion θ ε u)
    (hNorm : NormEquation u t) :
    opDist (rz θ) (completionMatrix u t) ≤ ε := by
  rcases hRegion with ⟨_huDisk, hRegionRe⟩
  have hradius :
      ‖rzPhase θ - u‖ ^ 2 + ‖t‖ ^ 2 ≤ ε ^ 2 := by
    rw [completion_error_radius θ hNorm]
    nlinarith
  unfold opDist
  apply (sq_le_sq₀ (norm_nonneg (rz θ - completionMatrix u t)) (le_of_lt hε)).1
  rw [opNorm_sq_completion_error θ u t]
  exact hradius

/-- Compatibility metric lemma from the earlier scaffold.  This is convenient for
local analytic work, but the oracle proof path above should normally use
`opDist_rz_completion_le_of_region`. -/
theorem opDist_rz_completion_le_of_close
    (θ : ℝ) {u t : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hu : ‖u - rzPhase θ‖ ≤ ε / 4)
    (ht : ‖t‖ ≤ ε / 4) :
    opDist (rz θ) (completionMatrix u t) ≤ ε := by
  have hu' : ‖rzPhase θ - u‖ ≤ ε / 4 := by
    simpa [norm_sub_rev] using hu
  have hradius :
      ‖rzPhase θ - u‖ ^ 2 + ‖t‖ ^ 2 ≤ ε ^ 2 := by
    have hε4_nonneg : 0 ≤ ε / 4 := by positivity
    have hu_sq : ‖rzPhase θ - u‖ ^ 2 ≤ (ε / 4) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hε4_nonneg).2 hu'
    have ht_sq : ‖t‖ ^ 2 ≤ (ε / 4) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hε4_nonneg).2 ht
    have hsum : ‖rzPhase θ - u‖ ^ 2 + ‖t‖ ^ 2 ≤ (ε / 4) ^ 2 + (ε / 4) ^ 2 :=
      add_le_add hu_sq ht_sq
    have hsmall : (ε / 4) ^ 2 + (ε / 4) ^ 2 ≤ ε ^ 2 := by
      nlinarith [sq_nonneg ε]
    exact hsum.trans hsmall
  unfold opDist
  apply (sq_le_sq₀ (norm_nonneg (rz θ - completionMatrix u t)) (le_of_lt hε)).1
  rw [opNorm_sq_completion_error θ u t]
  exact hradius

end MatrixCompletion

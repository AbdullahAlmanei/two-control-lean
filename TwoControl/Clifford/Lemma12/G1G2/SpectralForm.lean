import TwoControl.Clifford.Lemma12.G1G2.AxisRotation

namespace TwoControl
namespace Clifford
namespace Lemma12
namespace G1G2

open Universal
open Matrix

/-!
# Every determinant-one unitary is an axis rotation

Paper Lemma `from-unitary-to-exponentiated-hamiltonian`
(Nielsen–Chuang, Exercise 4.8): for any `2×2` unitary `G` with `det G = 1`
there is a Hermitian `A` with `A² = I` and a real `α` such that
`G = e^{iαA}`.  In `axisRotation` language: `G = axisRotation n α` for a unit
vector `n` and `α ∈ [0, π]` (the Hermitian `A` is `pauliVec n`).

The proof is elementary: unitarity plus `det = 1` force the SU(2) shape
`![![a, b], ![-conj b, conj a]]`, which is `su2Pair a.re (b.im, b.re, a.im)`;
then `α = arccos a.re` and normalizing the vector part gives the axis.
-/

theorem su2_eq_axisRotation (U : Square 2)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ (n : EuclideanSpace ℝ (Fin 3)) (α : ℝ),
      ‖n‖ = 1 ∧ 0 ≤ α ∧ α ≤ Real.pi ∧ U = axisRotation n α := by
  -- Entry equations from unitarity and the determinant.
  have hrow : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hcol : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hrow00 :
      U 0 0 * (starRingEnd ℂ) (U 0 0) + U 0 1 * (starRingEnd ℂ) (U 0 1) = 1 := by
    have h := (Matrix.ext_iff.mpr hrow) 0 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply, RCLike.star_def] using h
  have hcol00 :
      (starRingEnd ℂ) (U 0 0) * U 0 0 + (starRingEnd ℂ) (U 1 0) * U 1 0 = 1 := by
    have h := (Matrix.ext_iff.mpr hcol) 0 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply, RCLike.star_def] using h
  have hcol01 :
      (starRingEnd ℂ) (U 0 0) * U 0 1 + (starRingEnd ℂ) (U 1 0) * U 1 1 = 0 := by
    have h := (Matrix.ext_iff.mpr hcol) 0 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply, RCLike.star_def] using h
  have hcol11 :
      (starRingEnd ℂ) (U 0 1) * U 0 1 + (starRingEnd ℂ) (U 1 1) * U 1 1 = 1 := by
    have h := (Matrix.ext_iff.mpr hcol) 1 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply, RCLike.star_def] using h
  have hdet' : U 0 0 * U 1 1 - U 0 1 * U 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    exact hdet
  -- The SU(2) shape: `d = conj a`, `c = -conj b`.
  have hd : U 1 1 = (starRingEnd ℂ) (U 0 0) := by
    linear_combination (starRingEnd ℂ) (U 0 0) * hdet' + U 1 0 * hcol01 -
      U 1 1 * hcol00
  have hcol01c :
      U 0 0 * (starRingEnd ℂ) (U 0 1) + U 1 0 * (starRingEnd ℂ) (U 1 1) = 0 := by
    have h := congrArg (starRingEnd ℂ) hcol01
    simpa using h
  have hc : U 1 0 = -((starRingEnd ℂ) (U 0 1)) := by
    linear_combination (-(U 1 0)) * hcol11 + U 1 1 * hcol01c -
      (starRingEnd ℂ) (U 0 1) * hdet'
  -- The su2Pair coordinates.
  set t : ℝ := (U 0 0).re with ht
  set u : EuclideanSpace ℝ (Fin 3) :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm ![(U 0 1).im, (U 0 1).re, (U 0 0).im]
    with hu
  have hu0 : u 0 = (U 0 1).im := rfl
  have hu1 : u 1 = (U 0 1).re := rfl
  have hu2 : u 2 = (U 0 0).im := rfl
  have hUsu2 : U = su2Pair t u := by
    ext i j
    fin_cases i <;> fin_cases j
    · show U 0 0 = su2Pair t u 0 0
      rw [su2Pair_00, hu2, ht]
      apply Complex.ext <;> simp
    · show U 0 1 = su2Pair t u 0 1
      rw [su2Pair_01, hu0, hu1]
      apply Complex.ext <;> simp
    · show U 1 0 = su2Pair t u 1 0
      rw [su2Pair_10, hu0, hu1, hc]
      apply Complex.ext <;> simp
    · show U 1 1 = su2Pair t u 1 1
      rw [su2Pair_11, hu2, ht, hd]
      apply Complex.ext <;> simp
  -- The norm relation `t² + ‖u‖² = 1`.
  have hnormC :
      ((Complex.normSq (U 0 0) + Complex.normSq (U 0 1) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj, ← Complex.mul_conj]
    simpa using hrow00
  have hnorm_re : Complex.normSq (U 0 0) + Complex.normSq (U 0 1) = 1 :=
    Complex.ofReal_inj.mp hnormC
  have hu_norm_sq : ‖u‖ ^ 2 = (U 0 1).im ^ 2 + (U 0 1).re ^ 2 + (U 0 0).im ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, hu0, hu1, hu2]
    simp only [Real.norm_eq_abs, sq_abs]
  have hnorm_sq : t ^ 2 + ‖u‖ ^ 2 = 1 := by
    rw [hu_norm_sq, ht]
    have h := hnorm_re
    rw [Complex.normSq_apply, Complex.normSq_apply] at h
    nlinarith [h]
  have ht_lower : -1 ≤ t := by nlinarith [sq_nonneg (‖u‖), sq_nonneg (t + 1)]
  have ht_upper : t ≤ 1 := by nlinarith [sq_nonneg (‖u‖), sq_nonneg (t - 1)]
  by_cases hzero : ‖u‖ = 0
  · -- Degenerate case: `U = ±1`; use the standard z-axis.
    have hu_zero : u = 0 := norm_eq_zero.mp hzero
    have ht_sq : t ^ 2 = 1 := by
      rw [hzero] at hnorm_sq
      nlinarith [hnorm_sq]
    have hcases : (t - 1) * (t + 1) = 0 := by nlinarith [ht_sq]
    rcases mul_eq_zero.mp hcases with h1 | h1
    · -- `t = 1`, `α = 0`.
      refine ⟨standardZAxis, 0, standardZAxis_unit, le_refl 0, Real.pi_pos.le, ?_⟩
      rw [axisRotation_eq_su2Pair standardZAxis standardZAxis_unit 0,
        Real.cos_zero, Real.sin_zero, zero_smul, hUsu2, hu_zero,
        show t = 1 by linarith]
    · -- `t = -1`, `α = π`.
      refine ⟨standardZAxis, Real.pi, standardZAxis_unit, Real.pi_pos.le,
        le_refl Real.pi, ?_⟩
      rw [axisRotation_eq_su2Pair standardZAxis standardZAxis_unit Real.pi,
        Real.cos_pi, Real.sin_pi, zero_smul, hUsu2, hu_zero,
        show t = -1 by linarith]
  · -- Generic case: normalize the vector part.
    refine ⟨‖u‖⁻¹ • u, Real.arccos t, ?_, Real.arccos_nonneg t,
      Real.arccos_le_pi t, ?_⟩
    · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u),
        inv_mul_cancel₀ hzero]
    · have hn_unit : ‖(‖u‖⁻¹ • u : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u),
          inv_mul_cancel₀ hzero]
      rw [axisRotation_eq_su2Pair _ hn_unit, Real.cos_arccos ht_lower ht_upper,
        Real.sin_arccos]
      have hsin : Real.sqrt (1 - t ^ 2) = ‖u‖ := by
        rw [show 1 - t ^ 2 = ‖u‖ ^ 2 by linarith [hnorm_sq]]
        exact Real.sqrt_sq (norm_nonneg u)
      rw [hsin, smul_smul, mul_inv_cancel₀ hzero, one_smul]
      exact hUsu2

end G1G2
end Lemma12
end Clifford
end TwoControl

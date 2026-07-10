import TwoControl.Clifford.Lemma12.G1G2.Generators
import TwoControl.Clifford.Lemma12.G1G2.SpectralForm

namespace TwoControl
namespace Clifford
namespace Lemma12
namespace G1G2

open Universal
open Matrix

/-!
# Identifying the rotation angles of `G₁, G₂` by their traces

Paper Lemmas `a-specific-lambda-is-irrational` and `approximate-g1-a-g2-b`
(the angle-pinning part): writing `Gᵢ = axisRotation nᵢ αᵢ`
(via `su2_eq_axisRotation`) and using `Tr(Gᵢ) = 2 cos αᵢ`
(`trace_axisRotation`), the computed trace forces

  `(2 cos αᵢ)² = 1 + 1/√2`,

and any angle with that squared cosine is an irrational multiple of `π`.

We work with the *square* throughout: the paper's
`λ = (1/π)·arccos(½√(1+1/√2))` never needs to be named, the sign of
`cos αᵢ` never needs to be determined, and the algebraic-integer argument
below only uses the square anyway (`x = 2cos(απ)` gives `x² - 1 = 1/√2` and
`(x² - 1)² = 1/2`, which is not an algebraic integer).
-/

private lemma csqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- `1/2` is not an algebraic integer (its minimal polynomial `2X - 1` is not
monic; concretely, `ℤ` is integrally closed in `ℚ`). -/
private lemma not_isIntegral_half : ¬ IsIntegral ℤ ((1 : ℂ) / 2) := by
  intro h
  have hq : IsIntegral ℤ ((1 : ℚ) / 2) := by
    refine (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).mp ?_
    simpa using h
  obtain ⟨z, hz⟩ :=
    IsIntegrallyClosed.algebraMap_eq_of_integral (R := ℤ) (K := ℚ) hq
  norm_num at hz
  have hz' : (2 : ℚ) * (z : ℚ) = 1 := by nlinarith
  have hzint : (2 : ℤ) * z = 1 := by exact_mod_cast hz'
  omega

/-- Paper Lemma `a-specific-lambda-is-irrational`, in sign-free form: any
angle `α` with `(2 cos α)² = 1 + √2/2` is an irrational multiple of `2π`.

If `α/(2π)` were rational, `ζ = e^{iα}` would be a root of unity, hence an
algebraic integer; then `x = ζ + ζ⁻¹ = 2 cos α` and `(x² - 1)² = 1/2` would
be algebraic integers, contradicting `not_isIntegral_half`. -/
theorem irrational_div_two_pi_of_four_cos_sq {α : ℝ}
    (h : (2 * Real.cos α) ^ 2 = 1 + Real.sqrt 2 / 2) :
    Irrational (α / (2 * Real.pi)) := by
  intro ⟨q, hq⟩
  obtain ⟨n, hnpos, hroot⟩ :=
    rational_angle_is_rootOfUnity (α / (2 * Real.pi)) ⟨q, hq⟩
  have harg : Complex.I * (2 * (Real.pi : ℂ) * ((α / (2 * Real.pi) : ℝ) : ℂ)) =
      (α : ℂ) * Complex.I := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  rw [harg] at hroot
  have hζ_ne : Complex.exp ((α : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hζ_int : IsIntegral ℤ (Complex.exp ((α : ℂ) * Complex.I)) :=
    IsIntegral.of_pow hnpos (by rw [hroot]; exact isIntegral_one)
  have hζ_inv :
      (Complex.exp ((α : ℂ) * Complex.I))⁻¹ =
        Complex.exp ((α : ℂ) * Complex.I) ^ (n - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hnpos, hroot]
  have hx_int :
      IsIntegral ℤ
        (Complex.exp ((α : ℂ) * Complex.I) +
          (Complex.exp ((α : ℂ) * Complex.I))⁻¹) := by
    rw [hζ_inv]
    exact hζ_int.add (hζ_int.pow (n - 1))
  have hx_eq :
      Complex.exp ((α : ℂ) * Complex.I) +
          (Complex.exp ((α : ℂ) * Complex.I))⁻¹ =
        ((2 * Real.cos α : ℝ) : ℂ) := by
    have := exp_I_trace α
    push_cast at this ⊢
    exact this
  have hw_int :
      IsIntegral ℤ
        ((Complex.exp ((α : ℂ) * Complex.I) +
            (Complex.exp ((α : ℂ) * Complex.I))⁻¹) ^ 2 - 1) :=
    (hx_int.pow 2).sub isIntegral_one
  have hw_eq :
      (Complex.exp ((α : ℂ) * Complex.I) +
          (Complex.exp ((α : ℂ) * Complex.I))⁻¹) ^ 2 - 1 =
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    rw [hx_eq]
    have hcast : ((2 * Real.cos α : ℝ) : ℂ) ^ 2 =
        (((2 * Real.cos α) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, h]
    push_cast
    ring
  have hhalf_int : IsIntegral ℤ ((1 : ℂ) / 2) := by
    have hsq :
        ((Complex.exp ((α : ℂ) * Complex.I) +
            (Complex.exp ((α : ℂ) * Complex.I))⁻¹) ^ 2 - 1) ^ 2 = (1 : ℂ) / 2 := by
      rw [hw_eq]
      rw [show (((Real.sqrt 2 / 2 : ℝ) : ℂ)) ^ 2 =
          ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 / 4 by push_cast; ring, csqrt2_sq]
      norm_num
    rw [← hsq]
    exact hw_int.pow 2
  exact not_isIntegral_half hhalf_int

/-- Package the axis data for a gate whose squared trace is `1 + √2/2`:
a unit axis, the rotation form, the pinned squared cosine, a strictly
positive sine, and irrationality of the angle over `2π`. -/
private theorem axis_data_of_trace_sq (M : Square 2)
    (hmem : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : M.det = 1)
    (htr : Matrix.trace M ^ 2 = ((1 + Real.sqrt 2 / 2 : ℝ) : ℂ)) :
    ∃ (n : EuclideanSpace ℝ (Fin 3)) (α : ℝ),
      ‖n‖ = 1 ∧ M = axisRotation n α ∧
      Real.cos α ^ 2 = (2 + Real.sqrt 2) / 8 ∧
      0 < Real.sin α ∧ Irrational (α / (2 * Real.pi)) := by
  obtain ⟨n, α, hn, hα0, hαpi, hM⟩ := su2_eq_axisRotation M hmem hdet
  have htrace : Matrix.trace M = 2 * (Real.cos α : ℂ) := by
    rw [hM]
    exact trace_axisRotation n hn α
  have hcos_sq : (2 * Real.cos α) ^ 2 = 1 + Real.sqrt 2 / 2 := by
    have h := htr
    rw [htrace] at h
    exact_mod_cast h
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt2_lt : Real.sqrt 2 < 6 := by nlinarith
  have hcos2 : Real.cos α ^ 2 = (2 + Real.sqrt 2) / 8 := by
    have h4 : 4 * Real.cos α ^ 2 = 1 + Real.sqrt 2 / 2 := by
      linear_combination hcos_sq
    linarith
  have hα_ne0 : α ≠ 0 := by
    intro hzero
    rw [hzero, Real.cos_zero] at hcos2
    norm_num at hcos2
    linarith
  have hα_nepi : α ≠ Real.pi := by
    intro hpi
    rw [hpi, Real.cos_pi] at hcos2
    norm_num at hcos2
    linarith
  have hsin_pos : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_ne hα0 (Ne.symm hα_ne0))
      (lt_of_le_of_ne hαpi hα_nepi)
  exact ⟨n, α, hn, hM, hcos2, hsin_pos,
    irrational_div_two_pi_of_four_cos_sq hcos_sq⟩

/-- The axis data of `G₁`. -/
theorem g1_axis_data :
    ∃ (n : EuclideanSpace ℝ (Fin 3)) (α : ℝ),
      ‖n‖ = 1 ∧ g1 = axisRotation n α ∧
      Real.cos α ^ 2 = (2 + Real.sqrt 2) / 8 ∧
      0 < Real.sin α ∧ Irrational (α / (2 * Real.pi)) :=
  axis_data_of_trace_sq g1 g1_mem_unitaryGroup g1_det g1_trace_sq

/-- The axis data of `G₂`. -/
theorem g2_axis_data :
    ∃ (n : EuclideanSpace ℝ (Fin 3)) (α : ℝ),
      ‖n‖ = 1 ∧ g2 = axisRotation n α ∧
      Real.cos α ^ 2 = (2 + Real.sqrt 2) / 8 ∧
      0 < Real.sin α ∧ Irrational (α / (2 * Real.pi)) :=
  axis_data_of_trace_sq g2 g2_mem_unitaryGroup g2_det g2_trace_sq

end G1G2
end Lemma12
end Clifford
end TwoControl

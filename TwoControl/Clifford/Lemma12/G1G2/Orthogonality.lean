import TwoControl.Clifford.Lemma12.G1G2.AngleIdentification

namespace TwoControl
namespace Clifford
namespace Lemma12
namespace G1G2

open Universal
open Matrix

/-!
# The axes of `G₁` and `G₂` are orthogonal

Paper Lemma `a1-and-a2-anticommute`: the Hermitian generators of `G₁, G₂`
anticommute, i.e. (in `axisRotation` language) the rotation axes satisfy
`⟪n₁, n₂⟫ = 0`.

Proof: `Tr(G₁G₂) = 2(cos α₁ cos α₂ - sin α₁ sin α₂ · ⟪n₁,n₂⟫)`
(`trace_axisRotation_mul`), and the finite computation `g1_g2_trace` gives
`Tr(G₁G₂) = (2 + √2)/4`.  The pinned squared cosines force
`cos α₁ cos α₂ = ±(2 + √2)/8`; with the `+` sign the inner product term
vanishes, and the `-` sign would force `|⟪n₁,n₂⟫| > 1`, which is impossible
by Cauchy–Schwarz.
-/

/-- The combined axis data for `G₁, G₂`: unit axes, rotation forms,
irrational angles, and orthogonal axes. -/
theorem g_axes_data :
    ∃ (n₁ n₂ : EuclideanSpace ℝ (Fin 3)) (α₁ α₂ : ℝ),
      ‖n₁‖ = 1 ∧ ‖n₂‖ = 1 ∧
      g1 = axisRotation n₁ α₁ ∧ g2 = axisRotation n₂ α₂ ∧
      Irrational (α₁ / (2 * Real.pi)) ∧ Irrational (α₂ / (2 * Real.pi)) ∧
      inner ℝ n₁ n₂ = (0 : ℝ) := by
  obtain ⟨n₁, α₁, hn₁, hg1, hcos₁, hsin₁, hirr₁⟩ := g1_axis_data
  obtain ⟨n₂, α₂, hn₂, hg2, hcos₂, hsin₂, hirr₂⟩ := g2_axis_data
  refine ⟨n₁, n₂, α₁, α₂, hn₁, hn₂, hg1, hg2, hirr₁, hirr₂, ?_⟩
  -- The trace of the product, in terms of the axis inner product.
  have htr : Matrix.trace (g1 * g2) =
      2 * ((Real.cos α₁ * Real.cos α₂ -
        Real.sin α₁ * Real.sin α₂ * inner ℝ n₁ n₂ : ℝ) : ℂ) := by
    rw [hg1, hg2]
    exact trace_axisRotation_mul n₁ n₂ hn₁ hn₂ α₁ α₂
  have hreal :
      2 * (Real.cos α₁ * Real.cos α₂ -
        Real.sin α₁ * Real.sin α₂ * inner ℝ n₁ n₂) = (2 + Real.sqrt 2) / 4 := by
    have h := g1_g2_trace
    rw [htr] at h
    exact_mod_cast h
  -- Numeric facts about √2.
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  -- Cauchy–Schwarz.
  have hk_le : |inner ℝ n₁ n₂| ≤ 1 := by
    have h := abs_real_inner_le_norm n₁ n₂
    rw [hn₁, hn₂] at h
    simpa using h
  obtain ⟨hk_lower, hk_upper⟩ := abs_le.mp hk_le
  -- Squared sines.
  have hsin_sq₁ : Real.sin α₁ ^ 2 = (6 - Real.sqrt 2) / 8 := by
    have h := Real.sin_sq_add_cos_sq α₁
    linarith [hcos₁]
  have hsin_sq₂ : Real.sin α₂ ^ 2 = (6 - Real.sqrt 2) / 8 := by
    have h := Real.sin_sq_add_cos_sq α₂
    linarith [hcos₂]
  have hss_pos : 0 < Real.sin α₁ * Real.sin α₂ := mul_pos hsin₁ hsin₂
  -- The cosine product is `±(2+√2)/8`.
  have hfactor :
      (Real.cos α₁ * Real.cos α₂ - (2 + Real.sqrt 2) / 8) *
        (Real.cos α₁ * Real.cos α₂ + (2 + Real.sqrt 2) / 8) = 0 := by
    have hprod_sq : (Real.cos α₁ * Real.cos α₂) ^ 2 =
        ((2 + Real.sqrt 2) / 8) ^ 2 := by
      rw [mul_pow, hcos₁, hcos₂]
      ring
    linear_combination hprod_sq
  rcases mul_eq_zero.mp hfactor with hcase | hcase
  · -- `cos α₁ cos α₂ = (2+√2)/8`: the inner-product term vanishes.
    have hcc : Real.cos α₁ * Real.cos α₂ = (2 + Real.sqrt 2) / 8 := by linarith
    have hss_k : Real.sin α₁ * Real.sin α₂ * inner ℝ n₁ n₂ = 0 := by linarith
    rcases mul_eq_zero.mp hss_k with h | h
    · exact absurd h (ne_of_gt hss_pos)
    · exact h
  · -- `cos α₁ cos α₂ = -(2+√2)/8`: impossible by Cauchy–Schwarz.
    exfalso
    have hcc : Real.cos α₁ * Real.cos α₂ = -((2 + Real.sqrt 2) / 8) := by linarith
    have hss_k : Real.sin α₁ * Real.sin α₂ * inner ℝ n₁ n₂ =
        -((2 + Real.sqrt 2) / 4) := by linarith
    -- Square the previous identity and compare with `sin² sin² · k² ≤ sin² sin²`.
    have hss_k_sq :
        (Real.sin α₁ * Real.sin α₂) ^ 2 * inner ℝ n₁ n₂ ^ 2 =
          ((2 + Real.sqrt 2) / 4) ^ 2 := by
      have h := congrArg (fun x : ℝ => x ^ 2) hss_k
      simpa [mul_pow, neg_sq] using h
    have hk_sq : inner ℝ n₁ n₂ ^ 2 ≤ 1 := by nlinarith
    have hss_sq : (Real.sin α₁ * Real.sin α₂) ^ 2 =
        ((6 - Real.sqrt 2) / 8) ^ 2 := by
      rw [mul_pow, hsin_sq₁, hsin_sq₂]
      ring
    nlinarith [hss_k_sq, hss_sq, hk_sq, sq_nonneg (Real.sin α₁ * Real.sin α₂)]

end G1G2
end Lemma12
end Clifford
end TwoControl

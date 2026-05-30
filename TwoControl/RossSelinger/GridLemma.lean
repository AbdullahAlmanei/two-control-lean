import MatrixCompletion.Completion
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Archimedean

namespace TwoControl.RossSelinger

open MatrixCompletion
open DyadicCyclotomic

/-!
Phase-2 grid existence for the Ross-Selinger oracle layer.

For the oracle theorem we only need existence of a grid point in the
epsilon-region whose bullet conjugate lies in the closed unit disk.  The proof
below uses the Gaussian dyadic subgrid (`b = d = 0`) of `D[ω]`: dyadic Gaussian
rationals are dense in `ℂ`, and for this subgrid the bullet conjugate is the
same point.
-/

private theorem sqrtTwoComplex_pow_two_mul (m : ℕ) :
    sqrtTwoComplex ^ (2 * m) = (2 : ℂ) ^ m := by
  rw [pow_mul, sqrtTwoComplex_sq]

private theorem neg_sqrtTwoComplex_pow_two_mul (m : ℕ) :
    (((-Real.sqrt 2 : ℝ) : ℂ) ^ (2 * m)) = (2 : ℂ) ^ m := by
  rw [pow_mul]
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt]

private noncomputable def dyadicReal (m : ℕ) (a : ℤ) : ℝ :=
  (a : ℝ) / (2 : ℝ) ^ m

private noncomputable def gaussianDyadic (m : ℕ) (a c : ℤ) : ℂ :=
  (dyadicReal m a : ℂ) + (dyadicReal m c : ℂ) * Complex.I

private theorem coord_eq_gaussian (m : ℕ) (a c : ℤ) :
    ((a : ℂ) + (c : ℂ) * Complex.I) / (sqrtTwoComplex ^ (2 * m)) =
      gaussianDyadic m a c := by
  apply Complex.ext <;>
    simp [gaussianDyadic, dyadicReal, sqrtTwoComplex_pow_two_mul,
      Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
    ring

private theorem gaussianDyadic_coord (m : ℕ) (a c : ℤ) :
    gaussianDyadic m a c =
      ((a : ℂ) + (c : ℂ) * Complex.I) / (sqrtTwoComplex ^ (2 * m)) :=
  (coord_eq_gaussian m a c).symm

private theorem gaussianDyadic_re (m : ℕ) (a c : ℤ) :
    (gaussianDyadic m a c).re = dyadicReal m a := by
  simp [gaussianDyadic]

private theorem gaussianDyadic_im (m : ℕ) (a c : ℤ) :
    (gaussianDyadic m a c).im = dyadicReal m c := by
  simp [gaussianDyadic]

private theorem gaussianDyadic_in_dyadic (m : ℕ) (a c : ℤ) :
    InDyadicCyclotomic (gaussianDyadic m a c) := by
  refine ⟨2 * m, a, 0, c, 0, ?_⟩
  rw [gaussianDyadic_coord]
  simp

private theorem gaussianDyadic_bullet_self (m : ℕ) (a c : ℤ) :
    IsBulletConj (gaussianDyadic m a c) (gaussianDyadic m a c) := by
  refine ⟨2 * m, a, 0, c, 0, ?_, ?_⟩
  · rw [gaussianDyadic_coord]
    simp
  · rw [gaussianDyadic_coord]
    simp only [Int.cast_zero, zero_mul, sub_zero]
    rw [sqrtTwoComplex_pow_two_mul, neg_sqrtTwoComplex_pow_two_mul]

private theorem dyadic_real_floor_error
    (x : ℝ) {δ : ℝ} (_hδ : 0 < δ) {m : ℕ}
    (hsmall : 1 / (2 : ℝ) ^ m < δ) :
    ∃ a : ℤ, |(a : ℝ) / (2 : ℝ) ^ m - x| < δ := by
  let q : ℝ := (2 : ℝ) ^ m
  have hqpos : 0 < q := by positivity
  let a : ℤ := ⌊x * q⌋
  refine ⟨a, ?_⟩
  have hfloor_le : (a : ℝ) ≤ x * q := by
    dsimp [a]
    exact Int.floor_le _
  have hfloor_lt : x * q < (a : ℝ) + 1 := by
    dsimp [a]
    exact Int.lt_floor_add_one _
  have hle : (a : ℝ) / q ≤ x := by
    rw [div_le_iff₀ hqpos]
    simpa [mul_comm] using hfloor_le
  have hlt : x - (a : ℝ) / q < 1 / q := by
    have hxlt : x < ((a : ℝ) + 1) / q := by
      rw [lt_div_iff₀ hqpos]
      simpa [mul_comm] using hfloor_lt
    have hcalc : ((a : ℝ) + 1) / q - (a : ℝ) / q = 1 / q := by
      field_simp [ne_of_gt hqpos]
      ring
    calc
      x - (a : ℝ) / q < ((a : ℝ) + 1) / q - (a : ℝ) / q := by
        linarith
      _ = 1 / q := hcalc
  have habs : |(a : ℝ) / q - x| = x - (a : ℝ) / q := by
    have hnonpos : (a : ℝ) / q - x ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    ring
  rw [show (2 : ℝ) ^ m = q from rfl]
  rw [habs]
  exact hlt.trans hsmall

private theorem exists_gaussianDyadic_near
    (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, ∃ a c : ℤ, ‖gaussianDyadic m a c - z‖ < δ := by
  obtain ⟨m, hm⟩ :=
    add_one_pow_unbounded_of_pos (R := ℝ) (2 / δ)
      (by norm_num : (0 : ℝ) < 1)
  have htwo : (1 : ℝ) + 1 = 2 := by norm_num
  have hpow : 2 / δ < (2 : ℝ) ^ m := by
    simpa [htwo] using hm
  have hsmall : 1 / (2 : ℝ) ^ m < δ / 2 := by
    have hδ2 : 0 < δ / 2 := by positivity
    have hleft : 1 / (δ / 2) < (2 : ℝ) ^ m := by
      have h_inv : 1 / (δ / 2) = 2 / δ := by field_simp [hδ.ne']
      rw [h_inv]
      exact hpow
    exact (one_div_lt (by positivity : 0 < (2 : ℝ) ^ m) hδ2).2 hleft
  rcases dyadic_real_floor_error z.re (half_pos hδ) hsmall with ⟨a, ha⟩
  rcases dyadic_real_floor_error z.im (half_pos hδ) hsmall with ⟨c, hc⟩
  refine ⟨m, a, c, ?_⟩
  have hre : |(gaussianDyadic m a c - z).re| < δ / 2 := by
    rw [Complex.sub_re, gaussianDyadic_re]
    simpa [dyadicReal] using ha
  have him : |(gaussianDyadic m a c - z).im| < δ / 2 := by
    rw [Complex.sub_im, gaussianDyadic_im]
    simpa [dyadicReal] using hc
  calc
    ‖gaussianDyadic m a c - z‖
        ≤ |(gaussianDyadic m a c - z).re| +
            |(gaussianDyadic m a c - z).im| :=
          Complex.norm_le_abs_re_add_abs_im _
    _ < δ / 2 + δ / 2 := add_lt_add hre him
    _ = δ := by ring

private theorem star_mul_self_rzPhase (θ : ℝ) :
    star (rzPhase θ) * rzPhase θ = 1 := by
  have hnorm : Complex.normSq (rzPhase θ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, rzPhase_norm]
    norm_num
  have h := Complex.normSq_eq_conj_mul_self (z := rzPhase θ)
  rw [hnorm] at h
  simpa using h.symm

private theorem grid_candidate_large_epsilon
    (θ : ℝ) {ε : ℝ} (hlarge : 1 - ε ^ 2 / 2 ≤ 0) :
    ∃ u : ℂ,
      InDyadicCyclotomic u ∧
      InEpsilonRegion θ ε u ∧
      ∃ ub : ℂ, IsBulletConj u ub ∧ InClosedUnitDisk ub := by
  refine ⟨0, InDyadicCyclotomic.zero, ?_, ?_⟩
  · constructor
    · simp [InClosedUnitDisk]
    · simpa using hlarge
  · refine ⟨0, ?_, ?_⟩
    · simpa [gaussianDyadic, dyadicReal] using gaussianDyadic_bullet_self 0 0 0
    · simp [InClosedUnitDisk]

private theorem grid_candidate_small_epsilon
    (θ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hsmallCase : ¬ 1 - ε ^ 2 / 2 ≤ 0) :
    ∃ u : ℂ,
      InDyadicCyclotomic u ∧
      InEpsilonRegion θ ε u ∧
      ∃ ub : ℂ, IsBulletConj u ub ∧ InClosedUnitDisk ub := by
  let δ : ℝ := ε ^ 2 / 4
  let ρ : ℝ := 1 - δ
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hρnonneg : 0 ≤ ρ := by
    have hlt : ε ^ 2 / 2 < 1 := by linarith [lt_of_not_ge hsmallCase]
    dsimp [ρ, δ]
    nlinarith [sq_nonneg ε]
  let r := rzPhase θ
  let target : ℂ := (ρ : ℂ) * r
  rcases exists_gaussianDyadic_near target hδpos with ⟨m, a, c, hclose⟩
  let u := gaussianDyadic m a c
  have hdist_le : ‖u - target‖ ≤ δ := le_of_lt hclose
  have htarget_norm : ‖target‖ = ρ := by
    simp [target, r, rzPhase_norm, abs_of_nonneg hρnonneg]
  have huDisk : InClosedUnitDisk u := by
    have htri : ‖u‖ ≤ ‖target‖ + ‖u - target‖ := by
      simpa [norm_sub_rev, add_comm] using norm_le_norm_sub_add u target
    calc
      ‖u‖ ≤ ‖target‖ + ‖u - target‖ := htri
      _ = ρ + ‖u - target‖ := by rw [htarget_norm]
      _ ≤ ρ + δ := add_le_add (le_refl ρ) hdist_le
      _ = 1 := by simp [ρ]
  have htarget_dist_r : ‖target - r‖ = δ := by
    have hdiff : target - r = ((ρ - 1 : ℝ) : ℂ) * r := by
      simp [target]
      ring
    rw [hdiff, norm_mul, rzPhase_norm, mul_one, Complex.norm_real]
    have habs : |ρ - 1| = δ := by
      have : ρ - 1 = -δ := by simp [ρ]
      rw [this, abs_neg, abs_of_nonneg hδpos.le]
    exact habs
  have hu_close_r : ‖u - r‖ < ε ^ 2 / 2 := by
    have htri : ‖u - r‖ ≤ ‖u - target‖ + ‖target - r‖ := by
      have hsum : (u - target) + (target - r) = u - r := by ring
      calc
        ‖u - r‖ = ‖(u - target) + (target - r)‖ := by rw [hsum]
        _ ≤ ‖u - target‖ + ‖target - r‖ :=
          norm_add_le (u - target) (target - r)
    calc
      ‖u - r‖ ≤ ‖u - target‖ + ‖target - r‖ := htri
      _ < δ + δ := by
        rw [htarget_dist_r]
        exact add_lt_add_of_lt_of_le hclose le_rfl
      _ = ε ^ 2 / 2 := by
        simp [δ]
        ring
  have hRegionRe : 1 - ε ^ 2 / 2 ≤ (star (rzPhase θ) * u).re := by
    have hmul_decomp :
        star (rzPhase θ) * u =
          1 + star (rzPhase θ) * (u - rzPhase θ) := by
      calc
        star (rzPhase θ) * u =
            star (rzPhase θ) * (rzPhase θ + (u - rzPhase θ)) := by
              congr 1
              ring
        _ = star (rzPhase θ) * rzPhase θ +
              star (rzPhase θ) * (u - rzPhase θ) := by ring
        _ = 1 + star (rzPhase θ) * (u - rzPhase θ) := by
              rw [star_mul_self_rzPhase]
    rw [hmul_decomp]
    have herr_abs :
        |(star (rzPhase θ) * (u - rzPhase θ)).re| < ε ^ 2 / 2 := by
      calc
        |(star (rzPhase θ) * (u - rzPhase θ)).re|
            ≤ ‖star (rzPhase θ) * (u - rzPhase θ)‖ :=
              Complex.abs_re_le_norm _
        _ ≤ ‖star (rzPhase θ)‖ * ‖u - rzPhase θ‖ := norm_mul_le _ _
        _ = ‖u - rzPhase θ‖ := by simp [rzPhase_norm]
        _ < ε ^ 2 / 2 := by simpa [r] using hu_close_r
    have herr_lower :
        -ε ^ 2 / 2 ≤ (star (rzPhase θ) * (u - rzPhase θ)).re := by
      have := (abs_lt.mp herr_abs).1
      linarith
    simp only [Complex.add_re, Complex.one_re]
    linarith
  refine ⟨u, gaussianDyadic_in_dyadic m a c, ⟨huDisk, hRegionRe⟩, ?_⟩
  exact ⟨u, gaussianDyadic_bullet_self m a c, huDisk⟩

theorem grid_candidate_exists
    (θ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℂ,
      InDyadicCyclotomic u ∧
      InEpsilonRegion θ ε u ∧
      ∃ ub : ℂ, IsBulletConj u ub ∧ InClosedUnitDisk ub := by
  by_cases hlarge : 1 - ε ^ 2 / 2 ≤ 0
  · exact grid_candidate_large_epsilon θ hlarge
  · exact grid_candidate_small_epsilon θ hε hlarge

end RossSelinger
end TwoControl

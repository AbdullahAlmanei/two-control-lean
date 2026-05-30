import TwoControl.RossSelinger.GridLemma

namespace TwoControl.RossSelinger

open DyadicCyclotomic
open MatrixCompletion

/-!
Scaled-grid layer from Ross-Selinger Sections 5 and 7.

The algorithm enumerates `u ∈ D[ω]` in increasing least denominator exponent
such that

* `u` lies in the epsilon region around `rzPhase θ`; and
* the `sqrt 2`-conjugate of `u` lies in the unit disk.
-/

/-- A Ross-Selinger scaled-grid candidate for approximating `Rz θ`. -/
def ScaledGridCandidate (θ ε : ℝ) (u : ℂ) : Prop :=
  InDyadicCyclotomic u ∧
    InEpsilonRegion θ ε u ∧
    ∃ ubullet : ℂ, IsBulletConj u ubullet ∧ InClosedUnitDisk ubullet

/-- Fixed-denominator scaled grid problem. -/
def FixedDenominatorScaledGridCandidate (θ ε : ℝ) (k : ℕ) (u : ℂ) : Prop :=
  HasDenominatorExponent u k ∧
    InEpsilonRegion θ ε u ∧
    ∃ ubullet : ℂ, IsBulletConj u ubullet ∧ InClosedUnitDisk ubullet

/-- Data returned by the scaled-grid stage at denominator level `k`.

The geometric enumeration algorithm is deliberately separated from this
certificate.  Ross-Selinger search only consumes values carrying these proofs;
future executable grid code can produce this record from integer-coordinate
enumeration without changing the search/correctness layer. -/
structure RSCandidate (θ ε : ℝ) where
  level : ℕ
  u : ℂ
  hFixed : FixedDenominatorScaledGridCandidate θ ε level u
  /-- Ross-Selinger orders candidates by least denominator exponent, not merely
  by a chosen denominator presentation. -/
  hLeast : IsLeastDenominatorExponent u level

namespace RSCandidate

theorem hasDenominatorExponent {θ ε : ℝ} (candidate : RSCandidate θ ε) :
    HasDenominatorExponent candidate.u candidate.level :=
  candidate.hFixed.1

theorem isLeastDenominatorExponent {θ ε : ℝ} (candidate : RSCandidate θ ε) :
    IsLeastDenominatorExponent candidate.u candidate.level :=
  candidate.hLeast

theorem level_le_of_hasDenominatorExponent {θ ε : ℝ}
    (candidate : RSCandidate θ ε) {level : ℕ}
    (hlevel : HasDenominatorExponent candidate.u level) :
    candidate.level ≤ level :=
  candidate.hLeast.2 level hlevel

theorem inEpsilonRegion {θ ε : ℝ} (candidate : RSCandidate θ ε) :
    InEpsilonRegion θ ε candidate.u :=
  candidate.hFixed.2.1

theorem bullet_mem_closedUnitDisk {θ ε : ℝ} (candidate : RSCandidate θ ε) :
    ∃ ubullet : ℂ, IsBulletConj candidate.u ubullet ∧ InClosedUnitDisk ubullet :=
  candidate.hFixed.2.2

theorem inDyadicCyclotomic {θ ε : ℝ} (candidate : RSCandidate θ ε) :
    InDyadicCyclotomic candidate.u :=
  inDyadicCyclotomic_of_denominatorExponent candidate.hasDenominatorExponent

theorem scaledGridCandidate {θ ε : ℝ} (candidate : RSCandidate θ ε) :
    ScaledGridCandidate θ ε candidate.u :=
  ⟨candidate.inDyadicCyclotomic, candidate.inEpsilonRegion,
    candidate.bullet_mem_closedUnitDisk⟩

end RSCandidate

/-! ### Finite coordinate-box enumeration

The executable Ross-Selinger enumerator ultimately loops over integer
coordinates for

`u = (a + b√2 + (c + d√2)i) / √2^k`.

For arbitrary real `θ` and `ε`, deciding the epsilon-region predicates is not
computable yet, so the enumerator below is intentionally `noncomputable`: it
filters a finite coordinate box using classical decidability of propositions
and returns proof-carrying `RSCandidate`s.  This is still the real finite
search spine: every emitted candidate has the scaled-grid certificate, and
every admissible coordinate in the box is emitted.
-/

/-- Integer coordinates for a numerator in `ℤ[ω]`, written in the repository's
legacy basis `a + b√2 + (c + d√2)i`. -/
structure GridCoord where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq

namespace GridCoord

/-- The complex value represented by a numerator coordinate at denominator
level `k`. -/
noncomputable def value (coord : GridCoord) (k : ℕ) : ℂ :=
  (((coord.a : ℂ) + (coord.b : ℂ) * sqrtTwoComplex) +
      ((coord.c : ℂ) + (coord.d : ℂ) * sqrtTwoComplex) * Complex.I) /
    (sqrtTwoComplex ^ k)

/-- The `sqrt 2`-conjugate value of a coordinate at denominator level `k`. -/
noncomputable def bulletValue (coord : GridCoord) (k : ℕ) : ℂ :=
  (((coord.a : ℂ) - (coord.b : ℂ) * sqrtTwoComplex) +
      ((coord.c : ℂ) - (coord.d : ℂ) * sqrtTwoComplex) * Complex.I) /
    (((-Real.sqrt 2 : ℝ) : ℂ) ^ k)

theorem hasDenominatorExponent (coord : GridCoord) (k : ℕ) :
    HasDenominatorExponent (coord.value k) k := by
  exact ⟨coord.a, coord.b, coord.c, coord.d, rfl⟩

theorem isBulletConj (coord : GridCoord) (k : ℕ) :
    IsBulletConj (coord.value k) (coord.bulletValue k) := by
  exact ⟨k, coord.a, coord.b, coord.c, coord.d, rfl, rfl⟩

/-- The proof obligations needed to turn one coordinate into an
`RSCandidate`.  Denominator and bullet-conjugation facts are automatic from the
coordinate representation; the geometric predicates and least-denominator
claim remain proof-carrying. -/
def Admissible (θ ε : ℝ) (k : ℕ) (coord : GridCoord) : Prop :=
  InEpsilonRegion θ ε (coord.value k) ∧
    InClosedUnitDisk (coord.bulletValue k) ∧
      IsLeastDenominatorExponent (coord.value k) k

/-- Build the candidate carried by an admissible coordinate. -/
noncomputable def toCandidate {θ ε : ℝ} {k : ℕ}
    (coord : GridCoord) (hcoord : coord.Admissible θ ε k) :
    RSCandidate θ ε :=
  { level := k
    u := coord.value k
    hFixed :=
      ⟨coord.hasDenominatorExponent k, hcoord.1,
        ⟨coord.bulletValue k, coord.isBulletConj k, hcoord.2.1⟩⟩
    hLeast := hcoord.2.2 }

@[simp] theorem toCandidate_level {θ ε : ℝ} {k : ℕ}
    (coord : GridCoord) (hcoord : coord.Admissible θ ε k) :
    (coord.toCandidate hcoord).level = k := rfl

@[simp] theorem toCandidate_u {θ ε : ℝ} {k : ℕ}
    (coord : GridCoord) (hcoord : coord.Admissible θ ε k) :
    (coord.toCandidate hcoord).u = coord.value k := rfl

end GridCoord

/-- Symmetric integer range `[-B, B]`, represented as a list. -/
def intRange (B : ℕ) : List ℤ :=
  (List.range (2 * B + 1)).map fun n => (n : ℤ) - (B : ℤ)

theorem mem_intRange_iff {B : ℕ} {z : ℤ} :
    z ∈ intRange B ↔ -(B : ℤ) ≤ z ∧ z ≤ (B : ℤ) := by
  constructor
  · intro hz
    simp [intRange, List.mem_map] at hz
    rcases hz with ⟨n, hn, hzn⟩
    rw [← hzn]
    omega
  · intro hz
    simp [intRange, List.mem_map]
    refine ⟨(z + (B : ℤ)).toNat, ?_, ?_⟩
    ·
      have hnonneg : 0 ≤ z + (B : ℤ) := by omega
      omega
    · have hnonneg : 0 ≤ z + (B : ℤ) := by omega
      rw [Int.toNat_of_nonneg hnonneg]
      omega

/-- Finite box of numerator coordinates with each coordinate in `[-B, B]`. -/
def gridCoordsInBox (B : ℕ) : List GridCoord :=
  (intRange B).flatMap fun a =>
    (intRange B).flatMap fun b =>
      (intRange B).flatMap fun c =>
        (intRange B).map fun d =>
          { a := a, b := b, c := c, d := d }

theorem mem_gridCoordsInBox_iff {B : ℕ} {coord : GridCoord} :
    coord ∈ gridCoordsInBox B ↔
      coord.a ∈ intRange B ∧ coord.b ∈ intRange B ∧
        coord.c ∈ intRange B ∧ coord.d ∈ intRange B := by
  constructor
  · intro hcoord
    simp [gridCoordsInBox, List.mem_flatMap, List.mem_map] at hcoord
    rcases hcoord with ⟨a, ha, b, hb, c, hc, d, hd, hmk⟩
    cases hmk
    exact ⟨ha, hb, hc, hd⟩
  · intro hcoord
    rcases hcoord with ⟨ha, hb, hc, hd⟩
    simp [gridCoordsInBox, List.mem_flatMap, List.mem_map]
    exact ⟨coord.a, ha, coord.b, hb, coord.c, hc, coord.d, hd, rfl⟩

theorem mem_gridCoordsInBox_of_abs_le {B : ℕ} {coord : GridCoord}
    (ha : |(coord.a : ℝ)| ≤ (B : ℝ))
    (hb : |(coord.b : ℝ)| ≤ (B : ℝ))
    (hc : |(coord.c : ℝ)| ≤ (B : ℝ))
    (hd : |(coord.d : ℝ)| ≤ (B : ℝ)) :
    coord ∈ gridCoordsInBox B := by
  rw [mem_gridCoordsInBox_iff]
  have mk_mem (z : ℤ) (hz : |(z : ℝ)| ≤ (B : ℝ)) : z ∈ intRange B := by
    rw [mem_intRange_iff]
    have hz' := abs_le.mp hz
    constructor
    · exact_mod_cast hz'.1
    · exact_mod_cast hz'.2
  exact ⟨mk_mem coord.a ha, mk_mem coord.b hb,
    mk_mem coord.c hc, mk_mem coord.d hd⟩

/-- A simple coordinate box large enough for every fixed denominator level.
The two disk constraints imply the numerator coefficients are bounded by
`(sqrt 2)^k`; `2^k` is a convenient natural bound. -/
def gridCoordBound (k : ℕ) : ℕ :=
  2 ^ k

private theorem sqrtTwo_pow_le_two_pow (k : ℕ) :
    Real.sqrt 2 ^ k ≤ (2 : ℝ) ^ k := by
  have hs : Real.sqrt 2 ≤ (2 : ℝ) := by
    have hs_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hs_sq : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
      simpa [sq] using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  exact pow_le_pow_left₀ (Real.sqrt_nonneg 2) hs k

private noncomputable def GridCoord.numerator (coord : GridCoord) : ℂ :=
  ((coord.a : ℂ) + (coord.b : ℂ) * sqrtTwoComplex) +
    ((coord.c : ℂ) + (coord.d : ℂ) * sqrtTwoComplex) * Complex.I

private noncomputable def GridCoord.bulletNumerator (coord : GridCoord) : ℂ :=
  ((coord.a : ℂ) - (coord.b : ℂ) * sqrtTwoComplex) +
    ((coord.c : ℂ) - (coord.d : ℂ) * sqrtTwoComplex) * Complex.I

private theorem GridCoord.value_eq_numerator_div
    (coord : GridCoord) (k : ℕ) :
    coord.value k = coord.numerator / sqrtTwoComplex ^ k := rfl

private theorem GridCoord.bulletValue_eq_numerator_div
    (coord : GridCoord) (k : ℕ) :
    coord.bulletValue k =
      coord.bulletNumerator / (((-Real.sqrt 2 : ℝ) : ℂ) ^ k) := rfl

private theorem norm_sqrtTwoComplex_pow (k : ℕ) :
    ‖sqrtTwoComplex ^ k‖ = Real.sqrt 2 ^ k := by
  rw [norm_pow]
  have hnorm : ‖sqrtTwoComplex‖ = Real.sqrt 2 := by
    simp [sqrtTwoComplex, abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [hnorm]

private theorem norm_neg_sqrtTwoComplex_pow (k : ℕ) :
    ‖(((-Real.sqrt 2 : ℝ) : ℂ) ^ k)‖ = Real.sqrt 2 ^ k := by
  rw [norm_pow]
  have hnorm : ‖(((-Real.sqrt 2 : ℝ) : ℂ))‖ = Real.sqrt 2 := by
    simp [abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [hnorm]

private theorem numerator_norm_le_of_value_disk
    (coord : GridCoord) (k : ℕ)
    (hDisk : InClosedUnitDisk (coord.value k)) :
    ‖coord.numerator‖ ≤ Real.sqrt 2 ^ k := by
  have hden_pos : 0 < ‖sqrtTwoComplex ^ k‖ := by
    rw [norm_sqrtTwoComplex_pow]
    exact
      pow_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)) k
  have hval : ‖coord.numerator / sqrtTwoComplex ^ k‖ ≤ 1 := by
    simpa [InClosedUnitDisk, GridCoord.value_eq_numerator_div] using hDisk
  rw [norm_div] at hval
  have hmul := mul_le_mul_of_nonneg_right hval hden_pos.le
  have hden_ne : ‖sqrtTwoComplex ^ k‖ ≠ 0 := ne_of_gt hden_pos
  have hcalc :
      ‖coord.numerator‖ / ‖sqrtTwoComplex ^ k‖ * ‖sqrtTwoComplex ^ k‖ =
        ‖coord.numerator‖ := by
    field_simp [hden_ne]
  rwa [hcalc, one_mul, norm_sqrtTwoComplex_pow] at hmul

private theorem bulletNumerator_norm_le_of_bullet_disk
    (coord : GridCoord) (k : ℕ)
    (hDisk : InClosedUnitDisk (coord.bulletValue k)) :
    ‖coord.bulletNumerator‖ ≤ Real.sqrt 2 ^ k := by
  have hden_pos : 0 < ‖(((-Real.sqrt 2 : ℝ) : ℂ) ^ k)‖ := by
    rw [norm_neg_sqrtTwoComplex_pow]
    exact
      pow_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)) k
  have hval :
      ‖coord.bulletNumerator / (((-Real.sqrt 2 : ℝ) : ℂ) ^ k)‖ ≤ 1 := by
    simpa [InClosedUnitDisk, GridCoord.bulletValue_eq_numerator_div] using hDisk
  rw [norm_div] at hval
  have hmul := mul_le_mul_of_nonneg_right hval hden_pos.le
  have hden_ne : ‖(((-Real.sqrt 2 : ℝ) : ℂ) ^ k)‖ ≠ 0 := ne_of_gt hden_pos
  have hcalc :
      ‖coord.bulletNumerator‖ / ‖(((-Real.sqrt 2 : ℝ) : ℂ) ^ k)‖ *
          ‖(((-Real.sqrt 2 : ℝ) : ℂ) ^ k)‖ =
        ‖coord.bulletNumerator‖ := by
    field_simp [hden_ne]
  rwa [hcalc, one_mul, norm_neg_sqrtTwoComplex_pow] at hmul

private theorem abs_re_numerator_le
    (coord : GridCoord) (k : ℕ)
    (hDisk : InClosedUnitDisk (coord.value k)) :
    |coord.numerator.re| ≤ Real.sqrt 2 ^ k :=
  (Complex.abs_re_le_norm coord.numerator).trans
    (numerator_norm_le_of_value_disk coord k hDisk)

private theorem abs_im_numerator_le
    (coord : GridCoord) (k : ℕ)
    (hDisk : InClosedUnitDisk (coord.value k)) :
    |coord.numerator.im| ≤ Real.sqrt 2 ^ k :=
  (Complex.abs_im_le_norm coord.numerator).trans
    (numerator_norm_le_of_value_disk coord k hDisk)

private theorem abs_re_bulletNumerator_le
    (coord : GridCoord) (k : ℕ)
    (hDisk : InClosedUnitDisk (coord.bulletValue k)) :
    |coord.bulletNumerator.re| ≤ Real.sqrt 2 ^ k :=
  (Complex.abs_re_le_norm coord.bulletNumerator).trans
    (bulletNumerator_norm_le_of_bullet_disk coord k hDisk)

private theorem abs_im_bulletNumerator_le
    (coord : GridCoord) (k : ℕ)
    (hDisk : InClosedUnitDisk (coord.bulletValue k)) :
    |coord.bulletNumerator.im| ≤ Real.sqrt 2 ^ k :=
  (Complex.abs_im_le_norm coord.bulletNumerator).trans
    (bulletNumerator_norm_le_of_bullet_disk coord k hDisk)

private theorem GridCoord.abs_coeffs_le_sqrtTwo_pow
    {θ ε : ℝ} {k : ℕ} {coord : GridCoord}
    (hcoord : coord.Admissible θ ε k) :
    |(coord.a : ℝ)| ≤ Real.sqrt 2 ^ k ∧
      |(coord.b : ℝ)| ≤ Real.sqrt 2 ^ k ∧
        |(coord.c : ℝ)| ≤ Real.sqrt 2 ^ k ∧
          |(coord.d : ℝ)| ≤ Real.sqrt 2 ^ k := by
  have hDisk : InClosedUnitDisk (coord.value k) := hcoord.1.1
  have hBulletDisk : InClosedUnitDisk (coord.bulletValue k) := hcoord.2.1
  have hNr := abs_re_numerator_le coord k hDisk
  have hNi := abs_im_numerator_le coord k hDisk
  have hBr := abs_re_bulletNumerator_le coord k hBulletDisk
  have hBi := abs_im_bulletNumerator_le coord k hBulletDisk
  have hs_nonneg : 0 ≤ Real.sqrt 2 ^ k :=
    pow_nonneg (Real.sqrt_nonneg 2) k
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
    have hs_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hs_sq : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
      simpa [sq] using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have coeff_a :
      |(coord.a : ℝ)| ≤ Real.sqrt 2 ^ k := by
    have hsum :
        |coord.numerator.re + coord.bulletNumerator.re| ≤
          2 * Real.sqrt 2 ^ k := by
      calc
        |coord.numerator.re + coord.bulletNumerator.re|
            ≤ |coord.numerator.re| + |coord.bulletNumerator.re| := by
              simpa [Real.norm_eq_abs] using
                norm_add_le coord.numerator.re coord.bulletNumerator.re
        _ ≤ Real.sqrt 2 ^ k + Real.sqrt 2 ^ k := add_le_add hNr hBr
        _ = 2 * Real.sqrt 2 ^ k := by ring
    have hrepr :
        coord.numerator.re + coord.bulletNumerator.re = 2 * (coord.a : ℝ) := by
      simp [GridCoord.numerator, GridCoord.bulletNumerator, sqrtTwoComplex]
      ring
    rw [hrepr, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hsum
    nlinarith [hs_nonneg]
  have coeff_b :
      |(coord.b : ℝ)| ≤ Real.sqrt 2 ^ k := by
    have hdiff :
        |coord.numerator.re - coord.bulletNumerator.re| ≤
          2 * Real.sqrt 2 ^ k := by
      calc
        |coord.numerator.re - coord.bulletNumerator.re|
            ≤ |coord.numerator.re| + |coord.bulletNumerator.re| := by
              simpa [sub_eq_add_neg, abs_neg] using
                (show ‖coord.numerator.re + -coord.bulletNumerator.re‖ ≤
                    ‖coord.numerator.re‖ + ‖-coord.bulletNumerator.re‖ from
                  norm_add_le coord.numerator.re (-coord.bulletNumerator.re))
        _ ≤ Real.sqrt 2 ^ k + Real.sqrt 2 ^ k := add_le_add hNr hBr
        _ = 2 * Real.sqrt 2 ^ k := by ring
    have hrepr :
        coord.numerator.re - coord.bulletNumerator.re =
          2 * ((coord.b : ℝ) * Real.sqrt 2) := by
      simp [GridCoord.numerator, GridCoord.bulletNumerator, sqrtTwoComplex]
      ring
    rw [hrepr, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (Real.sqrt_nonneg 2)] at hdiff
    have hb_mul : |(coord.b : ℝ)| * Real.sqrt 2 ≤ Real.sqrt 2 ^ k := by
      nlinarith [Real.sqrt_nonneg 2, hs_nonneg]
    have hb_le_mul : |(coord.b : ℝ)| ≤ |(coord.b : ℝ)| * Real.sqrt 2 := by
      exact le_mul_of_one_le_right (abs_nonneg _) hsqrt_ge_one
    exact hb_le_mul.trans hb_mul
  have coeff_c :
      |(coord.c : ℝ)| ≤ Real.sqrt 2 ^ k := by
    have hsum :
        |coord.numerator.im + coord.bulletNumerator.im| ≤
          2 * Real.sqrt 2 ^ k := by
      calc
        |coord.numerator.im + coord.bulletNumerator.im|
            ≤ |coord.numerator.im| + |coord.bulletNumerator.im| := by
              simpa [Real.norm_eq_abs] using
                norm_add_le coord.numerator.im coord.bulletNumerator.im
        _ ≤ Real.sqrt 2 ^ k + Real.sqrt 2 ^ k := add_le_add hNi hBi
        _ = 2 * Real.sqrt 2 ^ k := by ring
    have hrepr :
        coord.numerator.im + coord.bulletNumerator.im = 2 * (coord.c : ℝ) := by
      simp [GridCoord.numerator, GridCoord.bulletNumerator, sqrtTwoComplex]
      ring
    rw [hrepr, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hsum
    nlinarith [hs_nonneg]
  have coeff_d :
      |(coord.d : ℝ)| ≤ Real.sqrt 2 ^ k := by
    have hdiff :
        |coord.numerator.im - coord.bulletNumerator.im| ≤
          2 * Real.sqrt 2 ^ k := by
      calc
        |coord.numerator.im - coord.bulletNumerator.im|
            ≤ |coord.numerator.im| + |coord.bulletNumerator.im| := by
              simpa [sub_eq_add_neg, abs_neg] using
                (show ‖coord.numerator.im + -coord.bulletNumerator.im‖ ≤
                    ‖coord.numerator.im‖ + ‖-coord.bulletNumerator.im‖ from
                  norm_add_le coord.numerator.im (-coord.bulletNumerator.im))
        _ ≤ Real.sqrt 2 ^ k + Real.sqrt 2 ^ k := add_le_add hNi hBi
        _ = 2 * Real.sqrt 2 ^ k := by ring
    have hrepr :
        coord.numerator.im - coord.bulletNumerator.im =
          2 * ((coord.d : ℝ) * Real.sqrt 2) := by
      simp [GridCoord.numerator, GridCoord.bulletNumerator, sqrtTwoComplex]
      ring
    rw [hrepr, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (Real.sqrt_nonneg 2)] at hdiff
    have hd_mul : |(coord.d : ℝ)| * Real.sqrt 2 ≤ Real.sqrt 2 ^ k := by
      nlinarith [Real.sqrt_nonneg 2, hs_nonneg]
    have hd_le_mul : |(coord.d : ℝ)| ≤ |(coord.d : ℝ)| * Real.sqrt 2 := by
      exact le_mul_of_one_le_right (abs_nonneg _) hsqrt_ge_one
    exact hd_le_mul.trans hd_mul
  exact ⟨coeff_a, coeff_b, coeff_c, coeff_d⟩

theorem GridCoord.mem_box_of_admissible
    {θ ε : ℝ} {k : ℕ} {coord : GridCoord}
    (hcoord : coord.Admissible θ ε k) :
    coord ∈ gridCoordsInBox (gridCoordBound k) := by
  rcases GridCoord.abs_coeffs_le_sqrtTwo_pow hcoord with
    ⟨ha, hb, hc, hd⟩
  have hbound : Real.sqrt 2 ^ k ≤ (gridCoordBound k : ℝ) := by
    simpa [gridCoordBound] using sqrtTwo_pow_le_two_pow k
  exact mem_gridCoordsInBox_of_abs_le
    (ha.trans hbound) (hb.trans hbound) (hc.trans hbound) (hd.trans hbound)

/-- Coordinates in a finite box that satisfy the proof-carrying scaled-grid
predicate. -/
noncomputable def certifiedGridCoords (θ ε : ℝ) (k B : ℕ) :
    List { coord : GridCoord // coord.Admissible θ ε k } := by
  classical
  exact (gridCoordsInBox B).filterMap fun coord =>
    if hcoord : coord.Admissible θ ε k then
      some ⟨coord, hcoord⟩
    else
      none

theorem mem_certifiedGridCoords_of_mem_box {θ ε : ℝ} {k B : ℕ}
    {coord : GridCoord}
    (hmem : coord ∈ gridCoordsInBox B)
    (hcoord : coord.Admissible θ ε k) :
    ∃ data ∈ certifiedGridCoords θ ε k B, data.1 = coord := by
  classical
  refine ⟨⟨coord, hcoord⟩, ?_, rfl⟩
  rw [certifiedGridCoords, List.mem_filterMap]
  refine ⟨coord, hmem, ?_⟩
  simp [hcoord]

/-- Concrete finite batch of Ross-Selinger candidates at denominator level
`k`, obtained by scanning the coordinate box `[-B, B]^4`. -/
noncomputable def boundedGridCandidatesAtLevel
    (θ ε : ℝ) (k B : ℕ) : List (RSCandidate θ ε) :=
  (certifiedGridCoords θ ε k B).map fun data =>
    data.1.toCandidate data.2

theorem boundedGridCandidatesAtLevel_level
    (θ ε : ℝ) (k B : ℕ) {candidate : RSCandidate θ ε}
    (hmem : candidate ∈ boundedGridCandidatesAtLevel θ ε k B) :
    candidate.level = k := by
  rcases List.mem_map.mp hmem with ⟨data, _hdata, hcandidate⟩
  rw [← hcandidate]
  exact GridCoord.toCandidate_level data.1 data.2

theorem boundedGridCandidatesAtLevel_sound
    (θ ε : ℝ) (k B : ℕ) {candidate : RSCandidate θ ε}
    (hmem : candidate ∈ boundedGridCandidatesAtLevel θ ε k B) :
    FixedDenominatorScaledGridCandidate θ ε k candidate.u ∧
      IsLeastDenominatorExponent candidate.u k := by
  have hlevel := boundedGridCandidatesAtLevel_level θ ε k B hmem
  constructor
  · simpa [hlevel] using candidate.hFixed
  · simpa [hlevel] using candidate.hLeast

/-- Bounded fixed-level completeness: every admissible coordinate that lies in
the scanned coordinate box appears in the finite candidate batch. -/
theorem exists_mem_boundedGridCandidatesAtLevel_of_admissible_coord
    {θ ε : ℝ} {k B : ℕ} {coord : GridCoord}
    (hmem : coord ∈ gridCoordsInBox B)
    (hcoord : coord.Admissible θ ε k) :
    ∃ candidate ∈ boundedGridCandidatesAtLevel θ ε k B,
      candidate.u = coord.value k := by
  rcases mem_certifiedGridCoords_of_mem_box hmem hcoord with
    ⟨data, hdata, hdata_coord⟩
  let candidate : RSCandidate θ ε := data.1.toCandidate data.2
  refine ⟨candidate, ?_, ?_⟩
  · exact List.mem_map.2 ⟨data, hdata, rfl⟩
  · simp [candidate, hdata_coord]

/-- The canonical finite Ross-Selinger candidate batch at level `k`.

The box `[-2^k, 2^k]^4` is large enough for all fixed-level admissible
coordinates: the two closed-disk constraints bound both the numerator and its
`sqrt 2` conjugate, hence each integer coefficient. -/
noncomputable def gridCandidatesAtLevel
    (θ ε : ℝ) (k : ℕ) : List (RSCandidate θ ε) :=
  boundedGridCandidatesAtLevel θ ε k (gridCoordBound k)

theorem gridCandidatesAtLevel_level
    (θ ε : ℝ) (k : ℕ) {candidate : RSCandidate θ ε}
    (hmem : candidate ∈ gridCandidatesAtLevel θ ε k) :
    candidate.level = k :=
  boundedGridCandidatesAtLevel_level θ ε k (gridCoordBound k) hmem

theorem gridCandidatesAtLevel_sound
    (θ ε : ℝ) (k : ℕ) {candidate : RSCandidate θ ε}
    (hmem : candidate ∈ gridCandidatesAtLevel θ ε k) :
    FixedDenominatorScaledGridCandidate θ ε k candidate.u ∧
      IsLeastDenominatorExponent candidate.u k :=
  boundedGridCandidatesAtLevel_sound θ ε k (gridCoordBound k) hmem

/-- Full fixed-level completeness for the coordinate presentation used by the
Ross-Selinger enumerator: every admissible coordinate at level `k` appears in
the canonical finite batch for that level. -/
theorem exists_mem_gridCandidatesAtLevel_of_admissible_coord
    {θ ε : ℝ} {k : ℕ} {coord : GridCoord}
    (hcoord : coord.Admissible θ ε k) :
    ∃ candidate ∈ gridCandidatesAtLevel θ ε k,
      candidate.u = coord.value k :=
  exists_mem_boundedGridCandidatesAtLevel_of_admissible_coord
    (GridCoord.mem_box_of_admissible hcoord) hcoord

/-- Phase-2 grid existence: there is a dyadic-cyclotomic grid point in the
epsilon region whose bullet conjugate lies in the closed unit disk. -/
theorem scaled_grid_candidate_exists
    (θ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℂ, ScaledGridCandidate θ ε u := by
  simpa [ScaledGridCandidate] using grid_candidate_exists θ hε

end RossSelinger
end TwoControl

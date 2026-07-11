import TwoControl.Prelude

namespace DyadicCyclotomic

open TwoControl

/-!
Dyadic-cyclotomic algebra shared by the Ross-Selinger and KMM parts of the
Lemma 12 proof.

The papers use

* `ℤ[ω]`, where `ω = exp(iπ/4)`;
* `D[ω] = ℤ[1 / sqrt 2, i]`;
* the real subring `D[sqrt 2]`;
* complex conjugation `†`; and
* `sqrt 2`-conjugation `•`, called `bullet` in the papers.

For now we represent membership predicates concretely by integer coordinates.
This keeps the remaining proof obligations first-order and avoids committing
too early to a quotient/ring-of-integers implementation.
-/

/-- The scalar `ω = exp(iπ/4)`. -/
noncomputable def rsOmega : ℂ :=
  Complex.exp (Complex.I * (Real.pi / 4))

/-- Complex coercion of `sqrt 2`, used in denominator coordinates. -/
noncomputable def sqrtTwoComplex : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)

/-- Numerators in `ℤ[ω]`, represented as
`a + b sqrt2 + (c + d sqrt2)i`. -/
def InCyclotomicIntegerCoord (z : ℂ) : Prop :=
  ∃ a b c d : ℤ,
    z =
      ((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
        ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I

/-- Elements of `D[ω] = ℤ[1 / sqrt 2, i]`, written as
`(a + b sqrt2 + (c + d sqrt2)i) / sqrt2^n`. -/
def InDyadicCyclotomic (z : ℂ) : Prop :=
  ∃ n : ℕ, ∃ a b c d : ℤ,
    z =
      (((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
          ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
        (sqrtTwoComplex ^ n)

/-- Elements of the real subring `D[sqrt 2]`. -/
def InDyadicSqrtTwo (x : ℝ) : Prop :=
  ∃ n : ℕ, ∃ a b : ℤ,
    x = ((a : ℝ) + (b : ℝ) * Real.sqrt 2) / (Real.sqrt 2 ^ n)

/-- Matrix entries all lie in `D[ω]`. -/
def MatrixEntriesInDyadicCyclotomic (U : Square 2) : Prop :=
  ∀ i j : Fin 2, InDyadicCyclotomic (U i j)

/-- Having a particular denominator exponent in `D[ω]`. -/
def HasDenominatorExponent (z : ℂ) (k : ℕ) : Prop :=
  ∃ a b c d : ℤ,
    z =
      (((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
          ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
        (sqrtTwoComplex ^ k)

/-- `k` is the least denominator exponent of a complex number. -/
def IsLeastDenominatorExponent (z : ℂ) (k : ℕ) : Prop :=
  HasDenominatorExponent z k ∧
    ∀ l : ℕ, HasDenominatorExponent z l → k ≤ l

/-- The `sqrt 2`-conjugate relation on `D[ω]`.

This is a relation rather than a total function on `ℂ`, since the bullet map is
intrinsically an automorphism of the represented coefficient ring. -/
def IsBulletConj (z zbullet : ℂ) : Prop :=
  ∃ n : ℕ, ∃ a b c d : ℤ,
    z =
      (((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
          ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
        (sqrtTwoComplex ^ n) ∧
    zbullet =
      (((a : ℂ) - (b : ℂ) * sqrtTwoComplex) +
          ((c : ℂ) - (d : ℂ) * sqrtTwoComplex) * Complex.I) /
        (((-Real.sqrt 2 : ℝ) : ℂ) ^ n)

@[simp] theorem sqrtTwoComplex_mul_self :
    sqrtTwoComplex * sqrtTwoComplex = (2 : ℂ) := by
  rw [sqrtTwoComplex]
  norm_num [← Complex.ofReal_mul, Real.sq_sqrt]

@[simp] theorem sqrtTwoComplex_sq :
    sqrtTwoComplex ^ 2 = (2 : ℂ) := by
  simpa [sq] using sqrtTwoComplex_mul_self

theorem sqrtTwoComplex_ne_zero :
    sqrtTwoComplex ≠ 0 := by
  intro h
  have hs : sqrtTwoComplex * sqrtTwoComplex = (0 : ℂ) := by simpa [h]
  norm_num at hs

/-- A coordinate numerator gives a denominator exponent `0`. -/
theorem hasDenominatorExponent_zero_of_coord {z : ℂ}
    (hz : InCyclotomicIntegerCoord z) :
    HasDenominatorExponent z 0 := by
  rcases hz with ⟨a, b, c, d, hz⟩
  refine ⟨a, b, c, d, ?_⟩
  simpa using hz

/-- `0 ∈ ℤ[ω]`. -/
theorem InCyclotomicIntegerCoord.zero :
    InCyclotomicIntegerCoord 0 := by
  refine ⟨0, 0, 0, 0, ?_⟩
  simp [sqrtTwoComplex]

/-- `1 ∈ ℤ[ω]`. -/
theorem InCyclotomicIntegerCoord.one :
    InCyclotomicIntegerCoord 1 := by
  refine ⟨1, 0, 0, 0, ?_⟩
  simp [sqrtTwoComplex]

/-- `ℤ[ω]` is closed under negation. -/
theorem InCyclotomicIntegerCoord.neg {z : ℂ}
    (hz : InCyclotomicIntegerCoord z) :
    InCyclotomicIntegerCoord (-z) := by
  rcases hz with ⟨a, b, c, d, hz⟩
  refine ⟨-a, -b, -c, -d, ?_⟩
  rw [hz]
  simp [sqrtTwoComplex]
  ring

/-- `ℤ[ω]` is closed under complex conjugation. -/
theorem InCyclotomicIntegerCoord.star {z : ℂ}
    (hz : InCyclotomicIntegerCoord z) :
    InCyclotomicIntegerCoord (star z) := by
  rcases hz with ⟨a, b, c, d, hz⟩
  refine ⟨a, b, -c, -d, ?_⟩
  rw [hz]
  simp [sqrtTwoComplex]
  ring

/-- `ℤ[ω]` is closed under addition. -/
theorem InCyclotomicIntegerCoord.add {z w : ℂ}
    (hz : InCyclotomicIntegerCoord z)
    (hw : InCyclotomicIntegerCoord w) :
    InCyclotomicIntegerCoord (z + w) := by
  rcases hz with ⟨a, b, c, d, hz⟩
  rcases hw with ⟨e, f, g, h, hw⟩
  refine ⟨a + e, b + f, c + g, d + h, ?_⟩
  rw [hz, hw]
  simp [sqrtTwoComplex]
  ring

/-- `ℤ[ω]` is closed under multiplication. -/
theorem InCyclotomicIntegerCoord.mul {z w : ℂ}
    (hz : InCyclotomicIntegerCoord z)
    (hw : InCyclotomicIntegerCoord w) :
    InCyclotomicIntegerCoord (z * w) := by
  rcases hz with ⟨a, b, c, d, hz⟩
  rcases hw with ⟨e, f, g, h, hw⟩
  refine ⟨a * e + 2 * b * f - c * g - 2 * d * h,
    a * f + b * e - c * h - d * g,
    a * g + 2 * b * h + c * e + 2 * d * f,
    a * h + b * g + c * f + d * e, ?_⟩
  rw [hz, hw]
  ring_nf
  simp [sqrtTwoComplex_sq]
  ring

/-- Multiplication by `sqrt 2` preserves `ℤ[ω]`. -/
theorem InCyclotomicIntegerCoord.mul_sqrtTwo {z : ℂ}
    (hz : InCyclotomicIntegerCoord z) :
    InCyclotomicIntegerCoord (sqrtTwoComplex * z) := by
  rcases hz with ⟨a, b, c, d, hz⟩
  refine ⟨2 * b, a, 2 * d, c, ?_⟩
  rw [hz]
  ring_nf
  simp [sqrtTwoComplex_sq]
  ring

/-- Multiplication by a power of `sqrt 2` preserves `ℤ[ω]`. -/
theorem InCyclotomicIntegerCoord.mul_sqrtTwo_pow {z : ℂ} (n : ℕ)
    (hz : InCyclotomicIntegerCoord z) :
    InCyclotomicIntegerCoord (sqrtTwoComplex ^ n * z) := by
  induction n with
  | zero =>
      simpa using hz
  | succ n ih =>
      simpa [pow_succ', mul_assoc] using InCyclotomicIntegerCoord.mul_sqrtTwo ih

theorem inDyadicCyclotomic_of_denominatorExponent {z : ℂ} {k : ℕ}
    (h : HasDenominatorExponent z k) :
    InDyadicCyclotomic z := by
  rcases h with ⟨a, b, c, d, hz⟩
  exact ⟨k, a, b, c, d, hz⟩

theorem hasDenominatorExponent_of_inDyadicCyclotomic {z : ℂ}
    (h : InDyadicCyclotomic z) :
    ∃ k : ℕ, HasDenominatorExponent z k := by
  rcases h with ⟨k, a, b, c, d, hz⟩
  exact ⟨k, a, b, c, d, hz⟩

/-- A denominator exponent can always be raised by multiplying the numerator by
the missing power of `sqrt 2`. -/
theorem hasDenominatorExponent_mono
    {z : ℂ} {k l : ℕ}
    (hk : HasDenominatorExponent z k)
    (hkl : k ≤ l) :
    HasDenominatorExponent z l := by
  rcases hk with ⟨a, b, c, d, hz⟩
  let N : ℂ :=
    ((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
      ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I
  have hN : InCyclotomicIntegerCoord N := by
    exact ⟨a, b, c, d, rfl⟩
  have hnum := InCyclotomicIntegerCoord.mul_sqrtTwo_pow (l - k) hN
  rcases hnum with ⟨a', b', c', d', hnum⟩
  refine ⟨a', b', c', d', ?_⟩
  rw [hz]
  change N / sqrtTwoComplex ^ k =
    (((a' : ℂ) + (b' : ℂ) * sqrtTwoComplex) +
      ((c' : ℂ) + (d' : ℂ) * sqrtTwoComplex) * Complex.I) / sqrtTwoComplex ^ l
  rw [← hnum]
  have hs : sqrtTwoComplex ≠ 0 := sqrtTwoComplex_ne_zero
  have hpowk : sqrtTwoComplex ^ k ≠ 0 := pow_ne_zero k hs
  have hpowl : sqrtTwoComplex ^ l ≠ 0 := pow_ne_zero l hs
  have hsub : l - k + k = l := Nat.sub_add_cancel hkl
  rw [← hsub, pow_add]
  field_simp [hpowk, hpowl, pow_ne_zero (l - k) hs]
  have hexp : l - k + k - k = l - k := by omega
  simpa [hexp]

/-- `D[ω]` is closed under complex conjugation. -/
theorem InDyadicCyclotomic.star {z : ℂ}
    (hz : InDyadicCyclotomic z) :
    InDyadicCyclotomic (star z) := by
  rcases hz with ⟨n, a, b, c, d, hz⟩
  refine ⟨n, a, b, -c, -d, ?_⟩
  rw [hz]
  simp [sqrtTwoComplex]
  ring

/-- `D[ω]` is closed under negation. -/
theorem InDyadicCyclotomic.neg {z : ℂ}
    (hz : InDyadicCyclotomic z) :
    InDyadicCyclotomic (-z) := by
  rcases hz with ⟨n, a, b, c, d, hz⟩
  refine ⟨n, -a, -b, -c, -d, ?_⟩
  rw [hz]
  simp [sqrtTwoComplex]
  ring

/-- `0 ∈ D[ω]`. -/
theorem InDyadicCyclotomic.zero :
    InDyadicCyclotomic 0 := by
  refine ⟨0, 0, 0, 0, 0, ?_⟩
  simp [sqrtTwoComplex]

/-- `1 ∈ D[ω]`. -/
theorem InDyadicCyclotomic.one :
    InDyadicCyclotomic 1 :=
  inDyadicCyclotomic_of_denominatorExponent
    (hasDenominatorExponent_zero_of_coord InCyclotomicIntegerCoord.one)

/-- Dividing by `sqrt 2` preserves `D[ω]`. -/
theorem InDyadicCyclotomic.div_sqrtTwo {z : ℂ}
    (hz : InDyadicCyclotomic z) :
    InDyadicCyclotomic (z / sqrtTwoComplex) := by
  rcases hasDenominatorExponent_of_inDyadicCyclotomic hz with ⟨k, a, b, c, d, hz'⟩
  refine ⟨k + 1, a, b, c, d, ?_⟩
  rw [hz']
  rw [pow_succ]
  field_simp [pow_ne_zero k sqrtTwoComplex_ne_zero, sqrtTwoComplex_ne_zero]

/-- `D[ω]` is closed under addition. -/
theorem InDyadicCyclotomic.add {z w : ℂ}
    (hz : InDyadicCyclotomic z)
    (hw : InDyadicCyclotomic w) :
    InDyadicCyclotomic (z + w) := by
  rcases hasDenominatorExponent_of_inDyadicCyclotomic hz with ⟨k, hk⟩
  rcases hasDenominatorExponent_of_inDyadicCyclotomic hw with ⟨l, hl⟩
  let m := max k l
  have hk' : HasDenominatorExponent z m :=
    hasDenominatorExponent_mono hk (Nat.le_max_left k l)
  have hl' : HasDenominatorExponent w m :=
    hasDenominatorExponent_mono hl (Nat.le_max_right k l)
  rcases hk' with ⟨a, b, c, d, hz'⟩
  rcases hl' with ⟨e, f, g, h, hw'⟩
  refine ⟨m, a + e, b + f, c + g, d + h, ?_⟩
  rw [hz', hw']
  field_simp [pow_ne_zero m sqrtTwoComplex_ne_zero]
  simp only [Int.cast_add]
  ring_nf

/-- `D[ω]` is closed under multiplication. -/
theorem InDyadicCyclotomic.mul {z w : ℂ}
    (hz : InDyadicCyclotomic z)
    (hw : InDyadicCyclotomic w) :
    InDyadicCyclotomic (z * w) := by
  rcases hasDenominatorExponent_of_inDyadicCyclotomic hz with ⟨k, a, b, c, d, hz'⟩
  rcases hasDenominatorExponent_of_inDyadicCyclotomic hw with ⟨l, e, f, g, h, hw'⟩
  let N : ℂ :=
    ((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
      ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I
  let M : ℂ :=
    ((e : ℂ) + (f : ℂ) * sqrtTwoComplex) +
      ((g : ℂ) + (h : ℂ) * sqrtTwoComplex) * Complex.I
  have hN : InCyclotomicIntegerCoord N := ⟨a, b, c, d, rfl⟩
  have hM : InCyclotomicIntegerCoord M := ⟨e, f, g, h, rfl⟩
  rcases InCyclotomicIntegerCoord.mul hN hM with ⟨a', b', c', d', hNM⟩
  refine ⟨k + l, a', b', c', d', ?_⟩
  rw [hz', hw']
  change (N / sqrtTwoComplex ^ k) * (M / sqrtTwoComplex ^ l) =
    (((a' : ℂ) + (b' : ℂ) * sqrtTwoComplex) +
      ((c' : ℂ) + (d' : ℂ) * sqrtTwoComplex) * Complex.I) / sqrtTwoComplex ^ (k + l)
  rw [← hNM]
  have hs : sqrtTwoComplex ≠ 0 := sqrtTwoComplex_ne_zero
  field_simp [pow_ne_zero k hs, pow_ne_zero l hs, pow_ne_zero (k + l) hs, pow_add]
  ring

private lemma sqrtTwoComplex_pow_eq_ofReal (n : ℕ) :
    sqrtTwoComplex ^ n = ((Real.sqrt 2 ^ n : ℝ) : ℂ) := by
  rw [sqrtTwoComplex, ← Complex.ofReal_pow]

private lemma star_mul_self_re_eq_normSq (w : ℂ) :
    (star w * w).re = Complex.normSq w := by
  have h : ((Complex.normSq w : ℝ) : ℂ) = star w * w := by
    simpa using (Complex.normSq_eq_conj_mul_self (z := w))
  have hr := congrArg Complex.re h
  simpa using hr.symm

/-- If `z ∈ D[ω]`, then `star z * z` lies in the real subring `D[sqrt 2]`.

Concretely: if `z = (a + b√2 + (c + d√2)i) / √2^n` then
`(star z · z).re = ((a² + 2b² + c² + 2d²) + 2(ab + cd)·√2) / √2^(2n)`,
which is in `InDyadicSqrtTwo` by inspection. -/
theorem star_mul_self_in_dyadicSqrtTwo {z : ℂ}
    (hz : InDyadicCyclotomic z) :
    InDyadicSqrtTwo ((star z * z).re) := by
  rcases hz with ⟨n, a, b, c, d, hz_eq⟩
  refine ⟨2 * n, a ^ 2 + 2 * b ^ 2 + c ^ 2 + 2 * d ^ 2,
          2 * (a * b + c * d), ?_⟩
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num)
  have hpow_pos : (0 : ℝ) < Real.sqrt 2 ^ n := pow_pos hsqrt2_pos n
  have hpow_ne : (Real.sqrt 2 ^ n : ℝ) ≠ 0 := ne_of_gt hpow_pos
  have hsq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  -- Replace (star z * z).re with normSq z; substitute the explicit form.
  rw [star_mul_self_re_eq_normSq, hz_eq, sqrtTwoComplex_pow_eq_ofReal]
  rw [Complex.normSq_div, Complex.normSq_ofReal]
  rw [Complex.normSq_apply]
  -- Compute the real and imaginary parts of the numerator explicitly.
  have hre : (((a : ℂ) + (b : ℂ) * sqrtTwoComplex +
              ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I)).re =
        (a : ℝ) + (b : ℝ) * Real.sqrt 2 := by
    simp [sqrtTwoComplex]
  have him : (((a : ℂ) + (b : ℂ) * sqrtTwoComplex +
              ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I)).im =
        (c : ℝ) + (d : ℝ) * Real.sqrt 2 := by
    simp [sqrtTwoComplex]
  rw [hre, him]
  -- Rewrite √2 ^ (2n) as (√2 ^ n)^2 so both denominators match.
  rw [show (2 * n : ℕ) = n + n from by omega, pow_add]
  rw [show Real.sqrt 2 ^ n * Real.sqrt 2 ^ n = (Real.sqrt 2 ^ n) ^ 2 from by ring]
  -- Clear denominator and reduce to a polynomial identity in √2.
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination
    ((b : ℝ) ^ 2 + (d : ℝ) ^ 2) * (Real.sqrt 2 ^ n) ^ 2 * hsq

/-- `D[√2]` is closed under `1 - ·`.  We split on parity of the denominator
exponent: even `n = 2k` makes `√2^n = 2^k` an integer; odd `n = 2k+1` makes
`√2^n = 2^k · √2`, requiring the witness to absorb the `2^k` into the `B`
coefficient. -/
theorem InDyadicSqrtTwo.one_sub {x : ℝ} (hx : InDyadicSqrtTwo x) :
    InDyadicSqrtTwo (1 - x) := by
  rcases hx with ⟨n, A, B, hx_eq⟩
  have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpow_ne : (Real.sqrt 2 ^ n : ℝ) ≠ 0 := ne_of_gt (pow_pos h2pos n)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rcases Nat.even_or_odd n with hEven | hOdd
  · rcases hEven with ⟨k, hk⟩
    -- n = k + k = 2k; √2 ^ n = 2 ^ k.
    refine ⟨n, (2 : ℤ) ^ k - A, -B, ?_⟩
    rw [hx_eq]
    have hk' : n = 2 * k := by omega
    have hpow_eq : Real.sqrt 2 ^ n = (2 : ℝ) ^ k := by
      rw [hk', pow_mul, hsq]
    push_cast
    rw [hpow_eq]
    field_simp
    ring
  · rcases hOdd with ⟨k, hk⟩
    -- n = 2k + 1; √2 ^ n = 2 ^ k · √2.
    refine ⟨n, -A, (2 : ℤ) ^ k - B, ?_⟩
    rw [hx_eq]
    have hpow_eq : Real.sqrt 2 ^ n = (2 : ℝ) ^ k * Real.sqrt 2 := by
      rw [hk, pow_add, pow_one, pow_mul, hsq]
    push_cast
    rw [hpow_eq]
    have h2k_ne : ((2 : ℝ) ^ k) ≠ 0 := by positivity
    have hsqrt2_ne : (Real.sqrt 2 : ℝ) ≠ 0 := ne_of_gt h2pos
    field_simp
    ring

end DyadicCyclotomic

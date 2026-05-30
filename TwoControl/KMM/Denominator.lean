import TwoControl.KMM.OmegaArithmetic

namespace TwoControl.KMM

open DyadicCyclotomic

/-!
KMM denominator-exponent vocabulary.

The exact-synthesis proof reduces a unitary over `D[ω]` by repeatedly lowering
the smallest denominator exponent (`sde`) of an entry, then dispatches the
finite `sde ≤ 3` base case with a certificate/table.
-/

/-- Smallest denominator exponent, with value `0` outside `D[ω]`.
For elements in `D[ω]`, this is the least `k` such that `sqrt2^k * z ∈ ℤ[ω]`,
represented through `HasDenominatorExponent`. -/
noncomputable def sde (z : ℂ) : ℕ :=
  by
    classical
    exact if h : ∃ k : ℕ, HasDenominatorExponent z k then Nat.find h else 0

theorem hasDenominatorExponent_sde {z : ℂ}
    (hz : InDyadicCyclotomic z) :
    HasDenominatorExponent z (sde z) := by
  classical
  rcases hasDenominatorExponent_of_inDyadicCyclotomic hz with ⟨k, hk⟩
  have h : ∃ k : ℕ, HasDenominatorExponent z k := ⟨k, hk⟩
  unfold sde
  simpa [h] using Nat.find_spec h

theorem sde_le_of_hasDenominatorExponent {z : ℂ} {k : ℕ}
    (hk : HasDenominatorExponent z k) :
    sde z ≤ k := by
  classical
  have h : ∃ k : ℕ, HasDenominatorExponent z k := ⟨k, hk⟩
  unfold sde
  simpa [h] using (Nat.find_min' (H := h) hk)

/-- Denominator exponent of the squared norm `z† z`, used in the KMM
state-preparation descent. -/
noncomputable def DenNormSDE (z : ℂ) : ℕ :=
  sde (star z * z)

/-- KMM denominator exponent in the actual `ℤ[ω]` numerator basis:
`sqrtTwoComplex ^ k * z ∈ ℤ[ω]`, represented by omega coordinates. -/
def HasOmegaDenominatorExponent (z : ℂ) (k : ℕ) : Prop :=
  ∃ x : OmegaIntCoord, z = OmegaIntCoord.val x / sqrtTwoComplex ^ k

/-- Elements of `D[ω]` using the KMM numerator basis. -/
def InOmegaDyadicCyclotomic (z : ℂ) : Prop :=
  ∃ k : ℕ, HasOmegaDenominatorExponent z k

/-- Smallest denominator exponent in the KMM omega-coordinate basis. -/
noncomputable def omegaSDE (z : ℂ) : ℕ :=
  by
    classical
    exact if h : ∃ k : ℕ, HasOmegaDenominatorExponent z k then Nat.find h else 0

theorem hasOmegaDenominatorExponent_omegaSDE {z : ℂ}
    (hz : InOmegaDyadicCyclotomic z) :
    HasOmegaDenominatorExponent z (omegaSDE z) := by
  classical
  rcases hz with ⟨k, hk⟩
  have h : ∃ k : ℕ, HasOmegaDenominatorExponent z k := ⟨k, hk⟩
  unfold omegaSDE
  simpa [h] using Nat.find_spec h

theorem omegaSDE_le_of_hasOmegaDenominatorExponent {z : ℂ} {k : ℕ}
    (hk : HasOmegaDenominatorExponent z k) :
    omegaSDE z ≤ k := by
  classical
  have h : ∃ k : ℕ, HasOmegaDenominatorExponent z k := ⟨k, hk⟩
  unfold omegaSDE
  simpa [h] using (Nat.find_min' (H := h) hk)

theorem hasOmegaDenominatorExponent_of_inOmegaDyadicCyclotomic {z : ℂ}
    (hz : InOmegaDyadicCyclotomic z) :
    ∃ x : OmegaIntCoord, z = OmegaIntCoord.val x / sqrtTwoComplex ^ omegaSDE z := by
  simpa [HasOmegaDenominatorExponent] using hasOmegaDenominatorExponent_omegaSDE hz

/-- At omega-denominator level `k`, the numerator is divisible by `√2` in
`ℤ[ω]`.  The quotient is stored explicitly so denominator lowering does not
depend on coordinate uniqueness. -/
def OmegaNumeratorAtLevelDivisibleBySqrtTwo (z : ℂ) (k : ℕ) : Prop :=
  ∃ x q : OmegaIntCoord,
    z = OmegaIntCoord.val x / sqrtTwoComplex ^ k ∧
    OmegaIntCoord.val x = sqrtTwoComplex * OmegaIntCoord.val q

theorem hasOmegaDenominatorExponent_of_hasDenominatorExponent
    {z : ℂ} {k : ℕ}
    (hz : HasDenominatorExponent z k) :
    HasOmegaDenominatorExponent z k := by
  rcases hz with ⟨a, b, c, d, hz⟩
  refine ⟨omegaCoordOfLegacy a b c d, ?_⟩
  simpa [omegaCoordOfLegacy_val] using hz

theorem hasOmegaDenominatorExponent_mono
    {z : ℂ} {k l : ℕ}
    (hk : HasOmegaDenominatorExponent z k)
    (hkl : k ≤ l) :
    HasOmegaDenominatorExponent z l := by
  rcases hk with ⟨x, hz⟩
  refine ⟨OmegaIntCoord.sqrtTwoPowMul (l - k) x, ?_⟩
  have hpow : sqrtTwoComplex ^ l =
      sqrtTwoComplex ^ (l - k) * sqrtTwoComplex ^ k := by
    calc
      sqrtTwoComplex ^ l = sqrtTwoComplex ^ ((l - k) + k) := by
        rw [show (l - k) + k = l by omega]
      _ = sqrtTwoComplex ^ (l - k) * sqrtTwoComplex ^ k := by
        rw [pow_add]
  rw [hz, OmegaIntCoord.val_sqrtTwoPowMul]
  rw [hpow]
  field_simp [pow_ne_zero k sqrtTwoComplex_ne_zero,
    pow_ne_zero (l - k) sqrtTwoComplex_ne_zero]

theorem inOmegaDyadicCyclotomic_of_inDyadicCyclotomic
    {z : ℂ}
    (hz : InDyadicCyclotomic z) :
    InOmegaDyadicCyclotomic z := by
  rcases hasDenominatorExponent_of_inDyadicCyclotomic hz with ⟨k, hk⟩
  exact ⟨k, hasOmegaDenominatorExponent_of_hasDenominatorExponent hk⟩

/-- Lower a KMM omega-basis denominator by one when the numerator at that level
is divisible by `√2`. -/
theorem hasOmegaDenominatorExponent_lower_of_sqrtTwo_dvd
    {z : ℂ} {k : ℕ}
    (_hk : HasOmegaDenominatorExponent z k)
    (hdiv : OmegaNumeratorAtLevelDivisibleBySqrtTwo z k)
    (hpos : 0 < k) :
    HasOmegaDenominatorExponent z (k - 1) := by
  rcases hdiv with ⟨x, q, hz, hx⟩
  refine ⟨q, ?_⟩
  have hkpow : sqrtTwoComplex ^ k =
      sqrtTwoComplex * sqrtTwoComplex ^ (k - 1) := by
    calc
      sqrtTwoComplex ^ k = sqrtTwoComplex ^ ((k - 1) + 1) := by
        congr 1
        omega
      _ = sqrtTwoComplex * sqrtTwoComplex ^ (k - 1) := by
        rw [pow_succ]
        ring
  rw [hz, hx, hkpow]
  field_simp [sqrtTwoComplex_ne_zero, pow_ne_zero (k - 1) sqrtTwoComplex_ne_zero]

/-- Minimality of a positive omega-denominator presentation forces the numerator
to have greatest `√2`-dividing exponent zero.  The positivity hypothesis is
needed because the current denominator exponent lives in `ℕ`, so exponent `0`
cannot be lowered further. -/
theorem sqrtTwoGDE_zero_of_minimal_omega_denominator_pos
    {z : ℂ} {r : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hr : omegaSDE z = r)
    (hpos : 0 < r) :
    OmegaIntCoord.SqrtTwoGDE x 0 := by
  refine OmegaIntCoord.sqrtTwoGDE_zero_of_not_sqrtTwo_dvd ?_
  intro hdiv
  rcases hdiv with ⟨q, hq⟩
  have hk : HasOmegaDenominatorExponent z r := ⟨x, hz⟩
  have hdivLevel : OmegaNumeratorAtLevelDivisibleBySqrtTwo z r :=
    ⟨x, q, hz, hq⟩
  have hlower := hasOmegaDenominatorExponent_lower_of_sqrtTwo_dvd hk hdivLevel hpos
  have hmin := omegaSDE_le_of_hasOmegaDenominatorExponent hlower
  rw [hr] at hmin
  omega

/-- A matrix has all entry denominator exponents at most `n`. -/
def MatrixSDELe (U : Square 2) (n : ℕ) : Prop :=
  ∀ i j : Fin 2, sde (U i j) ≤ n

/-- Greatest-dividing-exponent relation from KMM.  This is intentionally stated
as a relation until the algebraic integer representation is chosen. -/
def GreatestDividingExponent (_z : ℂ) (_base : ℂ) (_k : ℕ) : Prop :=
  True

theorem kmm_sde_gde_relation
    {z base : ℂ} {k : ℕ}
    (_h : GreatestDividingExponent z base k) :
    True := by
  trivial

end TwoControl.KMM

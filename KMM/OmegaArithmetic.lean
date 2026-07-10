import DyadicCyclotomic.Basic
import Mathlib.Tactic.IntervalCases

namespace KMM

open TwoControl
open DyadicCyclotomic

/-!
KMM arithmetic in the `ℤ[ω]` basis.

The exact-synthesis descent proof in Kliuchnikov-Maslov-Mosca is stated in
terms of integer coordinates

`x = x₀ + x₁ω + x₂ω² + x₃ω³`.

This file provides the coordinate vocabulary and the finite mod-8 check used in
the proof of the denominator-descent lemma.  It intentionally contains only
computable residue arithmetic plus the shared algebraic definition of `ω`.
-/

/-- Algebraic version of `ω = exp(iπ/4)`, avoiding transcendental trig in KMM
coordinate calculations. -/
noncomputable def rsOmegaAlg : ℂ :=
  ((1 : ℂ) + Complex.I) / sqrtTwoComplex

theorem rsOmegaAlg_in_dyadic :
    InDyadicCyclotomic rsOmegaAlg := by
  refine ⟨1, 1, 0, 1, 0, ?_⟩
  simp [rsOmegaAlg, sqrtTwoComplex]

theorem rsOmegaAlg_pow_in_dyadic (k : ℕ) :
    InDyadicCyclotomic (rsOmegaAlg ^ k) := by
  induction k with
  | zero =>
      simpa using InDyadicCyclotomic.one
  | succ k ih =>
      simpa [pow_succ] using InDyadicCyclotomic.mul ih rsOmegaAlg_in_dyadic

/-- Integer coordinates for `x₀ + x₁ω + x₂ω² + x₃ω³`. -/
structure OmegaIntCoord where
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
deriving DecidableEq, Repr

namespace OmegaIntCoord

noncomputable def val (x : OmegaIntCoord) : ℂ :=
  (x.x0 : ℂ) + (x.x1 : ℂ) * rsOmegaAlg +
    (x.x2 : ℂ) * rsOmegaAlg ^ 2 + (x.x3 : ℂ) * rsOmegaAlg ^ 3

def add (x y : OmegaIntCoord) : OmegaIntCoord where
  x0 := x.x0 + y.x0
  x1 := x.x1 + y.x1
  x2 := x.x2 + y.x2
  x3 := x.x3 + y.x3

def neg (x : OmegaIntCoord) : OmegaIntCoord where
  x0 := -x.x0
  x1 := -x.x1
  x2 := -x.x2
  x3 := -x.x3

/-- Multiplication by `ω`, using `ω⁴ = -1`. -/
def omegaMul (x : OmegaIntCoord) : OmegaIntCoord where
  x0 := -x.x3
  x1 := x.x0
  x2 := x.x1
  x3 := x.x2

def omegaPowMul : Nat → OmegaIntCoord → OmegaIntCoord
  | 0, x => x
  | n + 1, x => omegaMul (omegaPowMul n x)

def sqrtTwoMul (x : OmegaIntCoord) : OmegaIntCoord :=
  add (omegaMul x) (neg (omegaPowMul 3 x))

def sqrtTwoPowMul : Nat → OmegaIntCoord → OmegaIntCoord
  | 0, x => x
  | n + 1, x => sqrtTwoMul (sqrtTwoPowMul n x)

/-- KMM quadratic form `P(x)`, where `|x|² = P(x) + √2 Q(x)`. -/
def P (x : OmegaIntCoord) : ℤ :=
  x.x0 ^ 2 + x.x1 ^ 2 + x.x2 ^ 2 + x.x3 ^ 2

/-- KMM quadratic form `Q(x)`, where `|x|² = P(x) + √2 Q(x)`. -/
def Q (x : OmegaIntCoord) : ℤ :=
  x.x0 * (x.x1 - x.x3) + x.x2 * (x.x1 + x.x3)

end OmegaIntCoord

theorem rsOmegaAlg_sq :
    rsOmegaAlg ^ 2 = Complex.I := by
  have hs : sqrtTwoComplex ≠ 0 := sqrtTwoComplex_ne_zero
  simp [rsOmegaAlg]
  field_simp [hs]
  ring_nf
  simp [sqrtTwoComplex_sq, Complex.I_sq]

theorem rsOmegaAlg_sub_cube :
    rsOmegaAlg - rsOmegaAlg ^ 3 = sqrtTwoComplex := by
  have hs : sqrtTwoComplex ≠ 0 := sqrtTwoComplex_ne_zero
  rw [show rsOmegaAlg ^ 3 = rsOmegaAlg ^ 2 * rsOmegaAlg by ring]
  rw [rsOmegaAlg_sq]
  simp [rsOmegaAlg]
  field_simp [hs]
  ring_nf
  simp [sqrtTwoComplex_sq, Complex.I_sq]
  norm_num

theorem rsOmegaAlg_add_cube :
    rsOmegaAlg + rsOmegaAlg ^ 3 = sqrtTwoComplex * Complex.I := by
  have hs : sqrtTwoComplex ≠ 0 := sqrtTwoComplex_ne_zero
  rw [show rsOmegaAlg ^ 3 = rsOmegaAlg ^ 2 * rsOmegaAlg by ring]
  rw [rsOmegaAlg_sq]
  simp [rsOmegaAlg]
  field_simp [hs]
  ring_nf
  simp [sqrtTwoComplex_sq, Complex.I_sq]

theorem rsOmegaAlg_cube :
    rsOmegaAlg ^ 3 = (-1 + Complex.I) / sqrtTwoComplex := by
  have hs : sqrtTwoComplex ≠ 0 := sqrtTwoComplex_ne_zero
  rw [show rsOmegaAlg ^ 3 = rsOmegaAlg ^ 2 * rsOmegaAlg by ring]
  rw [rsOmegaAlg_sq]
  simp [rsOmegaAlg]
  field_simp [hs]
  ring_nf
  simp [sqrtTwoComplex_sq, Complex.I_sq]
  ring

theorem rsOmegaAlg_four :
    rsOmegaAlg ^ 4 = -1 := by
  rw [show rsOmegaAlg ^ 4 = (rsOmegaAlg ^ 2) ^ 2 by ring]
  rw [rsOmegaAlg_sq]
  simp [Complex.I_sq]

theorem rsOmegaAlg_five :
    rsOmegaAlg ^ 5 = -rsOmegaAlg := by
  calc
    rsOmegaAlg ^ 5 = rsOmegaAlg ^ 4 * rsOmegaAlg := by ring
    _ = -rsOmegaAlg := by rw [rsOmegaAlg_four]; ring

theorem rsOmegaAlg_six :
    rsOmegaAlg ^ 6 = -rsOmegaAlg ^ 2 := by
  calc
    rsOmegaAlg ^ 6 = rsOmegaAlg ^ 4 * rsOmegaAlg ^ 2 := by ring
    _ = -rsOmegaAlg ^ 2 := by rw [rsOmegaAlg_four]; ring

theorem rsOmegaAlg_seven :
    rsOmegaAlg ^ 7 = -rsOmegaAlg ^ 3 := by
  calc
    rsOmegaAlg ^ 7 = rsOmegaAlg ^ 4 * rsOmegaAlg ^ 3 := by ring
    _ = -rsOmegaAlg ^ 3 := by rw [rsOmegaAlg_four]; ring

theorem rsOmegaAlg_eight :
    rsOmegaAlg ^ 8 = 1 := by
  calc
    rsOmegaAlg ^ 8 = (rsOmegaAlg ^ 4) ^ 2 := by ring
    _ = 1 := by rw [rsOmegaAlg_four]; norm_num

theorem rsOmegaAlg_nine :
    rsOmegaAlg ^ 9 = rsOmegaAlg := by
  calc
    rsOmegaAlg ^ 9 = rsOmegaAlg ^ 8 * rsOmegaAlg := by ring
    _ = rsOmegaAlg := by rw [rsOmegaAlg_eight]; ring

theorem rsOmegaAlg_ten :
    rsOmegaAlg ^ 10 = rsOmegaAlg ^ 2 := by
  calc
    rsOmegaAlg ^ 10 = rsOmegaAlg ^ 8 * rsOmegaAlg ^ 2 := by ring
    _ = rsOmegaAlg ^ 2 := by rw [rsOmegaAlg_eight]; ring

theorem rsOmegaAlg_eleven :
    rsOmegaAlg ^ 11 = rsOmegaAlg ^ 3 := by
  calc
    rsOmegaAlg ^ 11 = rsOmegaAlg ^ 8 * rsOmegaAlg ^ 3 := by ring
    _ = rsOmegaAlg ^ 3 := by rw [rsOmegaAlg_eight]; ring

theorem rsOmegaAlg_twelve :
    rsOmegaAlg ^ 12 = -1 := by
  calc
    rsOmegaAlg ^ 12 = rsOmegaAlg ^ 8 * rsOmegaAlg ^ 4 := by ring
    _ = -1 := by rw [rsOmegaAlg_eight, rsOmegaAlg_four]; ring

theorem star_rsOmegaAlg :
    star rsOmegaAlg = -rsOmegaAlg ^ 3 := by
  have hs : star sqrtTwoComplex = sqrtTwoComplex := by simp [sqrtTwoComplex]
  rw [rsOmegaAlg_cube]
  simp [rsOmegaAlg, hs]
  field_simp [sqrtTwoComplex_ne_zero]
  ring_nf

theorem rsOmegaAlg_star_mul_self :
    star rsOmegaAlg * rsOmegaAlg = 1 := by
  rw [star_rsOmegaAlg]
  calc
    (-rsOmegaAlg ^ 3) * rsOmegaAlg = -(rsOmegaAlg ^ 4) := by ring
    _ = 1 := by rw [rsOmegaAlg_four]; norm_num

namespace OmegaIntCoord

theorem norm_val (x : OmegaIntCoord) :
    star (val x) * val x = (P x : ℂ) + (Q x : ℂ) * sqrtTwoComplex := by
  cases x
  rw [← rsOmegaAlg_sub_cube]
  simp [val, P, Q, star_add, star_mul, star_rsOmegaAlg]
  ring_nf
  simp [rsOmegaAlg_four, rsOmegaAlg_five, rsOmegaAlg_six, rsOmegaAlg_seven,
    rsOmegaAlg_eight, rsOmegaAlg_nine, rsOmegaAlg_ten, rsOmegaAlg_eleven,
    rsOmegaAlg_twelve]
  ring

theorem val_add (x y : OmegaIntCoord) :
    val (add x y) = val x + val y := by
  cases x
  cases y
  simp [val, add]
  ring

theorem val_neg (x : OmegaIntCoord) :
    val (neg x) = -val x := by
  cases x
  simp [val, neg]
  ring

theorem val_omegaMul (x : OmegaIntCoord) :
    val (omegaMul x) = rsOmegaAlg * val x := by
  cases x
  simp [val, omegaMul]
  ring_nf
  simp [rsOmegaAlg_four]

theorem val_omegaPowMul (n : Nat) (x : OmegaIntCoord) :
    val (omegaPowMul n x) = rsOmegaAlg ^ n * val x := by
  induction n with
  | zero =>
      simp [omegaPowMul]
  | succ n ih =>
      simp [omegaPowMul, val_omegaMul, ih, pow_succ]
      ring

theorem val_sqrtTwoMul (x : OmegaIntCoord) :
    val (sqrtTwoMul x) = sqrtTwoComplex * val x := by
  rw [sqrtTwoMul, val_add, val_omegaMul, val_neg, val_omegaPowMul]
  rw [show rsOmegaAlg * val x + -(rsOmegaAlg ^ 3 * val x) =
      (rsOmegaAlg - rsOmegaAlg ^ 3) * val x by ring]
  rw [rsOmegaAlg_sub_cube]

theorem sqrtTwoMul_mk (a b c d : ℤ) :
    sqrtTwoMul ⟨a, b, c, d⟩ =
      ⟨b - d, a + c, b + d, c - a⟩ := by
  simp [sqrtTwoMul, add, neg, omegaMul, omegaPowMul]
  constructor <;> ring

theorem exists_sqrtTwoMul_of_pair_even
    (x : OmegaIntCoord)
    (h02 : Even (x.x0 + x.x2))
    (h13 : Even (x.x1 + x.x3)) :
    ∃ q : OmegaIntCoord, sqrtTwoMul q = x := by
  rcases h02 with ⟨A, hA⟩
  rcases h13 with ⟨B, hB⟩
  refine ⟨⟨x.x1 - B, A, B, x.x2 - A⟩, ?_⟩
  cases x
  simp only at hA hB ⊢
  simp [sqrtTwoMul_mk]
  omega

theorem val_dvd_sqrtTwo_of_pair_even
    (x : OmegaIntCoord)
    (h02 : Even (x.x0 + x.x2))
    (h13 : Even (x.x1 + x.x3)) :
    ∃ q : OmegaIntCoord, val x = sqrtTwoComplex * val q := by
  rcases exists_sqrtTwoMul_of_pair_even x h02 h13 with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [← val_sqrtTwoMul, hq]

private theorem pair_even_of_norm_even
    (x : OmegaIntCoord)
    (hP : Even (P x))
    (hQ : Even (Q x)) :
    Even (x.x0 + x.x2) ∧ Even (x.x1 + x.x3) := by
  cases x with
  | mk x0 x1 x2 x3 =>
      by_cases hx0 : Even x0 <;>
      by_cases hx1 : Even x1 <;>
      by_cases hx2 : Even x2 <;>
      by_cases hx3 : Even x3 <;>
      simp [P, Q, hx0, hx1, hx2, hx3, parity_simps] at hP hQ ⊢ <;>
      tauto

theorem val_dvd_sqrtTwo_of_norm_pair_even
    (x : OmegaIntCoord)
    (hP : Even (P x))
    (hQ : Even (Q x)) :
    ∃ q : OmegaIntCoord, val x = sqrtTwoComplex * val q := by
  rcases pair_even_of_norm_even x hP hQ with ⟨h02, h13⟩
  exact val_dvd_sqrtTwo_of_pair_even x h02 h13

theorem val_sqrtTwoPowMul (n : Nat) (x : OmegaIntCoord) :
    val (sqrtTwoPowMul n x) = sqrtTwoComplex ^ n * val x := by
  induction n with
  | zero =>
      simp [sqrtTwoPowMul]
  | succ n ih =>
      simp [sqrtTwoPowMul, val_sqrtTwoMul, ih, pow_succ]
      ring

/-- Divisibility by `(√2)^n` inside `ℤ[ω]`, represented on omega-basis
coordinates by an explicit quotient. -/
def SqrtTwoPowDivides (x : OmegaIntCoord) (n : ℕ) : Prop :=
  ∃ q : OmegaIntCoord, val x = sqrtTwoComplex ^ n * val q

/-- Greatest dividing exponent by `√2` in the omega-basis coordinate ring,
stated as a relation. -/
def SqrtTwoGDE (x : OmegaIntCoord) (g : ℕ) : Prop :=
  SqrtTwoPowDivides x g ∧ ¬ SqrtTwoPowDivides x (g + 1)

theorem sqrtTwoPowDivides_zero (x : OmegaIntCoord) :
    SqrtTwoPowDivides x 0 := by
  exact ⟨x, by simp [SqrtTwoPowDivides]⟩

theorem sqrtTwoPowDivides_one_iff (x : OmegaIntCoord) :
    SqrtTwoPowDivides x 1 ↔
      ∃ q : OmegaIntCoord, val x = sqrtTwoComplex * val q := by
  simp [SqrtTwoPowDivides]

theorem sqrtTwoGDE_zero_of_not_sqrtTwo_dvd
    {x : OmegaIntCoord}
    (hnot : ¬ ∃ q : OmegaIntCoord, val x = sqrtTwoComplex * val q) :
    SqrtTwoGDE x 0 := by
  refine ⟨sqrtTwoPowDivides_zero x, ?_⟩
  simpa [sqrtTwoPowDivides_one_iff] using hnot

theorem sqrtTwoGDE_zero_not_sqrtTwo_dvd
    {x : OmegaIntCoord}
    (hg : SqrtTwoGDE x 0) :
    ¬ ∃ q : OmegaIntCoord, val x = sqrtTwoComplex * val q := by
  simpa [sqrtTwoPowDivides_one_iff] using hg.2

end OmegaIntCoord

/-- Convert the legacy `a + b√2 + (c+d√2)i` numerator coordinates to KMM's
omega basis. -/
def omegaCoordOfLegacy (a b c d : ℤ) : OmegaIntCoord where
  x0 := a
  x1 := b + d
  x2 := c
  x3 := d - b

theorem omegaCoordOfLegacy_val (a b c d : ℤ) :
    OmegaIntCoord.val (omegaCoordOfLegacy a b c d) =
      (((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
        ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) := by
  simp [OmegaIntCoord.val, omegaCoordOfLegacy]
  rw [rsOmegaAlg_sq]
  have hsqrt : ((b : ℂ) * sqrtTwoComplex) =
      (b : ℂ) * (rsOmegaAlg - rsOmegaAlg ^ 3) := by
    rw [rsOmegaAlg_sub_cube]
  have hsqrtI : ((d : ℂ) * sqrtTwoComplex * Complex.I) =
      (d : ℂ) * (rsOmegaAlg + rsOmegaAlg ^ 3) := by
    rw [rsOmegaAlg_add_cube]
    ring
  rw [show ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I =
      (c : ℂ) * Complex.I + (d : ℂ) * sqrtTwoComplex * Complex.I by ring]
  rw [hsqrt, hsqrtI]
  ring

/-- Residue coordinates in `(ℤ/8ℤ)^4`, used by KMM's finite verification. -/
structure OmegaResidue where
  x0 : ZMod 8
  x1 : ZMod 8
  x2 : ZMod 8
  x3 : ZMod 8
deriving DecidableEq, Repr

namespace OmegaResidue

def ofIntCoord (x : OmegaIntCoord) : OmegaResidue where
  x0 := (x.x0 : ZMod 8)
  x1 := (x.x1 : ZMod 8)
  x2 := (x.x2 : ZMod 8)
  x3 := (x.x3 : ZMod 8)

def add (x y : OmegaResidue) : OmegaResidue where
  x0 := x.x0 + y.x0
  x1 := x.x1 + y.x1
  x2 := x.x2 + y.x2
  x3 := x.x3 + y.x3

/-- Multiplication by `ω`, using `ω⁴ = -1`. -/
def omegaMul (x : OmegaResidue) : OmegaResidue where
  x0 := -x.x3
  x1 := x.x0
  x2 := x.x1
  x3 := x.x2

def omegaPowMul : Nat → OmegaResidue → OmegaResidue
  | 0, x => x
  | n + 1, x => omegaMul (omegaPowMul n x)

def P (x : OmegaResidue) : ZMod 8 :=
  x.x0 ^ 2 + x.x1 ^ 2 + x.x2 ^ 2 + x.x3 ^ 2

def Q (x : OmegaResidue) : ZMod 8 :=
  x.x0 * (x.x1 - x.x3) + x.x2 * (x.x1 + x.x3)

def normPair (x : OmegaResidue) : ZMod 8 × ZMod 8 :=
  (P x, Q x)

private def residueValues : List (ZMod 8) :=
  (List.finRange 8).map fun i : Fin 8 => ((i : ℕ) : ZMod 8)

def all : List OmegaResidue :=
  residueValues.flatMap fun a =>
    residueValues.flatMap fun b =>
      residueValues.flatMap fun c =>
        residueValues.map fun d => ⟨a, b, c, d⟩

private def div2 (a : ZMod 8) : Bool :=
  decide (a.val % 2 = 0)

private def div4 (a : ZMod 8) : Bool :=
  decide (a.val % 4 = 0)

/-- Divisibility by `(√2)^n` for a real residue `A + √2 B`, readable from
modulo `8` for `n ≤ 4`.  At level `4`, this means divisibility by at least
`(√2)^4 = 4`, which is all the finite KMM check needs. -/
def sqrtTwoGDEGePair : Nat → ZMod 8 → ZMod 8 → Bool
  | 0, _, _ => true
  | 1, A, _ => div2 A
  | 2, A, B => div2 A && div2 B
  | 3, A, B => div4 A && div2 B
  | 4, A, B => div4 A && div4 B
  | _, _, _ => false

def sqrtTwoGDEEqPair (n : Nat) (A B : ZMod 8) : Bool :=
  if n = 4 then
    sqrtTwoGDEGePair 4 A B
  else
    sqrtTwoGDEGePair n A B && !sqrtTwoGDEGePair (n + 1) A B

private theorem even_int_of_zmod8_val_even (P : ℤ)
    (h : (((P : ZMod 8).val) % 2 = 0)) :
    Even P := by
  let A : ZMod 8 := (P : ZMod 8)
  have hAval_even : Even (A.val : ℤ) := by
    rw [Int.even_iff]
    exact_mod_cast h
  have hmod : P ≡ (A.val : ℤ) [ZMOD (8 : ℤ)] := by
    have hz : ((A.val : ℤ) : ZMod 8) = (P : ZMod 8) := by
      simpa [A] using (ZMod.natCast_zmod_val A)
    have hiff := (ZMod.intCast_eq_intCast_iff (A.val : ℤ) P 8)
    have hmod' : (A.val : ℤ) ≡ P [ZMOD (8 : ℤ)] := hiff.mp hz
    exact hmod'.symm
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨r, hr⟩
  rcases hAval_even with ⟨s, hs⟩
  use s - 4 * r
  omega

private theorem four_dvd_int_of_zmod8_val_div4 (P : ℤ)
    (h : (((P : ZMod 8).val) % 4 = 0)) :
    (4 : ℤ) ∣ P := by
  let A : ZMod 8 := (P : ZMod 8)
  have hAval : (4 : ℤ) ∣ (A.val : ℤ) := by
    exact_mod_cast Nat.dvd_of_mod_eq_zero h
  have hmod : P ≡ (A.val : ℤ) [ZMOD (8 : ℤ)] := by
    have hz : ((A.val : ℤ) : ZMod 8) = (P : ZMod 8) := by
      simpa [A] using (ZMod.natCast_zmod_val A)
    have hiff := (ZMod.intCast_eq_intCast_iff (A.val : ℤ) P 8)
    have hmod' : (A.val : ℤ) ≡ P [ZMOD (8 : ℤ)] := hiff.mp hz
    exact hmod'.symm
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨r, hr⟩
  rcases hAval with ⟨s, hs⟩
  refine ⟨s - 2 * r, ?_⟩
  omega

private theorem zmod8_val_even_of_val_div4 {A : ZMod 8}
    (h : A.val % 4 = 0) :
    A.val % 2 = 0 := by
  have h4 : 4 ∣ A.val := Nat.dvd_of_mod_eq_zero h
  rcases h4 with ⟨r, hr⟩
  rw [hr]
  omega

theorem even_left_of_sqrtTwoGDEEqPair_pos
    {n : Nat} {P Q : ℤ}
    (hn : 1 ≤ n) (hn4 : n ≤ 4)
    (h : sqrtTwoGDEEqPair n (P : ZMod 8) (Q : ZMod 8) = true) :
    Even P := by
  interval_cases n <;>
    simp [sqrtTwoGDEEqPair, sqrtTwoGDEGePair, div2, div4, Bool.and_eq_true] at h
  · exact even_int_of_zmod8_val_even P h.1
  · exact even_int_of_zmod8_val_even P h.1.1
  · exact even_int_of_zmod8_val_even P (zmod8_val_even_of_val_div4 h.1.1)
  · exact even_int_of_zmod8_val_even P (zmod8_val_even_of_val_div4 h.1)

theorem four_dvd_left_of_sqrtTwoGDEEqPair_ge_three
    {n : Nat} {P Q : ℤ}
    (hn : 3 ≤ n) (hn4 : n ≤ 4)
    (h : sqrtTwoGDEEqPair n (P : ZMod 8) (Q : ZMod 8) = true) :
    (4 : ℤ) ∣ P := by
  interval_cases n <;>
    simp [sqrtTwoGDEEqPair, sqrtTwoGDEGePair, div2, div4, Bool.and_eq_true] at h
  · exact four_dvd_int_of_zmod8_val_div4 P h.1.1
  · exact four_dvd_int_of_zmod8_val_div4 P h.1

theorem even_right_of_sqrtTwoGDEEqPair_ge_three
    {n : Nat} {P Q : ℤ}
    (hn : 3 ≤ n) (hn4 : n ≤ 4)
    (h : sqrtTwoGDEEqPair n (P : ZMod 8) (Q : ZMod 8) = true) :
    Even Q := by
  interval_cases n <;>
    simp [sqrtTwoGDEEqPair, sqrtTwoGDEGePair, div2, div4, Bool.and_eq_true] at h
  · exact even_int_of_zmod8_val_even Q h.1.2
  · exact even_int_of_zmod8_val_even Q (zmod8_val_even_of_val_div4 h.2)

theorem four_dvd_right_of_sqrtTwoGDEEqPair_four
    {P Q : ℤ}
    (h : sqrtTwoGDEEqPair 4 (P : ZMod 8) (Q : ZMod 8) = true) :
    (4 : ℤ) ∣ Q := by
  simp [sqrtTwoGDEEqPair, sqrtTwoGDEGePair, div4, Bool.and_eq_true] at h
  exact four_dvd_int_of_zmod8_val_div4 Q h.2

theorem even_pair_of_sqrtTwoGDEGePair_two
    {P Q : ℤ}
    (h : sqrtTwoGDEGePair 2 (P : ZMod 8) (Q : ZMod 8) = true) :
    Even P ∧ Even Q := by
  simp [sqrtTwoGDEGePair, div2, Bool.and_eq_true] at h
  exact ⟨even_int_of_zmod8_val_even P h.1,
    even_int_of_zmod8_val_even Q h.2⟩

/-- The KMM residue class condition for `gde(|x|²) = j`, for `j = 0,1`. -/
def normGDEEq (j : Nat) (x : OmegaResidue) : Bool :=
  sqrtTwoGDEEqPair j (P x) (Q x)

theorem sqrtTwoGDEGePair_neg (j : Nat) (P Q : ZMod 8) :
    sqrtTwoGDEGePair j (-P) (-Q) = sqrtTwoGDEGePair j P Q := by
  rcases j with _ | _ | _ | _ | _ | j
  · rfl
  · fin_cases P <;> fin_cases Q <;> native_decide
  · fin_cases P <;> fin_cases Q <;> native_decide
  · fin_cases P <;> fin_cases Q <;> native_decide
  · fin_cases P <;> fin_cases Q <;> native_decide
  · rfl

theorem sqrtTwoGDEEqPair_neg (j : Nat) (P Q : ZMod 8) :
    sqrtTwoGDEEqPair j (-P) (-Q) = sqrtTwoGDEEqPair j P Q := by
  unfold sqrtTwoGDEEqPair
  split <;> rename_i h
  · rw [sqrtTwoGDEGePair_neg]
  · rw [sqrtTwoGDEGePair_neg, sqrtTwoGDEGePair_neg]

theorem normGDEEq_of_neg_norm_pair
    {j : Nat} {x y : OmegaResidue}
    (hx : normGDEEq j x = true)
    (hP : P x + P y = 0)
    (hQ : Q x + Q y = 0) :
    normGDEEq j y = true := by
  have hPy : P y = -P x := eq_neg_of_add_eq_zero_right hP
  have hQy : Q y = -Q x := eq_neg_of_add_eq_zero_right hQ
  unfold normGDEEq at *
  rw [hPy, hQy, sqrtTwoGDEEqPair_neg]
  exact hx

/-- Analog of `normGDEEq_of_neg_norm_pair` for the `P + P' = 4` residue condition
that arises at `omegaSDE z = 2` (where the unit-state parity constraint gives
`P x + P y = 4` instead of `0`).  The parity of `P x` and `Q x` is preserved
when passing to `P y = 4 - P x`, `Q y = -Q x`. -/
theorem normGDEEq_of_four_minus_pair
    {j : Nat} (hj : j = 0 ∨ j = 1) {x y : OmegaResidue}
    (hx : normGDEEq j x = true)
    (hP : P x + P y = 4)
    (hQ : Q x + Q y = 0) :
    normGDEEq j y = true := by
  have hPy : P y = 4 - P x := by linear_combination hP
  have hQy : Q y = -Q x := eq_neg_of_add_eq_zero_right hQ
  rw [normGDEEq, hPy, hQy]
  have hj0 : ∀ A B : ZMod 8,
      sqrtTwoGDEEqPair 0 A B = true → sqrtTwoGDEEqPair 0 (4 - A) (-B) = true := by
    native_decide
  have hj1 : ∀ A B : ZMod 8,
      sqrtTwoGDEEqPair 1 A B = true → sqrtTwoGDEEqPair 1 (4 - A) (-B) = true := by
    native_decide
  rw [normGDEEq] at hx
  rcases hj with rfl | rfl
  · exact hj0 _ _ hx
  · exact hj1 _ _ hx

def compatiblePair (j : Nat) (x y : OmegaResidue) : Bool :=
  normGDEEq j x &&
    normGDEEq j y &&
    decide (P x + P y = 0) &&
    decide (Q x + Q y = 0)

def transformed (k : Nat) (x y : OmegaResidue) : OmegaResidue :=
  add x (omegaPowMul k y)

theorem ofIntCoord_add (x y : OmegaIntCoord) :
    ofIntCoord (OmegaIntCoord.add x y) = add (ofIntCoord x) (ofIntCoord y) := by
  cases x
  cases y
  simp [ofIntCoord, add, OmegaIntCoord.add]

theorem ofIntCoord_omegaMul (x : OmegaIntCoord) :
    ofIntCoord (OmegaIntCoord.omegaMul x) = omegaMul (ofIntCoord x) := by
  cases x
  simp [ofIntCoord, omegaMul, OmegaIntCoord.omegaMul]

theorem ofIntCoord_omegaPowMul (n : Nat) (x : OmegaIntCoord) :
    ofIntCoord (OmegaIntCoord.omegaPowMul n x) =
      omegaPowMul n (ofIntCoord x) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [OmegaIntCoord.omegaPowMul, omegaPowMul, ofIntCoord_omegaMul, ih]

theorem ofIntCoord_transformed (k : Nat) (x y : OmegaIntCoord) :
    ofIntCoord (OmegaIntCoord.add x (OmegaIntCoord.omegaPowMul k y)) =
      transformed k (ofIntCoord x) (ofIntCoord y) := by
  simp [transformed, ofIntCoord_add, ofIntCoord_omegaPowMul]

theorem P_ofIntCoord (x : OmegaIntCoord) :
    P (ofIntCoord x) = (OmegaIntCoord.P x : ZMod 8) := by
  cases x
  simp [P, ofIntCoord, OmegaIntCoord.P]

theorem Q_ofIntCoord (x : OmegaIntCoord) :
    Q (ofIntCoord x) = (OmegaIntCoord.Q x : ZMod 8) := by
  cases x
  simp [Q, ofIntCoord, OmegaIntCoord.Q]

def reachesGDE (j d : Nat) (x y : OmegaResidue) : Bool :=
  [0, 1, 2, 3].any fun k =>
    let t := transformed k x y
    sqrtTwoGDEEqPair (d + j) (P t) (Q t)

def pairPasses (j : Nat) (x y : OmegaResidue) : Bool :=
  if compatiblePair j x y then
    [1, 2, 3].all fun d => reachesGDE j d x y
  else
    true

/-- Residues with fixed `gde(|x|²) = j` and fixed norm-pair residue.

This is the paper's finite verification shape.  Grouping before checking pairs
keeps the executable proof small enough to run, because the unit-state
condition only pairs a norm residue `(P,Q)` with its negative. -/
def group (j : Nat) (A B : ZMod 8) : List OmegaResidue :=
  all.filter fun x =>
    normGDEEq j x && decide (P x = A) && decide (Q x = B)

def groupPairPasses (j : Nat) (A B : ZMod 8) : Bool :=
  let xs := group j A B
  let ys := group j (-A) (-B)
  xs.all fun x =>
    ys.all fun y =>
      [1, 2, 3].all fun d => reachesGDE j d x y

def allPairsPass (j : Nat) : Bool :=
  residueValues.all fun A =>
    residueValues.all fun B =>
      groupPairPasses j A B

/-- Executable form of KMM Algorithm 2 over residue classes modulo `8`. -/
def kmmResidueCheck : Bool :=
  allPairsPass 0 && allPairsPass 1

/-- KMM's finite mod-8 verification.  This is the computer-assisted finite
case check from the paper, but expressed as a kernel-checked Lean computation. -/
theorem kmmResidueCheck_eq_true : kmmResidueCheck = true := by
  native_decide

private theorem mem_residueValues (a : ZMod 8) :
    a ∈ (residueValues : List (ZMod 8)) := by
  fin_cases a <;> native_decide

private theorem mem_all (x : OmegaResidue) :
    x ∈ (all : List OmegaResidue) := by
  cases x
  simp [all, mem_residueValues]

private theorem allPairsPass_eq_true_of_residue_check
    {j : Nat} (hj : j = 0 ∨ j = 1) :
    allPairsPass j = true := by
  have hcheck := kmmResidueCheck_eq_true
  unfold kmmResidueCheck at hcheck
  rw [Bool.and_eq_true] at hcheck
  rcases hj with rfl | rfl
  · exact hcheck.1
  · exact hcheck.2

/-- Residue-level KMM choice extracted from the executable check.

If two omega-basis residue numerators are compatible with the unit-state
constraint and `gde(|x|²) = gde(|y|²) = j`, then the finite KMM table says that
for each required denominator change `d ∈ {1,2,3}` one of the four
`x + ω^k y`, `k = 0,1,2,3`, has the target norm `gde` residue. -/
theorem residue_choice_all_d
    {j : Nat} (hj : j = 0 ∨ j = 1)
    {x y : OmegaResidue}
    (hcompat : compatiblePair j x y = true) :
    [1, 2, 3].all fun d => reachesGDE j d x y := by
  have hall := allPairsPass_eq_true_of_residue_check hj
  unfold allPairsPass at hall
  have hA := (List.all_eq_true.mp hall (P x) (mem_residueValues (P x)))
  have hB := (List.all_eq_true.mp hA (Q x) (mem_residueValues (Q x)))
  unfold groupPairPasses at hB
  have hcompat' :
      normGDEEq j x = true ∧ normGDEEq j y = true ∧
        decide (P x + P y = 0) = true ∧
          decide (Q x + Q y = 0) = true := by
    simpa [compatiblePair, Bool.and_eq_true, and_assoc] using hcompat
  have hPxPy : P x + P y = 0 := of_decide_eq_true hcompat'.2.2.1
  have hQxQy : Q x + Q y = 0 := of_decide_eq_true hcompat'.2.2.2
  have hPy : P y = -P x := eq_neg_of_add_eq_zero_right hPxPy
  have hQy : Q y = -Q x := eq_neg_of_add_eq_zero_right hQxQy
  have hxmem : x ∈ group j (P x) (Q x) := by
    simp [group, mem_all, hcompat'.1]
  have hymem : y ∈ group j (-P x) (-Q x) := by
    simp [group, mem_all, hcompat'.2.1, hPy, hQy]
  exact List.all_eq_true.mp (List.all_eq_true.mp hB x hxmem) y hymem

theorem residue_choice_for_d
    {j d : Nat} (hj : j = 0 ∨ j = 1)
    {x y : OmegaResidue}
    (hcompat : compatiblePair j x y = true)
    (hd : d ∈ ([1, 2, 3] : List Nat)) :
    ∃ k : Fin 4,
      let t := transformed (k : ℕ) x y
      sqrtTwoGDEEqPair (d + j) (P t) (Q t) = true := by
  have hall := residue_choice_all_d hj hcompat
  have hdany := List.all_eq_true.mp hall d hd
  rcases (List.any_eq_true.mp hdany) with ⟨k, hkmem, hk⟩
  refine ⟨⟨k, ?_⟩, ?_⟩
  · simp at hkmem
    omega
  · simpa using hk

/-- Integer-coordinate form of the KMM finite residue bridge. -/
theorem intCoord_choice_for_d
    {j d : Nat} (hj : j = 0 ∨ j = 1)
    {x y : OmegaIntCoord}
    (hcompat : compatiblePair j (ofIntCoord x) (ofIntCoord y) = true)
    (hd : d ∈ ([1, 2, 3] : List Nat)) :
    ∃ k : Fin 4,
      let t := transformed (k : ℕ) (ofIntCoord x) (ofIntCoord y)
      sqrtTwoGDEEqPair (d + j) (P t) (Q t) = true :=
  residue_choice_for_d hj hcompat hd

end OmegaResidue

/-- Divisibility by `(√2)^n` for a real omega-integer norm
`P + √2 Q`. It is represented by the residue test used by KMM's finite
mod-8 verification. -/
def SqrtTwoNormPairGDEGe (n : ℕ) (P Q : ℤ) : Prop :=
  OmegaResidue.sqrtTwoGDEGePair n (P : ZMod 8) (Q : ZMod 8) = true

/-- Exact `√2`-GDE for a real omega-integer norm pair, in the residue form
used by KMM's mod-8 verification. -/
def SqrtTwoNormPairGDEEq (n : ℕ) (P Q : ℤ) : Prop :=
  OmegaResidue.sqrtTwoGDEEqPair n (P : ZMod 8) (Q : ZMod 8) = true

/-- Exact `√2`-GDE of the norm `x†x`, using `x†x = P(x)+√2 Q(x)`. -/
def SqrtTwoNormGDEEq (x : OmegaIntCoord) (n : ℕ) : Prop :=
  SqrtTwoNormPairGDEEq n (OmegaIntCoord.P x) (OmegaIntCoord.Q x)

theorem sqrtTwoNormGDEEq_iff_residue (x : OmegaIntCoord) (n : ℕ) :
    SqrtTwoNormGDEEq x n ↔
      OmegaResidue.normGDEEq n (OmegaResidue.ofIntCoord x) = true := by
  simp [SqrtTwoNormGDEEq, SqrtTwoNormPairGDEEq, OmegaResidue.normGDEEq,
    OmegaResidue.P_ofIntCoord, OmegaResidue.Q_ofIntCoord]

theorem normGDEEq_residue_of_sqrtTwoNormGDEEq
    {x : OmegaIntCoord} {n : ℕ}
    (h : SqrtTwoNormGDEEq x n) :
    OmegaResidue.normGDEEq n (OmegaResidue.ofIntCoord x) = true :=
  (sqrtTwoNormGDEEq_iff_residue x n).mp h

theorem sqrtTwoNormGDEEq_of_residue_normGDEEq
    {x : OmegaIntCoord} {n : ℕ}
    (h : OmegaResidue.normGDEEq n (OmegaResidue.ofIntCoord x) = true) :
    SqrtTwoNormGDEEq x n :=
  (sqrtTwoNormGDEEq_iff_residue x n).mpr h

theorem norm_pair_gde_ge_two_sqrtTwo_dvd
    (x : OmegaIntCoord)
    (h : SqrtTwoNormPairGDEGe 2 (OmegaIntCoord.P x) (OmegaIntCoord.Q x)) :
    ∃ q : OmegaIntCoord, OmegaIntCoord.val x = sqrtTwoComplex * OmegaIntCoord.val q := by
  rcases OmegaResidue.even_pair_of_sqrtTwoGDEGePair_two h with ⟨hP, hQ⟩
  exact OmegaIntCoord.val_dvd_sqrtTwo_of_norm_pair_even x hP hQ

/-! ### Low-SDE descent checks (DenNormSDE ∈ {3, 4})

These `native_decide`-verified checks cover the two residue cases that arise
when `DenNormSDE z ∈ {3, 4}` (omegaSDE z = 2).  In both cases the unit-state
condition forces `P_x + P_y = 4` mod 8 (not 0), so the standard KMM
compatible-pair criterion fails.  But a direct finite check shows that at
least one of the four `H T^k` transforms still raises the GDE of the
transformed norm pair by the required amount. -/

/-- For pairs with `normGDEEq 0` (P odd) and `P + P' ≡ 4`, `Q + Q' ≡ 0`
(mod 8) — the unit-state residue at `DenNormSDE z = 4` — some transform
`x + ω^k y` achieves `sqrtTwoGDEGePair 3`, i.e. GDE ≥ 3. -/
private def sde4PairDescentCheck : Bool :=
  OmegaResidue.residueValues.all fun A =>
    OmegaResidue.residueValues.all fun B =>
      let xs := OmegaResidue.all.filter fun x =>
        OmegaResidue.normGDEEq 0 x &&
          decide (OmegaResidue.P x = A) && decide (OmegaResidue.Q x = B)
      let ys := OmegaResidue.all.filter fun y =>
        OmegaResidue.normGDEEq 0 y &&
          decide (OmegaResidue.P y = (4 : ZMod 8) - A) &&
          decide (OmegaResidue.Q y = -B)
      xs.all fun x => ys.all fun y =>
        [0, 1, 2, 3].any fun k =>
          OmegaResidue.sqrtTwoGDEGePair 3
            (OmegaResidue.P (OmegaResidue.transformed k x y))
            (OmegaResidue.Q (OmegaResidue.transformed k x y))

private theorem sde4PairDescentCheck_eq_true :
    sde4PairDescentCheck = true := by native_decide

/-- For pairs with `normGDEEq 1` (P even, Q odd) and `P + P' ≡ 4`, `Q + Q' ≡ 0`
(mod 8) — the unit-state residue at `DenNormSDE z = 3` — some transform
achieves `sqrtTwoGDEGePair 4`, i.e. GDE ≥ 4. -/
private def sde3PairDescentCheck : Bool :=
  OmegaResidue.residueValues.all fun A =>
    OmegaResidue.residueValues.all fun B =>
      let xs := OmegaResidue.all.filter fun x =>
        OmegaResidue.normGDEEq 1 x &&
          decide (OmegaResidue.P x = A) && decide (OmegaResidue.Q x = B)
      let ys := OmegaResidue.all.filter fun y =>
        OmegaResidue.normGDEEq 1 y &&
          decide (OmegaResidue.P y = (4 : ZMod 8) - A) &&
          decide (OmegaResidue.Q y = -B)
      xs.all fun x => ys.all fun y =>
        [0, 1, 2, 3].any fun k =>
          OmegaResidue.sqrtTwoGDEGePair 4
            (OmegaResidue.P (OmegaResidue.transformed k x y))
            (OmegaResidue.Q (OmegaResidue.transformed k x y))

private theorem sde3PairDescentCheck_eq_true :
    sde3PairDescentCheck = true := by native_decide

/-- For `DenNormSDE z = 4` pairs at level 2, some `H T^k` gives GDE ≥ 3 on the
transformed norm pair, enabling the one-step denominator descent. -/
theorem sde4_descent_choice
    {x y : OmegaIntCoord}
    (hNormX : OmegaResidue.normGDEEq 0 (OmegaResidue.ofIntCoord x) = true)
    (hNormY : OmegaResidue.normGDEEq 0 (OmegaResidue.ofIntCoord y) = true)
    (hP : (OmegaResidue.P (OmegaResidue.ofIntCoord x) : ZMod 8) +
            OmegaResidue.P (OmegaResidue.ofIntCoord y) = 4)
    (hQ : OmegaResidue.Q (OmegaResidue.ofIntCoord x) +
            OmegaResidue.Q (OmegaResidue.ofIntCoord y) = 0) :
    ∃ k : Fin 4,
      let t := OmegaResidue.transformed (k : ℕ)
        (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y)
      OmegaResidue.sqrtTwoGDEGePair 3 (OmegaResidue.P t) (OmegaResidue.Q t)
        = true := by
  have hcheck := sde4PairDescentCheck_eq_true
  unfold sde4PairDescentCheck at hcheck
  have hA := List.all_eq_true.mp hcheck (OmegaResidue.P (OmegaResidue.ofIntCoord x))
    (OmegaResidue.mem_residueValues _)
  have hB := List.all_eq_true.mp hA (OmegaResidue.Q (OmegaResidue.ofIntCoord x))
    (OmegaResidue.mem_residueValues _)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
  have hxmem : OmegaResidue.ofIntCoord x ∈
      OmegaResidue.all.filter fun x' =>
        OmegaResidue.normGDEEq 0 x' &&
          decide (OmegaResidue.P x' = OmegaResidue.P (OmegaResidue.ofIntCoord x)) &&
          decide (OmegaResidue.Q x' = OmegaResidue.Q (OmegaResidue.ofIntCoord x)) := by
    simp [OmegaResidue.mem_all, hNormX]
  have hymem : OmegaResidue.ofIntCoord y ∈
      OmegaResidue.all.filter fun y' =>
        OmegaResidue.normGDEEq 0 y' &&
          decide (OmegaResidue.P y' = (4 : ZMod 8) -
            OmegaResidue.P (OmegaResidue.ofIntCoord x)) &&
          decide (OmegaResidue.Q y' = -OmegaResidue.Q (OmegaResidue.ofIntCoord x)) := by
    have hPy : OmegaResidue.P (OmegaResidue.ofIntCoord y) =
        (4 : ZMod 8) - OmegaResidue.P (OmegaResidue.ofIntCoord x) := by
      linear_combination hP
    have hQy : OmegaResidue.Q (OmegaResidue.ofIntCoord y) =
        -OmegaResidue.Q (OmegaResidue.ofIntCoord x) := by
      linear_combination hQ
    simp [OmegaResidue.mem_all, hNormY, hPy, hQy]
  rcases List.any_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp hB _ hxmem) _ hymem) with ⟨k, hkmem, hk⟩
  exact ⟨⟨k, by simp at hkmem; omega⟩, by simpa using hk⟩

/-- For `DenNormSDE z = 3` pairs at level 2, some `H T^k` gives GDE ≥ 4 on the
transformed norm pair, enabling a two-level denominator descent to ≤ 2. -/
theorem sde3_descent_choice
    {x y : OmegaIntCoord}
    (hNormX : OmegaResidue.normGDEEq 1 (OmegaResidue.ofIntCoord x) = true)
    (hNormY : OmegaResidue.normGDEEq 1 (OmegaResidue.ofIntCoord y) = true)
    (hP : (OmegaResidue.P (OmegaResidue.ofIntCoord x) : ZMod 8) +
            OmegaResidue.P (OmegaResidue.ofIntCoord y) = 4)
    (hQ : OmegaResidue.Q (OmegaResidue.ofIntCoord x) +
            OmegaResidue.Q (OmegaResidue.ofIntCoord y) = 0) :
    ∃ k : Fin 4,
      let t := OmegaResidue.transformed (k : ℕ)
        (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y)
      OmegaResidue.sqrtTwoGDEGePair 4 (OmegaResidue.P t) (OmegaResidue.Q t)
        = true := by
  have hcheck := sde3PairDescentCheck_eq_true
  unfold sde3PairDescentCheck at hcheck
  have hA := List.all_eq_true.mp hcheck (OmegaResidue.P (OmegaResidue.ofIntCoord x))
    (OmegaResidue.mem_residueValues _)
  have hB := List.all_eq_true.mp hA (OmegaResidue.Q (OmegaResidue.ofIntCoord x))
    (OmegaResidue.mem_residueValues _)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
  have hxmem : OmegaResidue.ofIntCoord x ∈
      OmegaResidue.all.filter fun x' =>
        OmegaResidue.normGDEEq 1 x' &&
          decide (OmegaResidue.P x' = OmegaResidue.P (OmegaResidue.ofIntCoord x)) &&
          decide (OmegaResidue.Q x' = OmegaResidue.Q (OmegaResidue.ofIntCoord x)) := by
    simp [OmegaResidue.mem_all, hNormX]
  have hymem : OmegaResidue.ofIntCoord y ∈
      OmegaResidue.all.filter fun y' =>
        OmegaResidue.normGDEEq 1 y' &&
          decide (OmegaResidue.P y' = (4 : ZMod 8) -
            OmegaResidue.P (OmegaResidue.ofIntCoord x)) &&
          decide (OmegaResidue.Q y' = -OmegaResidue.Q (OmegaResidue.ofIntCoord x)) := by
    have hPy : OmegaResidue.P (OmegaResidue.ofIntCoord y) =
        (4 : ZMod 8) - OmegaResidue.P (OmegaResidue.ofIntCoord x) := by
      linear_combination hP
    have hQy : OmegaResidue.Q (OmegaResidue.ofIntCoord y) =
        -OmegaResidue.Q (OmegaResidue.ofIntCoord x) := by
      linear_combination hQ
    simp [OmegaResidue.mem_all, hNormY, hPy, hQy]
  rcases List.any_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp hB _ hxmem) _ hymem) with ⟨k, hkmem, hk⟩
  exact ⟨⟨k, by simp at hkmem; omega⟩, by simpa using hk⟩

end KMM

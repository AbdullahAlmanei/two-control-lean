import TwoControl.KMM.OmegaArithmetic

open DyadicCyclotomic
open TwoControl.KMM

/-!
Concrete `ℤ[ω]` arithmetic needed by the Ross-Selinger Diophantine layer.

The KMM development already uses `OmegaIntCoord` for
`x₀ + x₁ω + x₂ω² + x₃ω³`.  This file extends that coordinate API with the
ring operations and conjugation lemmas needed to state the norm-equation
factorization step without introducing a second representation of `ℤ[ω]`.
-/

namespace TwoControl.KMM.OmegaIntCoord

private theorem inDyadicCyclotomic_int (m : ℤ) :
    InDyadicCyclotomic (m : ℂ) := by
  refine ⟨0, m, 0, 0, 0, ?_⟩
  simp [sqrtTwoComplex]

def zero : OmegaIntCoord where
  x0 := 0
  x1 := 0
  x2 := 0
  x3 := 0

def one : OmegaIntCoord where
  x0 := 1
  x1 := 0
  x2 := 0
  x3 := 0

/-- Multiplication in the basis `1,ω,ω²,ω³`, reducing by `ω⁴ = -1`. -/
def mul (x y : OmegaIntCoord) : OmegaIntCoord where
  x0 := x.x0 * y.x0 - x.x1 * y.x3 - x.x2 * y.x2 - x.x3 * y.x1
  x1 := x.x0 * y.x1 + x.x1 * y.x0 - x.x2 * y.x3 - x.x3 * y.x2
  x2 := x.x0 * y.x2 + x.x1 * y.x1 + x.x2 * y.x0 - x.x3 * y.x3
  x3 := x.x0 * y.x3 + x.x1 * y.x2 + x.x2 * y.x1 + x.x3 * y.x0

/-- Complex conjugation on `ℤ[ω]`: `ω† = ω⁻¹ = -ω³`. -/
def conj (x : OmegaIntCoord) : OmegaIntCoord where
  x0 := x.x0
  x1 := -x.x3
  x2 := -x.x2
  x3 := -x.x1

def sub (x y : OmegaIntCoord) : OmegaIntCoord :=
  add x (neg y)

theorem val_zero :
    val zero = 0 := by
  simp [zero, val]

theorem val_one :
    val one = 1 := by
  simp [one, val]

theorem val_sub (x y : OmegaIntCoord) :
    val (sub x y) = val x - val y := by
  simp [sub, val_add, val_neg]
  ring

theorem val_mul (x y : OmegaIntCoord) :
    val (mul x y) = val x * val y := by
  cases x
  cases y
  simp [mul, val]
  ring_nf
  simp [rsOmegaAlg_four, rsOmegaAlg_five, rsOmegaAlg_six]
  ring

theorem val_conj (x : OmegaIntCoord) :
    val (conj x) = star (val x) := by
  cases x
  simp [conj, val, star_add, star_mul, star_rsOmegaAlg]
  ring_nf
  simp [rsOmegaAlg_six, rsOmegaAlg_nine]
  ring

theorem val_conj_mul_self (x : OmegaIntCoord) :
    val (mul (conj x) x) =
      (P x : ℂ) + (Q x : ℂ) * sqrtTwoComplex := by
  rw [val_mul, val_conj, norm_val]

/-- The norm pair of a product, characterized by the already-proved complex
norm identity.  This is deliberately stated as an equality in `ℂ`, avoiding a
coordinate-uniqueness detour for `ℤ[√2]`. -/
theorem normPair_mul_eval (x y : OmegaIntCoord) :
    ((P (mul x y) : ℂ) + (Q (mul x y) : ℂ) * sqrtTwoComplex) =
      ((P x : ℂ) + (Q x : ℂ) * sqrtTwoComplex) *
        ((P y : ℂ) + (Q y : ℂ) * sqrtTwoComplex) := by
  calc
    ((P (mul x y) : ℂ) + (Q (mul x y) : ℂ) * sqrtTwoComplex)
        = star (val (mul x y)) * val (mul x y) := by
            rw [norm_val]
    _ = star (val x * val y) * (val x * val y) := by rw [val_mul]
    _ = (star (val x) * val x) * (star (val y) * val y) := by
            simp [star_mul]
            ring
    _ = ((P x : ℂ) + (Q x : ℂ) * sqrtTwoComplex) *
          ((P y : ℂ) + (Q y : ℂ) * sqrtTwoComplex) := by
            rw [norm_val, norm_val]

/-- An omega-coordinate integer is an element of `D[ω]`. -/
theorem val_in_dyadic (x : OmegaIntCoord) :
    InDyadicCyclotomic (val x) := by
  dsimp [val]
  exact
    InDyadicCyclotomic.add
      (InDyadicCyclotomic.add
        (InDyadicCyclotomic.add
          (inDyadicCyclotomic_int _)
          (InDyadicCyclotomic.mul (inDyadicCyclotomic_int _) rsOmegaAlg_in_dyadic))
        (InDyadicCyclotomic.mul (inDyadicCyclotomic_int _)
          (rsOmegaAlg_pow_in_dyadic 2)))
      (InDyadicCyclotomic.mul (inDyadicCyclotomic_int _)
        (rsOmegaAlg_pow_in_dyadic 3))

/-- Scaling an omega-coordinate integer by a power of `√2` stays in `D[ω]`. -/
theorem val_div_sqrtTwo_pow_in_dyadic (x : OmegaIntCoord) (k : ℕ) :
    InDyadicCyclotomic (val x / sqrtTwoComplex ^ k) := by
  induction k with
  | zero =>
      simpa using val_in_dyadic x
  | succ k ih =>
      have hstep : val x / sqrtTwoComplex ^ (k + 1) =
          (val x / sqrtTwoComplex ^ k) / sqrtTwoComplex := by
        field_simp [sqrtTwoComplex_ne_zero, pow_ne_zero k sqrtTwoComplex_ne_zero,
          pow_ne_zero (k + 1) sqrtTwoComplex_ne_zero]
        ring
      rw [hstep]
      exact InDyadicCyclotomic.div_sqrtTwo ih

end OmegaIntCoord
end TwoControl.KMM

namespace TwoControl
namespace RossSelinger

/-- A real `D[√2]` value written as a normalized pair over a power of `√2`. -/
structure DyadicSqrtTwoPair where
  level : ℕ
  A : ℤ
  B : ℤ
deriving Repr

namespace DyadicSqrtTwoPair

noncomputable def val (ξ : DyadicSqrtTwoPair) : ℂ :=
  ((ξ.A : ℂ) + (ξ.B : ℂ) * sqrtTwoComplex) / sqrtTwoComplex ^ ξ.level

noncomputable def bulletVal (ξ : DyadicSqrtTwoPair) : ℂ :=
  ((ξ.A : ℂ) - (ξ.B : ℂ) * sqrtTwoComplex) /
    (((-Real.sqrt 2 : ℝ) : ℂ) ^ ξ.level)

theorem in_dyadic_sqrtTwo_re (ξ : DyadicSqrtTwoPair) :
    InDyadicSqrtTwo (ξ.val.re) := by
  refine ⟨ξ.level, ξ.A, ξ.B, ?_⟩
  unfold val sqrtTwoComplex
  rw [show (((Real.sqrt 2 : ℝ) : ℂ) ^ ξ.level) =
      ((Real.sqrt 2 ^ ξ.level : ℝ) : ℂ) by
        exact (Complex.ofReal_pow (Real.sqrt 2) ξ.level).symm]
  rw [Complex.div_ofReal_re]
  simp

theorem val_im (ξ : DyadicSqrtTwoPair) :
    ξ.val.im = 0 := by
  unfold val sqrtTwoComplex
  have hnumim :
      (((ξ.A : ℂ) + (ξ.B : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)).im) = 0 := by
    simp
  have hdenim : ((((Real.sqrt 2 : ℝ) : ℂ) ^ ξ.level).im) = 0 := by
    induction ξ.level with
    | zero =>
        simp
    | succ n ih =>
        rw [pow_succ]
        simp [ih]
  rw [Complex.div_im]
  simp [hnumim, hdenim]

end DyadicSqrtTwoPair

/-- The hard algebraic-number-theory core of Ross-Selinger Theorem 6.2, stated
in the concrete coordinate vocabulary used by this project.

This is the Phase-3 theorem that remains to be proved by the Euclidean-domain
and mod-8 prime-splitting development for `ℤ[ω]`.  Once proved, the surrounding
Diophantine/oracle layer only needs a short wrapper. -/
def ZomegaNormEquationSolvable (ξ : DyadicSqrtTwoPair) : Prop :=
  ∃ k : ℕ, ∃ x : OmegaIntCoord,
    star (OmegaIntCoord.val x / sqrtTwoComplex ^ k) *
      (OmegaIntCoord.val x / sqrtTwoComplex ^ k) = ξ.val

end RossSelinger
end TwoControl

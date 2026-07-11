import RossSelinger.DiophantineCore
import Mathlib.Data.Complex.Basic

namespace RossSelinger

open TwoControl
open DyadicCyclotomic

/-!
# Gaussian Dyadic Norm Computation

Pure algebra for the small-ε Diophantine step of Ross-Selinger.

For integers `x y : ℤ` and `m : ℕ`, define the **Gaussian dyadic** complex
number `t = (x + yi) / 2^m`.  This file proves:

1. `gaussianDyadicC_inDyadic`: `t ∈ D[ω]` (b = d = 0 suffices).
2. `gaussianDyadicC_star_mul_self`: `t†t = (x² + y²) / 4^m`.
3. `completionXi_gaussianDyadicC`: `completionXi u = (4^m - a² - c²) / 4^m`
   when `u = (a + ci) / 2^m`.
4. `solvesNormEquation_of_sq_add_sq`: if `x² + y² = 4^m - a² - c²` then
   `SolvesNormEquation (completionXi u) t`.

No hard number theory is used — every proof is `simp`/`ring`/`push_cast`.
-/

-- ---------------------------------------------------------------------------
-- Local helper
-- ---------------------------------------------------------------------------

/-- `√2^(2·m) = 2^m` in ℂ. -/
private theorem sqrtTwo_pow_two_mul (m : ℕ) :
    sqrtTwoComplex ^ (2 * m) = (2 : ℂ) ^ m := by
  rw [pow_mul]
  simp [sqrtTwoComplex_sq]

-- ---------------------------------------------------------------------------
-- Definition
-- ---------------------------------------------------------------------------

/-- The Gaussian dyadic: `(x + yi) / 2^m ∈ ℂ`. -/
noncomputable def gaussianDyadicC (m : ℕ) (x y : ℤ) : ℂ :=
  ((x : ℂ) + (y : ℂ) * Complex.I) / sqrtTwoComplex ^ (2 * m)

-- ---------------------------------------------------------------------------
-- Membership in D[ω]
-- ---------------------------------------------------------------------------

theorem gaussianDyadicC_inDyadic (m : ℕ) (x y : ℤ) :
    InDyadicCyclotomic (gaussianDyadicC m x y) :=
  ⟨2 * m, x, 0, y, 0, by simp [gaussianDyadicC]⟩

-- ---------------------------------------------------------------------------
-- Norm: t†t = (x² + y²) / 4^m
-- ---------------------------------------------------------------------------

/-- The norm squared `(star t) * t` equals `(x² + y²) / 4^m`. -/
theorem gaussianDyadicC_star_mul_self (m : ℕ) (x y : ℤ) :
    star (gaussianDyadicC m x y) * gaussianDyadicC m x y =
      ((x ^ 2 + y ^ 2 : ℤ) : ℂ) / ((4 : ℂ) ^ m) := by
  -- Step 1: star t * t = ↑(normSq t)
  have hnorm : star (gaussianDyadicC m x y) * gaussianDyadicC m x y =
      ((Complex.normSq (gaussianDyadicC m x y) : ℝ) : ℂ) := by
    have := Complex.normSq_eq_conj_mul_self (z := gaussianDyadicC m x y)
    simpa using this.symm
  rw [hnorm]
  -- Step 2: normSq(t) = (x² + y²) / 4^m  (all in ℝ)
  have hval : Complex.normSq (gaussianDyadicC m x y) =
      ((x ^ 2 + y ^ 2 : ℤ) : ℝ) / (4 : ℝ) ^ m := by
    rw [gaussianDyadicC, Complex.normSq_div, map_pow Complex.normSq]
    -- normSq of sqrtTwoComplex = 2
    have hs : Complex.normSq sqrtTwoComplex = 2 := by
      simp only [sqrtTwoComplex, Complex.normSq_ofReal]
      norm_num [Real.sq_sqrt]
    rw [hs]
    -- normSq of numerator (x + yi) = x² + y²
    have hnum : Complex.normSq ((x : ℂ) + (y : ℂ) * Complex.I) =
        ((x ^ 2 + y ^ 2 : ℤ) : ℝ) := by
      calc
        Complex.normSq ((x : ℂ) + (y : ℂ) * Complex.I)
            = (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by
                simpa using (Complex.normSq_add_mul_I (x : ℝ) (y : ℝ))
        _ = ((x ^ 2 + y ^ 2 : ℤ) : ℝ) := by
            push_cast
            ring
    rw [hnum]
    -- 2^(2·m) = 4^m in ℝ
    rw [show (2 : ℝ) ^ (2 * m) = (4 : ℝ) ^ m from by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 from by norm_num, ← pow_mul]]
  rw [hval]
  -- Step 3: cast from ℝ to ℂ
  push_cast
  ring

-- ---------------------------------------------------------------------------
-- completionXi for a Gaussian dyadic
-- ---------------------------------------------------------------------------

/-- `completionXi ((a + ci)/2^m) = (4^m - a² - c²) / 4^m`. -/
theorem completionXi_gaussianDyadicC (m : ℕ) (a c : ℤ) :
    completionXi (gaussianDyadicC m a c) =
      ((4 ^ m - a ^ 2 - c ^ 2 : ℤ) : ℂ) / ((4 : ℂ) ^ m) := by
  simp only [completionXi, gaussianDyadicC_star_mul_self]
  have hne : ((4 : ℂ) ^ m) ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  field_simp
  push_cast
  ring

-- ---------------------------------------------------------------------------
-- Main result: solving the norm equation from a sum-of-squares identity
-- ---------------------------------------------------------------------------

/-- If `x² + y² = 4^m - a² - c²` then the Gaussian dyadic `(x + yi)/2^m`
solves the Ross-Selinger norm equation for `completionXi ((a + ci)/2^m)`. -/
theorem solvesNormEquation_of_sq_add_sq (m : ℕ) (a c x y : ℤ)
    (h : x ^ 2 + y ^ 2 = 4 ^ m - a ^ 2 - c ^ 2) :
    SolvesNormEquation
      (completionXi (gaussianDyadicC m a c))
      (gaussianDyadicC m x y) := by
  constructor
  · -- t ∈ D[ω]
    exact gaussianDyadicC_inDyadic m x y
  · -- t†t = completionXi u
    rw [gaussianDyadicC_star_mul_self, completionXi_gaussianDyadicC]
    rw [h]

end RossSelinger

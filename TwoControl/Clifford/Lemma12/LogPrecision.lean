import Mathlib.Data.Real.Archimedean

namespace TwoControl
namespace Clifford
namespace Lemma12

/-!
Logarithmic precision bookkeeping for quantitative Lemma 12.

`logPrecision epsilon` is the least natural number `k` whose power of two is
large enough to dominate `1 / epsilon`.  This is the Lean-side replacement for
informal expressions like `ceil(log_2(1/epsilon))`.
-/

/-- Powers of two eventually dominate the inverse of any positive precision. -/
theorem exists_nat_pow_two_inv_bound {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ k : ℕ, 1 / epsilon ≤ (2 : ℝ) ^ k := by
  sorry

/-- A natural-number precision scale, morally `ceil(log_2(1/epsilon))`.

For nonpositive `epsilon`, the value is irrelevant; all exported theorems use
the hypothesis `0 < epsilon`. -/
noncomputable def logPrecision (epsilon : ℝ) : ℕ :=
  if hepsilon : 0 < epsilon then
    Nat.find (exists_nat_pow_two_inv_bound hepsilon)
  else
    0

/-- The defining upper-power property of `logPrecision`. -/
theorem logPrecision_spec {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    1 / epsilon ≤ (2 : ℝ) ^ logPrecision epsilon := by
  dsimp [logPrecision]
  rw [dif_pos hepsilon]
  exact Nat.find_spec (exists_nat_pow_two_inv_bound hepsilon)

/-- `logPrecision` is minimal among natural exponents satisfying its power
bound. -/
theorem logPrecision_minimal {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {k : ℕ} (hk : 1 / epsilon ≤ (2 : ℝ) ^ k) :
    logPrecision epsilon ≤ k := by
  sorry

/-- Dividing the target precision by a fixed `C * 4^n + 1` budget increases
logarithmic precision by at most `2*n` plus a constant depending only on `C`. -/
theorem exists_logPrecision_mul_four_pow_overhead (C : ℕ) :
    ∃ overhead : ℕ,
      ∀ {n : ℕ} {epsilon : ℝ}, 0 < epsilon →
        logPrecision
            (epsilon / (((C * 4 ^ n : ℕ) : ℝ) + 1)) ≤
          logPrecision epsilon + 2 * n + overhead := by
  sorry

end Lemma12
end Clifford
end TwoControl

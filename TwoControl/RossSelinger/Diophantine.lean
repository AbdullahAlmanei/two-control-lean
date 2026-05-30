import TwoControl.RossSelinger.DiophantineCore
import TwoControl.RossSelinger.Grid
import TwoControl.RossSelinger.ZomegaRingTheory

namespace TwoControl.RossSelinger

open DyadicCyclotomic
open MatrixCompletion
open TwoControl.KMM

/-!
Ross-Selinger's Diophantine completion step.

For a grid candidate `u`, set `ξ = 1 - u†u`.  Completing `u` is exactly the
problem of solving `t†t = ξ` with `t ∈ D[ω]`.  Theorem 6.2 reduces this to
integer factorization; the oracle route assumes that factorization is available.

The compiler-facing path does not assume that every input has a completable
candidate.  Instead, a completion solver returns a witness `t` when it can,
and the sound-if-return theorem consumes only the returned norm-equation
certificate.  This file therefore keeps the algebraic bridge from a returned
Diophantine solution to `MatrixCompletion.NormEquation`; factorization and
termination are modeled by solver contracts in `Algorithm.lean`.
-/

theorem completionXi_in_dyadic_sqrtTwo {u : ℂ}
    (hu : InDyadicCyclotomic u) :
    InDyadicSqrtTwo (completionXi u).re := by
  unfold completionXi
  simp only [Complex.sub_re, Complex.one_re]
  exact InDyadicSqrtTwo.one_sub (star_mul_self_in_dyadicSqrtTwo hu)

/-- Theorem 6.2, packaged for the oracle proof: with exact factorization
available, the norm equation is decided and a witness is returned exactly when
one exists.  This statement is the law of excluded middle for the
solvability predicate; the `hξ` hypothesis is only carried to make the API
match the oracle interface. -/
theorem diophantine_oracle_finds_solution_iff
    {ξ : ℂ}
    (_hξ : InDyadicSqrtTwo ξ.re) :
    (∃ t : ℂ, SolvesNormEquation ξ t) ∨ ¬ ∃ t : ℂ, SolvesNormEquation ξ t :=
  Classical.em _

/-- Convert a concrete `ℤ[ω]` norm-equation solution into the project-level
`SolvesNormEquation` predicate. -/
theorem solvesNormEquation_of_zomegaNormEquationSolvable
    {ξ : DyadicSqrtTwoPair}
    (hξ : ZomegaNormEquationSolvable ξ) :
    ∃ t : ℂ, SolvesNormEquation ξ.val t := by
  rcases hξ with ⟨k, x, hx⟩
  refine ⟨OmegaIntCoord.val x / sqrtTwoComplex ^ k, ?_, hx⟩
  exact OmegaIntCoord.val_div_sqrtTwo_pow_in_dyadic x k

theorem normEquation_of_solves_completionXi {u t : ℂ}
    (h : SolvesNormEquation (completionXi u) t) :
    NormEquation u t := by
  exact normEquation_of_diophantine h.2

end RossSelinger
end TwoControl

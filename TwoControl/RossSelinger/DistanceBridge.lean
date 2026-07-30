import TwoControl.RossSelinger.Basic
import TwoControl.Clifford.Universal.Distance
import MatrixCompletion.Completion
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace TwoControl.RossSelinger

open TwoControl.Clifford
open TwoControl.Clifford.Universal
open MatrixCompletion
open scoped Matrix.Norms.L2Operator

/-!
Bridge Ross-Selinger's operator-norm approximation statement to the project's
Hilbert-Schmidt distance `hsDistance`.

This file is **part of the conditional Ross-Selinger compiler leg**.  It is
useful when promoting a circuit produced by Ross-Selinger from an `opDist`
bound to an `hsDistance` bound (for example when comparing the RS output
against the `G₁/G₂` HT density baseline).  It is not used to prove Lemma 12.
-/

/-- The paper's `R_z` matrix, spelled out explicitly for the Lemma 12 branch. -/
noncomputable def paperRz (θ : ℝ) : Square 2 :=
  diag2 (Complex.exp (-Complex.I * (θ / 2))) (Complex.exp (Complex.I * (θ / 2)))

@[simp] theorem paperRz_eq_rz (θ : ℝ) : paperRz θ = rz θ := by
  rfl

/-- A conservative operator-norm tolerance sufficient to force `hsDistance < ε`. -/
noncomputable def rsOpTolerance (ε : ℝ) : ℝ :=
  min (1 / 4) (ε ^ 2 / 8)

theorem rsOpTolerance_pos {ε : ℝ} (hε : 0 < ε) :
    0 < rsOpTolerance ε := by
  unfold rsOpTolerance
  exact lt_min (by norm_num) (by positivity)

private lemma norm_entry_le_opNorm (A : Square 2) (i j : Fin 2) :
    ‖A i j‖ ≤ ‖A‖ := by
  let x : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 j (1 : ℂ)
  have hxnorm : ‖x‖ = 1 := by
    simp [x, PiLp.norm_single]
  have hvec : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) A x‖ ≤ ‖A‖ := by
    simpa [Matrix.cstar_norm_def, hxnorm] using
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) A).unit_le_opNorm x
        (by simp [hxnorm])
  have hcoord := PiLp.norm_apply_le
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) A x) i
  have hentry_eq : (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) A x) i = A i j := by
    simp [x]
  calc
    ‖A i j‖ = ‖(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) A x) i‖ := by
      rw [hentry_eq]
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) A x‖ := hcoord
    _ ≤ ‖A‖ := hvec

private lemma norm_trace_le_two_mul_opNorm (A : Square 2) :
    ‖Matrix.trace A‖ ≤ 2 * ‖A‖ := by
  calc
    ‖Matrix.trace A‖ = ‖∑ i : Fin 2, A i i‖ := by rfl
    _ ≤ ∑ i : Fin 2, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 2, ‖A‖ := by
      exact Finset.sum_le_sum (fun i _ => norm_entry_le_opNorm A i i)
    _ = 2 * ‖A‖ := by norm_num

private lemma opNorm_eq_one_of_mem_unitaryGroup {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖U‖ = 1 := by
  have hUU : U† * U = (1 : Square 2) := Matrix.mem_unitaryGroup_iff'.mp hU
  have hsq : ‖U‖ * ‖U‖ = 1 := by
    calc
      ‖U‖ * ‖U‖ = ‖U† * U‖ := by rw [Matrix.l2_opNorm_conjTranspose_mul_self]
      _ = ‖(1 : Square 2)‖ := by rw [hUU]
      _ = 1 := by simp
  have hnonneg : 0 ≤ ‖U‖ := norm_nonneg U
  nlinarith [sq_nonneg (‖U‖ - 1)]

private lemma trace_overlap_close_of_opDist {U V : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖Matrix.trace (U† * V) - 2‖ ≤ 2 * opDist U V := by
  have hUU : U† * U = (1 : Square 2) := Matrix.mem_unitaryGroup_iff'.mp hU
  have htrace_eq :
      Matrix.trace (U† * V) - 2 = Matrix.trace (U† * (V - U)) := by
    calc
      Matrix.trace (U† * V) - 2
          = Matrix.trace (U† * V) - Matrix.trace (1 : Square 2) := by
              norm_num [Matrix.trace_one]
      _ = Matrix.trace (U† * V) - Matrix.trace (U† * U) := by rw [hUU]
      _ = Matrix.trace (U† * (V - U)) := by
          simp [Matrix.mul_sub, Matrix.trace_sub]
  have hmul : ‖U† * (V - U)‖ ≤ ‖U - V‖ := by
    calc
      ‖U† * (V - U)‖ ≤ ‖U†‖ * ‖V - U‖ := Matrix.l2_opNorm_mul U† (V - U)
      _ = 1 * ‖V - U‖ := by
          rw [opNorm_eq_one_of_mem_unitaryGroup (TwoControl.conjTranspose_mem_unitaryGroup hU)]
      _ = 1 * ‖U - V‖ := by rw [norm_sub_rev]
      _ = ‖U - V‖ := by ring
  calc
    ‖Matrix.trace (U† * V) - 2‖ = ‖Matrix.trace (U† * (V - U))‖ := by
      rw [htrace_eq]
    _ ≤ 2 * ‖U† * (V - U)‖ := norm_trace_le_two_mul_opNorm _
    _ ≤ 2 * opDist U V := by
      unfold opDist
      nlinarith

theorem hsDistance_lt_of_opDist_small
    {U V : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (_hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    {ε : ℝ}
    (hε : 0 < ε)
    (hDist : opDist U V ≤ rsOpTolerance ε) :
    hsDistance U V < ε := by
  let d : ℝ := opDist U V
  let z : ℂ := Matrix.trace (U† * V)
  have hd_nonneg : 0 ≤ d := by
    dsimp [d, opDist]
    exact norm_nonneg (U - V)
  have hd_quarter : d ≤ 1 / 4 := by
    exact hDist.trans (min_le_left _ _)
  have hd_eps : d ≤ ε ^ 2 / 8 := by
    exact hDist.trans (min_le_right _ _)
  have hclose : ‖z - 2‖ ≤ 2 * d := by
    simpa [z, d] using trace_overlap_close_of_opDist (U := U) (V := V) hU
  have hz_lower : 2 - 2 * d ≤ ‖z‖ := by
    have htri : (2 : ℝ) ≤ ‖z‖ + ‖z - 2‖ := by
      calc
        (2 : ℝ) = ‖(2 : ℂ)‖ := by norm_num
        _ = ‖z - (z - 2)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖z - 2‖ := norm_sub_le z (z - 2)
    nlinarith
  have hbase_nonneg : 0 ≤ 2 - 2 * d := by
    nlinarith
  have hsquare_lower : (2 - 2 * d) ^ 2 ≤ ‖z‖ ^ 2 := by
    exact (sq_le_sq₀ hbase_nonneg (norm_nonneg z)).2 hz_lower
  have hrad :
      1 - ‖z‖ ^ 2 / 4 ≤ ε ^ 2 / 4 := by
    have hmain : 1 - ‖z‖ ^ 2 / 4 ≤ 2 * d - d ^ 2 := by
      nlinarith
    have hnonneg_sq : 0 ≤ d ^ 2 := sq_nonneg d
    nlinarith
  have hsqrt_le : hsDistance U V ≤ ε / 2 := by
    unfold hsDistance
    change Real.sqrt (1 - ‖z‖ ^ 2 / ((2 : ℝ) ^ 2)) ≤ ε / 2
    have hsqrt_bound :
        Real.sqrt (1 - ‖z‖ ^ 2 / ((2 : ℝ) ^ 2)) ≤ Real.sqrt (ε ^ 2 / 4) := by
      apply Real.sqrt_le_sqrt
      norm_num
      simpa using hrad
    have hsqrt_eps : Real.sqrt (ε ^ 2 / 4) = ε / 2 := by
      have hrewrite : ε ^ 2 / 4 = (ε / 2) ^ 2 := by ring
      rw [hrewrite, Real.sqrt_sq_eq_abs, abs_of_nonneg]
      positivity
    exact hsqrt_bound.trans_eq hsqrt_eps
  nlinarith

end RossSelinger
end TwoControl

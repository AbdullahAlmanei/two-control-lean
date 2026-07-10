import TwoControl.Clifford.Lemma12.Common.HTCircuit
import TwoControl.Clifford.Universal.Distance
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace TwoControl
namespace Clifford
namespace Lemma12

open Universal
open Matrix

/-!
# Generic axis-rotation infrastructure for the `{H,T}` density proof

Supports the `G₁/G₂` track of `reference/cliff/universal_new_gates.tex`
(July 2026): rotations `R(n,φ) = exp(iφ n·σ)` about unit axes, their
closed form, traces, the SU(2) `su2Pair` algebra, the generalized Euler
decomposition for two *orthogonal* axes (paper: N&C Ex. 4.11), density of
integer powers of an irrational rotation (paper: Hardy–Wright dense-orbit
lemma), and `{H,T}`-circuit integer powers of a gate word.

Nothing in this file mentions the concrete gates `G₁, G₂`; those live in
`G1G2/Generators.lean` and are connected to this infrastructure in
`G1G2/RzApprox.lean`.
-/

/-! ## Pauli matrices and axis rotations -/

/-- The Pauli X matrix σ_x. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![0, 1], ![1, 0]]

/-- The Pauli Y matrix σ_y. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![0, -Complex.I], ![Complex.I, 0]]

/-- The Pauli Z matrix σ_z. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![1, 0], ![0, -1]]

/-- The Pauli vector operator n · σ for a unit vector n = (n_x, n_y, n_z). -/
def pauliVec (n : EuclideanSpace ℝ (Fin 3)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (n 0 : ℂ) • pauliX + (n 1 : ℂ) • pauliY + (n 2 : ℂ) • pauliZ

/-- Rotation around axis n by angle φ, defined as exp(i φ n·σ). -/
noncomputable def axisRotation (n : EuclideanSpace ℝ (Fin 3)) (φ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp ((Complex.I * φ : ℂ) • pauliVec n)

/-! ### Basic Pauli properties -/

theorem pauliX_sq : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliY_sq : pauliY * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli X and Z anticommute. -/
theorem pauliX_pauliZ_anticommute : pauliX * pauliZ = -(pauliZ * pauliX) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli Y and Z anticommute. -/
theorem pauliY_pauliZ_anticommute : pauliY * pauliZ = -(pauliZ * pauliY) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli X and Y anticommute. -/
theorem pauliX_pauliY_anticommute : pauliX * pauliY = -(pauliY * pauliX) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_two]

/-- For a unit vector n, (n·σ)² = I. This follows from the Pauli algebra. -/
theorem pauliVec_sq_eq_one (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) :
    pauliVec n * pauliVec n = 1 := by
  -- Extract the norm condition
  have hnorm : (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 + (n 2 : ℝ) ^ 2 = 1 := by
    have h2 : ‖n‖ ^ 2 = 1 := by rw [hn]; ring
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three] at h2
    simp only [Real.norm_eq_abs, sq_abs] at h2
    exact h2
  -- Direct computation by cases
  ext i j
  fin_cases i <;> fin_cases j
  · -- i = 0, j = 0
    unfold pauliVec
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
    have hIsq : Complex.I * Complex.I = -1 := by rw [← sq]; exact Complex.I_sq
    calc ↑(n.ofLp 2) * ↑(n.ofLp 2) + (↑(n.ofLp 0) + -(↑(n.ofLp 1) * Complex.I)) * (↑(n.ofLp 0) + ↑(n.ofLp 1) * Complex.I)
        = ↑(n.ofLp 2) * ↑(n.ofLp 2) + (↑(n.ofLp 0) * ↑(n.ofLp 0) + ↑(n.ofLp 0) * (↑(n.ofLp 1) * Complex.I) +
          -(↑(n.ofLp 1) * Complex.I) * ↑(n.ofLp 0) + -(↑(n.ofLp 1) * Complex.I) * (↑(n.ofLp 1) * Complex.I)) := by ring
      _ = ↑(n.ofLp 2) * ↑(n.ofLp 2) + ↑(n.ofLp 0) * ↑(n.ofLp 0) + (↑(n.ofLp 1) * ↑(n.ofLp 1)) * (-(Complex.I * Complex.I)) := by ring
      _ = ↑(n.ofLp 2) * ↑(n.ofLp 2) + ↑(n.ofLp 0) * ↑(n.ofLp 0) + (↑(n.ofLp 1) * ↑(n.ofLp 1)) * (-(-1 : ℂ)) := by rw [hIsq]
      _ = ↑(n.ofLp 2) * ↑(n.ofLp 2) + ↑(n.ofLp 0) * ↑(n.ofLp 0) + ↑(n.ofLp 1) * ↑(n.ofLp 1) := by ring
      _ = ↑(n.ofLp 2 ^ 2) + ↑(n.ofLp 0 ^ 2) + ↑(n.ofLp 1 ^ 2) := by simp [sq]
      _ = ↑(n.ofLp 0 ^ 2 + n.ofLp 1 ^ 2 + n.ofLp 2 ^ 2) := by push_cast; ring
      _ = ↑(1 : ℝ) := by rw [hnorm]
      _ = 1 := by norm_num
  · -- i = 0, j = 1
    unfold pauliVec
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · -- i = 1, j = 0
    unfold pauliVec
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · -- i = 1, j = 1
    unfold pauliVec
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
    have hIsq : Complex.I * Complex.I = -1 := by rw [← sq]; exact Complex.I_sq
    calc (↑(n.ofLp 0) + ↑(n.ofLp 1) * Complex.I) * (↑(n.ofLp 0) + -(↑(n.ofLp 1) * Complex.I)) + ↑(n.ofLp 2) * ↑(n.ofLp 2)
        = (↑(n.ofLp 0) * ↑(n.ofLp 0) + ↑(n.ofLp 0) * (-(↑(n.ofLp 1) * Complex.I)) +
          (↑(n.ofLp 1) * Complex.I) * ↑(n.ofLp 0) + (↑(n.ofLp 1) * Complex.I) * (-(↑(n.ofLp 1) * Complex.I))) + ↑(n.ofLp 2) * ↑(n.ofLp 2) := by ring
      _ = ↑(n.ofLp 0) * ↑(n.ofLp 0) + (↑(n.ofLp 1) * ↑(n.ofLp 1)) * (-(Complex.I * Complex.I)) + ↑(n.ofLp 2) * ↑(n.ofLp 2) := by ring
      _ = ↑(n.ofLp 0) * ↑(n.ofLp 0) + (↑(n.ofLp 1) * ↑(n.ofLp 1)) * (-(-1 : ℂ)) + ↑(n.ofLp 2) * ↑(n.ofLp 2) := by rw [hIsq]
      _ = ↑(n.ofLp 0) * ↑(n.ofLp 0) + ↑(n.ofLp 1) * ↑(n.ofLp 1) + ↑(n.ofLp 2) * ↑(n.ofLp 2) := by ring
      _ = ↑(n.ofLp 0 ^ 2) + ↑(n.ofLp 1 ^ 2) + ↑(n.ofLp 2 ^ 2) := by simp [sq]
      _ = ↑(n.ofLp 0 ^ 2 + n.ofLp 1 ^ 2 + n.ofLp 2 ^ 2) := by push_cast; ring
      _ = ↑(1 : ℝ) := by rw [hnorm]
      _ = 1 := by norm_num

/-! ### Axis rotation closed form -/

private lemma expSeries_even_sq_eq_one {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A * A = 1) (φ : ℝ) (n : ℕ) :
    NormedSpace.expSeries ℂ (Matrix (Fin 2) (Fin 2) ℂ) (2 * n)
        (fun _ => (Complex.I * φ : ℂ) • A) =
      (((-1 : ℂ) ^ n * (φ : ℂ) ^ (2 * n) / ((2 * n).factorial : ℂ)) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [NormedSpace.expSeries_apply_eq]
  have hAeven : A ^ (2 * n) = 1 := by
    rw [pow_mul]
    have hA2 : A ^ 2 = 1 := by simpa [pow_two] using hA
    rw [hA2]
    simp
  rw [smul_pow, hAeven, mul_pow]
  rw [show Complex.I ^ (2 * n) = (-1 : ℂ) ^ n by rw [pow_mul, Complex.I_sq]]
  rw [smul_smul]
  congr 1
  ring_nf

private lemma expSeries_odd_sq_eq_one {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A * A = 1) (φ : ℝ) (n : ℕ) :
    NormedSpace.expSeries ℂ (Matrix (Fin 2) (Fin 2) ℂ) (2 * n + 1)
        (fun _ => (Complex.I * φ : ℂ) • A) =
      ((Complex.I *
          ((-1 : ℂ) ^ n * (φ : ℂ) ^ (2 * n + 1) /
            ((2 * n + 1).factorial : ℂ))) • A) := by
  rw [NormedSpace.expSeries_apply_eq]
  have hAodd : A ^ (2 * n + 1) = A := by
    rw [pow_succ, pow_mul]
    have hA2 : A ^ 2 = 1 := by simpa [pow_two] using hA
    rw [hA2]
    simp
  rw [smul_pow, hAodd, mul_pow]
  have hIpow : Complex.I ^ (2 * n + 1) = Complex.I * (-1 : ℂ) ^ n := by
    rw [pow_succ, pow_mul, Complex.I_sq]
    ring
  rw [hIpow]
  rw [smul_smul]
  congr 1
  ring_nf

/-- If a `2 × 2` complex matrix squares to `1`, then exponentiating an imaginary
scalar multiple has the usual cosine/sine closed form. -/
theorem exp_of_sq_eq_one
    {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A * A = 1)
    (φ : ℝ) :
    NormedSpace.exp ((Complex.I * φ : ℂ) • A) =
      (Real.cos φ : ℂ) • 1 + (Complex.I * Real.sin φ : ℂ) • A := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  simp_rw [← NormedSpace.expSeries_apply_eq]
  refine HasSum.tsum_eq ?_
  refine HasSum.even_add_odd ?_ ?_
  · have hcC :
        HasSum
          (fun n : ℕ =>
            (((-1 : ℝ) ^ n * φ ^ (2 * n) / ((2 * n).factorial : ℝ) : ℝ) : ℂ))
          (Real.cos φ : ℂ) := by
        simpa [Function.comp_def] using
          (Complex.ofRealCLM.hasSum (Real.hasSum_cos φ))
    have hcM := hcC.smul_const (1 : Matrix (Fin 2) (Fin 2) ℂ)
    convert hcM using 1
    ext n
    rw [expSeries_even_sq_eq_one hA]
    norm_num
  · have hsC :
        HasSum
          (fun n : ℕ =>
            (((-1 : ℝ) ^ n * φ ^ (2 * n + 1) /
              ((2 * n + 1).factorial : ℝ) : ℝ) : ℂ))
          (Real.sin φ : ℂ) := by
        simpa [Function.comp_def] using
          (Complex.ofRealCLM.hasSum (Real.hasSum_sin φ))
    have hsI :
        HasSum
          (fun n : ℕ =>
            Complex.I *
              (((-1 : ℝ) ^ n * φ ^ (2 * n + 1) /
                ((2 * n + 1).factorial : ℝ) : ℝ) : ℂ))
          (Complex.I * (Real.sin φ : ℂ)) := by
        exact HasSum.mul_left Complex.I hsC
    have hsM := hsI.smul_const A
    convert hsM using 1
    ext n
    rw [expSeries_odd_sq_eq_one hA]
    norm_num

/-- The closed form of axis rotation: R(n,φ) = cos(φ)I + i·sin(φ)·(n·σ). -/
theorem axisRotation_closed_form (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) (φ : ℝ) :
    axisRotation n φ = (Real.cos φ : ℂ) • 1 + (Complex.I * Real.sin φ : ℂ) • pauliVec n := by
  unfold axisRotation
  exact exp_of_sq_eq_one (pauliVec_sq_eq_one n hn) φ

theorem axisRotation_mem_unitaryGroup (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) (φ : ℝ) :
    axisRotation n φ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hnorm : (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 + (n 2 : ℝ) ^ 2 = 1 := by
    have h2 : ‖n‖ ^ 2 = 1 := by rw [hn]; ring
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three] at h2
    simp only [Real.norm_eq_abs, sq_abs] at h2
    exact h2
  have hnormC : ((n 0 : ℂ) ^ 2 + (n 1 : ℂ) ^ 2 + (n 2 : ℂ) ^ 2) = 1 := by
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hnorm
    norm_num at hc ⊢
    simpa using hc
  have htrig : Complex.cos (↑φ : ℂ) ^ 2 + Complex.sin (↑φ : ℂ) ^ 2 = 1 :=
    Complex.cos_sq_add_sin_sq (↑φ : ℂ)
  have hcos_star : (starRingEnd ℂ) (Complex.cos (↑φ : ℂ)) = Complex.cos (↑φ : ℂ) := by
    rw [← Complex.cos_conj]
    simp
  have hsin_star : (starRingEnd ℂ) (Complex.sin (↑φ : ℂ)) = Complex.sin (↑φ : ℂ) := by
    rw [← Complex.sin_conj]
    simp
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 by ring, Complex.I_sq]
    norm_num
  rw [Matrix.mem_unitaryGroup_iff']
  rw [axisRotation_closed_form n hn φ]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [pauliVec, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
      hcos_star, hsin_star]
  all_goals ring_nf
  all_goals try rw [Complex.I_sq, hI4]
  all_goals ring_nf
  · linear_combination htrig + Complex.sin (↑φ : ℂ) ^ 2 * hnormC
  · linear_combination htrig + Complex.sin (↑φ : ℂ) ^ 2 * hnormC

/-! ## Rational angles give roots of unity -/

/-- If `c` is rational, then `exp(i 2πc)` is a root of unity. -/
lemma rational_angle_is_rootOfUnity
    (c : ℝ) (hc : ∃ q : ℚ, (q : ℝ) = c) :
    ∃ n : ℕ, 0 < n ∧
      (Complex.exp (Complex.I * (2 * Real.pi * c))) ^ n = 1 := by
  obtain ⟨q, hq⟩ := hc
  refine ⟨q.den, q.den_pos, ?_⟩
  have h := (Complex.isPrimitiveRoot_exp_rat q).pow_eq_one
  convert h using 2
  rw [← hq]
  push_cast
  ring_nf

/-- The trace of a complex phase written as `z + z⁻¹`. -/
lemma exp_I_trace (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ =
      (2 * Real.cos θ : ℂ) := by
  rw [← Complex.exp_neg]
  have hneg : -((θ : ℂ) * Complex.I) = (((-θ : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hneg]
  rw [Complex.exp_mul_I (θ : ℂ), Complex.exp_mul_I ((-θ : ℝ) : ℂ)]
  simp [Complex.ofReal_cos]
  ring
/-! ## HT circuit realization -/

theorem HTCircuit_eval_append (left right : HTCircuit) :
    HTCircuit.eval (left ++ right) = HTCircuit.eval left * HTCircuit.eval right := by
  simpa [HTCircuit.eval] using oneQubitHTCircuitMatrix_append left right

/-- Circuit consisting of `n` copies of the `T` gate. -/
def tPowCircuit (n : ℕ) : HTCircuit :=
  List.replicate n .t

theorem eval_tPowCircuit (n : ℕ) :
    HTCircuit.eval (tPowCircuit n) = phaseT ^ n := by
  induction n with
  | zero =>
      simp [tPowCircuit]
  | succ n ih =>
      change HTCircuit.eval (.t :: tPowCircuit n) = phaseT ^ (n + 1)
      rw [HTCircuit.eval_cons, ih]
      simp [OneQubitHTPrimitive.eval, pow_succ']

lemma phaseT_pow_eight :
    phaseT ^ 8 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseT, diag2, Matrix.diagonal_pow]
  rw [← Complex.exp_nat_mul]
  change Complex.exp ((8 : ℂ) * (Complex.I * (↑Real.pi / 4))) = 1
  have harg : (8 : ℂ) * (Complex.I * (↑Real.pi / 4)) =
      (1 : ℤ) * (2 * ↑Real.pi * Complex.I) := by
    norm_num
    ring
  rw [harg, Complex.exp_int_mul_two_pi_mul_I]

lemma hadamard2_sq_eq_one :
    hadamard2 * hadamard2 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hhalf :
      ((↑(Real.sqrt 2) : ℂ)⁻¹) * ((↑(Real.sqrt 2) : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    have hsqrt_ne : (↑(Real.sqrt 2) : ℂ) ≠ 0 := by
      exact_mod_cast (show (Real.sqrt 2 : ℝ) ≠ 0 by positivity)
    have hsq_real : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hsq : ((↑(Real.sqrt 2) : ℂ)) ^ 2 = (2 : ℂ) := by
      exact_mod_cast hsq_real
    field_simp [pow_two, hsqrt_ne]
    simpa using hsq.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamard2, Matrix.mul_apply, Fin.sum_univ_two, hhalf]

/-! ### Integer powers of gate words -/

/-- The inverse word for one HT primitive, using `H⁻¹ = H` and `T⁻¹ = T^7`
(paper: `G₁⁻¹ ∼ T⁷HT⁷HT⁷`). -/
def primitiveInvCircuit : OneQubitHTPrimitive → HTCircuit
  | .h => [.h]
  | .t => tPowCircuit 7

theorem primitiveInvCircuit_eval (gate : OneQubitHTPrimitive) :
    HTCircuit.eval (primitiveInvCircuit gate) = (OneQubitHTPrimitive.eval gate)⁻¹ := by
  cases gate
  · simpa [primitiveInvCircuit, HTCircuit.eval, oneQubitHTCircuitMatrix,
      OneQubitHTPrimitive.eval] using
      (Matrix.inv_eq_right_inv hadamard2_sq_eq_one).symm
  · have ht_inv : phaseT⁻¹ = phaseT ^ 7 := by
      exact Matrix.inv_eq_right_inv (by
        rw [← pow_succ']
        simpa using phaseT_pow_eight)
    simpa [primitiveInvCircuit, eval_tPowCircuit, OneQubitHTPrimitive.eval] using ht_inv.symm

/-- Reverse a circuit and replace each gate by its HT inverse word. -/
def circuitInverse : HTCircuit → HTCircuit
  | [] => []
  | gate :: gates => circuitInverse gates ++ primitiveInvCircuit gate

theorem circuitInverse_eval (gates : HTCircuit) :
    HTCircuit.eval (circuitInverse gates) = (HTCircuit.eval gates)⁻¹ := by
  induction gates with
  | nil =>
      simp [circuitInverse]
  | cons gate gates ih =>
      rw [circuitInverse, HTCircuit_eval_append, ih, primitiveInvCircuit_eval]
      simp [HTCircuit.eval_cons, Matrix.mul_inv_rev]

/-- Repeat a circuit `n` times. -/
def circuitPower (C : HTCircuit) : ℕ → HTCircuit
  | 0 => []
  | n + 1 => C ++ circuitPower C n

theorem circuitPower_eval (C : HTCircuit) (n : ℕ) :
    HTCircuit.eval (circuitPower C n) = (HTCircuit.eval C) ^ n := by
  induction n with
  | zero =>
      simp [circuitPower]
  | succ n ih =>
      change HTCircuit.eval (C ++ circuitPower C n) = (HTCircuit.eval C) ^ (n + 1)
      rw [HTCircuit_eval_append, ih]
      simp [pow_succ']

/-- Integer power of a matrix using zpow. -/
noncomputable def zpowMatrix (U : Matrix (Fin 2) (Fin 2) ℂ) (n : ℤ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if n ≥ 0 then U ^ n.natAbs else (U⁻¹) ^ n.natAbs

/-- Integer power of a gate word: repeat the word, or repeat its inverse word. -/
def zpowCircuit (C : HTCircuit) (k : ℤ) : HTCircuit :=
  if k ≥ 0 then circuitPower C k.natAbs
  else circuitPower (circuitInverse C) k.natAbs

theorem eval_zpowCircuit (C : HTCircuit) (k : ℤ) :
    HTCircuit.eval (zpowCircuit C k) = zpowMatrix (HTCircuit.eval C) k := by
  by_cases hk : k ≥ 0
  · simp [zpowCircuit, zpowMatrix, hk, circuitPower_eval]
  · simp [zpowCircuit, zpowMatrix, hk, circuitPower_eval, circuitInverse_eval]

/-! ## Density of irrational rotations -/

open scoped Matrix.Norms.Operator in
private theorem axisRotation_zero (n : EuclideanSpace ℝ (Fin 3)) :
    axisRotation n 0 = 1 := by
  unfold axisRotation
  simp

open scoped Matrix.Norms.Operator in
private theorem axisRotation_add (n : EuclideanSpace ℝ (Fin 3)) (φ ψ : ℝ) :
    axisRotation n (φ + ψ) = axisRotation n φ * axisRotation n ψ := by
  unfold axisRotation
  rw [← Matrix.exp_add_of_commute]
  · congr 1
    ext i j
    simp [Matrix.add_apply]
    ring
  · exact ((Commute.refl (pauliVec n)).smul_left (Complex.I * (φ : ℂ))).smul_right
      (Complex.I * (ψ : ℂ))

private theorem axisRotation_inv (n : EuclideanSpace ℝ (Fin 3)) (φ : ℝ) :
    (axisRotation n φ)⁻¹ = axisRotation n (-φ) := by
  apply Matrix.inv_eq_left_inv
  rw [← axisRotation_add]
  simpa using axisRotation_zero n

private theorem axisRotation_nat_pow (n : EuclideanSpace ℝ (Fin 3)) (φ : ℝ) (k : ℕ) :
    (axisRotation n φ) ^ k = axisRotation n ((k : ℝ) * φ) := by
  induction k with
  | zero =>
      simp [axisRotation_zero]
  | succ k ih =>
      rw [pow_succ', ih, ← axisRotation_add]
      congr 1
      norm_num
      ring

private theorem zpowMatrix_axisRotation
    (n : EuclideanSpace ℝ (Fin 3)) (φ : ℝ) (k : ℤ) :
    zpowMatrix (axisRotation n φ) k = axisRotation n ((k : ℝ) * φ) := by
  by_cases hk : k ≥ 0
  · have hcast : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
      calc
        ((k.natAbs : ℕ) : ℝ) = (((k.natAbs : ℕ) : ℤ) : ℝ) := by norm_num
        _ = (k : ℝ) := by rw [Int.natAbs_of_nonneg hk]
    simp [zpowMatrix, hk, axisRotation_nat_pow, hcast]
  · have hcast : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
      calc
        ((k.natAbs : ℕ) : ℝ) = (((k.natAbs : ℕ) : ℤ) : ℝ) := by norm_num
        _ = ((-k : ℤ) : ℝ) := by
          rw [← Int.natAbs_neg k]
          rw [Int.natAbs_of_nonneg (by omega : 0 ≤ -k)]
        _ = -(k : ℝ) := by simp
    simp [zpowMatrix, hk, axisRotation_inv, axisRotation_nat_pow, hcast]

private theorem axisRotation_int_mul_two_pi
    (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) (k : ℤ) :
    axisRotation n ((k : ℝ) * (2 * Real.pi)) = 1 := by
  rw [axisRotation_closed_form n hn]
  have hcos : Real.cos ((k : ℝ) * (2 * Real.pi)) = 1 :=
    Real.cos_int_mul_two_pi k
  have hsin : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
    simpa using (Real.sin_add_int_mul_two_pi 0 k)
  simp [hcos, hsin]

private theorem axisRotation_add_int_mul_two_pi
    (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) (φ : ℝ) (k : ℤ) :
    axisRotation n (φ + (k : ℝ) * (2 * Real.pi)) = axisRotation n φ := by
  rw [axisRotation_add, axisRotation_int_mul_two_pi n hn k, Matrix.mul_one]

private theorem continuous_axisRotation_of_unit
    (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) :
    Continuous (fun φ : ℝ => axisRotation n φ) := by
  have hclosed :
      (fun φ : ℝ => axisRotation n φ) =
        fun φ : ℝ =>
          (Real.cos φ : ℂ) • 1 + (Complex.I * Real.sin φ : ℂ) • pauliVec n := by
    funext φ
    exact axisRotation_closed_form n hn φ
  rw [hclosed]
  have hcos : Continuous (fun φ : ℝ => (Real.cos φ : ℂ)) :=
    Complex.continuous_ofReal.comp Real.continuous_cos
  have hsin : Continuous (fun φ : ℝ => (Complex.I * Real.sin φ : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_sin)
  exact (hcos.smul continuous_const).add (hsin.smul continuous_const)

private theorem continuous_hsDistance_axisRotation
    (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) (α : ℝ) :
    Continuous (fun φ : ℝ => hsDistance (axisRotation n α) (axisRotation n φ)) := by
  unfold hsDistance
  have hrot : Continuous (fun φ : ℝ => axisRotation n φ) :=
    continuous_axisRotation_of_unit n hn
  have hmul :
      Continuous fun φ : ℝ => (axisRotation n α)† * axisRotation n φ :=
    continuous_const.matrix_mul hrot
  have htrace :
      Continuous fun φ : ℝ => Matrix.trace ((axisRotation n α)† * axisRotation n φ) := by
    unfold Matrix.trace
    exact continuous_finset_sum Finset.univ (fun i _hi => hmul.matrix_elem i i)
  exact (continuous_const.sub ((htrace.norm.pow 2).div_const ((2 : ℝ) ^ 2))).sqrt

theorem axisRotation_powers_dense
    (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1)
    (U : Matrix (Fin 2) (Fin 2) ℂ) (θ α : ℝ)
    (hU : U = axisRotation n θ)
    (hirr : Irrational (θ / (2 * Real.pi)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℤ, hsDistance (axisRotation n α) (zpowMatrix U k) < ε := by
  have hdense :
      Dense ((AddSubgroup.closure {θ, 2 * Real.pi} : AddSubgroup ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  have hcont :
      ContinuousAt (fun φ : ℝ => hsDistance (axisRotation n α) (axisRotation n φ)) α :=
    (continuous_hsDistance_axisRotation n hn α).continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont ε hε
  obtain ⟨x, hxmem, hxdist⟩ := hdense.exists_dist_lt α hδpos
  change x ∈ AddSubgroup.closure ({θ, 2 * Real.pi} : Set ℝ) at hxmem
  rw [AddSubgroup.mem_closure_pair] at hxmem
  obtain ⟨k, l, hx⟩ := hxmem
  refine ⟨k, ?_⟩
  have hzpow : zpowMatrix U k = axisRotation n ((k : ℝ) * θ) := by
    rw [hU]
    exact zpowMatrix_axisRotation n θ k
  have hperiod : axisRotation n x = axisRotation n ((k : ℝ) * θ) := by
    rw [← hx]
    simpa [zsmul_eq_mul] using axisRotation_add_int_mul_two_pi n hn ((k : ℝ) * θ) l
  have hself : hsDistance (axisRotation n α) (axisRotation n α) = 0 :=
    hsDistance_self (by norm_num : (0 : ℕ) < 2) (axisRotation n α)
      (axisRotation_mem_unitaryGroup n hn α)
  have hdist_val :
      dist (hsDistance (axisRotation n α) (axisRotation n x))
        (hsDistance (axisRotation n α) (axisRotation n α)) < ε := by
    exact hδ (by simpa [dist_comm] using hxdist)
  have hclose : hsDistance (axisRotation n α) (axisRotation n x) < ε := by
    rw [hself, Real.dist_eq] at hdist_val
    simpa using (abs_lt.mp hdist_val).2
  simpa [hzpow, hperiod] using hclose

/-! ## The standard z-axis -/

noncomputable def standardZAxis : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.equiv (Fin 3) ℝ |>.symm ![0, 0, 1]

lemma standardZAxis_unit : ‖standardZAxis‖ = 1 := by
  have hsq : ‖standardZAxis‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    have h2 : ![(0 : ℝ), 0, 1] (2 : Fin 3) = 1 := by
      rfl
    simp [standardZAxis, h2]
  nlinarith [norm_nonneg standardZAxis]

lemma rz_eq_axisRotation_standardZ (θ : ℝ) :
    rz θ = axisRotation standardZAxis (-(θ / 2)) := by
  rw [axisRotation_closed_form standardZAxis standardZAxis_unit]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [rz, diag2, standardZAxis, pauliVec, pauliX, pauliY, pauliZ]
    rw [show -(Complex.I * (↑θ / 2 : ℂ)) = ((-(θ / 2) : ℝ) : ℂ) * Complex.I by
      push_cast
      ring, Complex.exp_mul_I]
    simp
    ring
  · simp [rz, diag2, standardZAxis, pauliVec, pauliX, pauliY, pauliZ]
  · simp [rz, diag2, standardZAxis, pauliVec, pauliX, pauliY, pauliZ]
  · simp [rz, diag2, standardZAxis, pauliVec, pauliX, pauliY, pauliZ]
    rw [show Complex.I * (↑θ / 2 : ℂ) = (((θ / 2) : ℝ) : ℂ) * Complex.I by
      push_cast
      ring, Complex.exp_mul_I]
    simp
    ring

/-- pauliVec is linear in its argument. -/
private theorem pauliVec_add (v w : EuclideanSpace ℝ (Fin 3)) :
    pauliVec (v + w) = pauliVec v + pauliVec w := by
  unfold pauliVec
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.add_apply, Matrix.smul_apply,
          PiLp.add_apply] <;> ring

private theorem pauliVec_smul (c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    pauliVec (c • v) = (c : ℂ) • pauliVec v := by
  unfold pauliVec
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.add_apply, Matrix.smul_apply,
          PiLp.smul_apply] <;> ring

open scoped Matrix

/-- Explicit coordinate cross product for 3D Euclidean space. -/
private noncomputable def cross (u v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![
    u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0
  ]

/-! ### SU(2)/Quaternion algebra layer -/

/-- SU(2) element as scalar + vector: a·I + i·(u·σ) -/
def su2Pair (a : ℝ) (u : EuclideanSpace ℝ (Fin 3)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (a : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Complex.I • pauliVec u

/-- Entry [0,0] of su2Pair: a + i·u₂ -/
@[simp]
lemma su2Pair_00 (a : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    (su2Pair a u) 0 0 = a + Complex.I * (u 2 : ℂ) := by
  simp only [su2Pair, pauliVec, pauliX, pauliY, pauliZ, Matrix.add_apply, Matrix.smul_apply,
             Matrix.one_apply, ite_true, Fin.isValue]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]

/-- Entry [0,1] of su2Pair: i·u₀ + u₁ -/
@[simp]
lemma su2Pair_01 (a : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    (su2Pair a u) 0 1 = Complex.I * (u 0 : ℂ) + (u 1 : ℂ) := by
  unfold su2Pair pauliVec
  simp only [Matrix.add_apply, Matrix.smul_apply, pauliX, pauliY, pauliZ]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.one_apply]
  ring_nf
  simp [Complex.I_sq]

/-- Entry [1,0] of su2Pair: i·u₀ - u₁ -/
@[simp]
lemma su2Pair_10 (a : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    (su2Pair a u) 1 0 = Complex.I * (u 0 : ℂ) - (u 1 : ℂ) := by
  unfold su2Pair pauliVec
  simp only [Matrix.add_apply, Matrix.smul_apply, pauliX, pauliY, pauliZ]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.one_apply]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Entry [1,1] of su2Pair: a - i·u₂ -/
@[simp]
lemma su2Pair_11 (a : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    (su2Pair a u) 1 1 = a + Complex.I * (-(u 2 : ℂ)) := by
  simp only [su2Pair, pauliVec, pauliX, pauliY, pauliZ, Matrix.add_apply, Matrix.smul_apply,
             Matrix.one_apply, ite_true, Fin.isValue]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]

set_option maxHeartbeats 800000 in
/-- Fundamental Pauli product identity: (u·σ)(v·σ) = ⟨u,v⟩I + i(u×v)·σ -/
theorem pauliVec_mul_pauliVec (u v : EuclideanSpace ℝ (Fin 3)) :
    pauliVec u * pauliVec v =
      (inner ℝ u v : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Complex.I • pauliVec (cross u v) := by
  ext i j
  fin_cases i <;> fin_cases j
  · -- Case i=0, j=0
    simp only [Matrix.mul_apply, pauliVec, pauliX, pauliY, pauliZ,
               Matrix.add_apply, Matrix.smul_apply,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.one_apply, Fin.isValue, cross, inner, PiLp.inner_apply]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    -- Simplify sum and RCLike.re
    simp only [Fin.sum_univ_three, Complex.ofReal_sum,
               starRingEnd_apply, star_trivial, Function.comp_apply,
               Fin.succ_zero_eq_one, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.head_cons]
    ring_nf
    simp [Complex.I_sq]
    ring
  · -- Case i=0, j=1
    simp only [Matrix.mul_apply, pauliVec, pauliX, pauliY, pauliZ,
               Matrix.add_apply, Matrix.smul_apply,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.one_apply, Fin.isValue, cross, inner, PiLp.inner_apply]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring_nf
    simp [Complex.I_sq]
    ring
  · -- Case i=1, j=0
    simp only [Matrix.mul_apply, pauliVec, pauliX, pauliY, pauliZ,
               Matrix.add_apply, Matrix.smul_apply,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.one_apply, Fin.isValue, cross, inner, PiLp.inner_apply]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring_nf
    simp [Complex.I_sq]
    ring
  · -- Case i=1, j=1
    simp only [Matrix.mul_apply, pauliVec, pauliX, pauliY, pauliZ,
               Matrix.add_apply, Matrix.smul_apply,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.one_apply, Fin.isValue, cross, inner, PiLp.inner_apply]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    simp only [Fin.sum_univ_three, Complex.ofReal_sum,
               starRingEnd_apply, star_trivial, Function.comp_apply,
               Fin.succ_zero_eq_one, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.head_cons]
    ring_nf
    simp [Complex.I_sq]
    ring

set_option maxHeartbeats 800000 in
/-- Multiplication law for su2Pair -/
theorem su2Pair_mul (a b : ℝ) (u v : EuclideanSpace ℝ (Fin 3)) :
    su2Pair a u * su2Pair b v =
      su2Pair (a * b - inner ℝ u v) (a • v + b • u - cross u v) := by
  ext i j
  fin_cases i <;> fin_cases j
  · -- Case i=0, j=0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, su2Pair, pauliVec, pauliX, pauliY, pauliZ,
               Matrix.add_apply, Matrix.smul_apply,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.one_apply, Fin.isValue, cross, inner, PiLp.inner_apply, Pi.smul_apply]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    simp only [Fin.sum_univ_three, Complex.ofReal_sum,
               starRingEnd_apply, star_trivial, Function.comp_apply,
               Fin.succ_zero_eq_one, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.head_cons]
    ring_nf
    simp [Complex.I_sq]
    ring
  · -- Case i=0, j=1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, su2Pair, pauliVec, pauliX, pauliY, pauliZ,
               Matrix.add_apply, Matrix.smul_apply,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.one_apply, Fin.isValue, cross, inner, PiLp.inner_apply, Pi.smul_apply]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring_nf
    simp [Complex.I_sq]
    ring
  · -- Case i=1, j=0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, su2Pair, pauliVec, pauliX, pauliY, pauliZ,
               Matrix.add_apply, Matrix.smul_apply,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.one_apply, Fin.isValue, cross, inner, PiLp.inner_apply, Pi.smul_apply]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring_nf
    simp [Complex.I_sq]
    ring
  · -- Case i=1, j=1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, su2Pair, pauliVec, pauliX, pauliY, pauliZ,
               Matrix.add_apply, Matrix.smul_apply,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.one_apply, Fin.isValue, cross, inner, PiLp.inner_apply, Pi.smul_apply]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    simp only [Fin.sum_univ_three, Complex.ofReal_sum,
               starRingEnd_apply, star_trivial, Function.comp_apply,
               Fin.succ_zero_eq_one, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.head_cons]
    ring_nf
    simp [Complex.I_sq]
    ring

/-- Axis rotations are su2Pairs -/
theorem axisRotation_eq_su2Pair (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) (φ : ℝ) :
    axisRotation n φ = su2Pair (Real.cos φ) (Real.sin φ • n) := by
  rw [axisRotation_closed_form n hn φ]
  simp only [su2Pair, pauliVec_smul, smul_smul]

/-! ### Cross product helper lemmas -/

/-- The 0-th component of `cross`, definitionally. -/
private lemma cross_apply_zero (u v : EuclideanSpace ℝ (Fin 3)) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 := rfl

private lemma cross_apply_one (u v : EuclideanSpace ℝ (Fin 3)) :
    cross u v 1 = u 2 * v 0 - u 0 * v 2 := rfl

private lemma cross_apply_two (u v : EuclideanSpace ℝ (Fin 3)) :
    cross u v 2 = u 0 * v 1 - u 1 * v 0 := rfl

/-- The cross product is bilinear: linearity in the first argument (scalar). -/
private lemma cross_smul_left (c : ℝ) (u v : EuclideanSpace ℝ (Fin 3)) :
    cross (c • u) v = c • cross u v := by
  ext i
  fin_cases i
  · show (c * u 1) * v 2 - (c * u 2) * v 1 = c * (u 1 * v 2 - u 2 * v 1)
    ring
  · show (c * u 2) * v 0 - (c * u 0) * v 2 = c * (u 2 * v 0 - u 0 * v 2)
    ring
  · show (c * u 0) * v 1 - (c * u 1) * v 0 = c * (u 0 * v 1 - u 1 * v 0)
    ring

/-- Linearity of `cross` in the second argument (scalar). -/
private lemma cross_smul_right (c : ℝ) (u v : EuclideanSpace ℝ (Fin 3)) :
    cross u (c • v) = c • cross u v := by
  ext i
  fin_cases i
  · show u 1 * (c * v 2) - u 2 * (c * v 1) = c * (u 1 * v 2 - u 2 * v 1)
    ring
  · show u 2 * (c * v 0) - u 0 * (c * v 2) = c * (u 2 * v 0 - u 0 * v 2)
    ring
  · show u 0 * (c * v 1) - u 1 * (c * v 0) = c * (u 0 * v 1 - u 1 * v 0)
    ring

/-- Self-cross product is zero. -/
private lemma cross_self (v : EuclideanSpace ℝ (Fin 3)) : cross v v = 0 := by
  ext i
  fin_cases i
  · show v 1 * v 2 - v 2 * v 1 = 0; ring
  · show v 2 * v 0 - v 0 * v 2 = 0; ring
  · show v 0 * v 1 - v 1 * v 0 = 0; ring

/-- Additivity of `cross` in the first argument. -/
private lemma cross_add_left (u v w : EuclideanSpace ℝ (Fin 3)) :
    cross (u + v) w = cross u w + cross v w := by
  ext i
  fin_cases i
  · show (u 1 + v 1) * w 2 - (u 2 + v 2) * w 1 =
      (u 1 * w 2 - u 2 * w 1) + (v 1 * w 2 - v 2 * w 1)
    ring
  · show (u 2 + v 2) * w 0 - (u 0 + v 0) * w 2 =
      (u 2 * w 0 - u 0 * w 2) + (v 2 * w 0 - v 0 * w 2)
    ring
  · show (u 0 + v 0) * w 1 - (u 1 + v 1) * w 0 =
      (u 0 * w 1 - u 1 * w 0) + (v 0 * w 1 - v 1 * w 0)
    ring

/-- Additivity of `cross` in the second argument. -/
private lemma cross_add_right (u v w : EuclideanSpace ℝ (Fin 3)) :
    cross u (v + w) = cross u v + cross u w := by
  ext i
  fin_cases i
  · show u 1 * (v 2 + w 2) - u 2 * (v 1 + w 1) =
      (u 1 * v 2 - u 2 * v 1) + (u 1 * w 2 - u 2 * w 1)
    ring
  · show u 2 * (v 0 + w 0) - u 0 * (v 2 + w 2) =
      (u 2 * v 0 - u 0 * v 2) + (u 2 * w 0 - u 0 * w 2)
    ring
  · show u 0 * (v 1 + w 1) - u 1 * (v 0 + w 0) =
      (u 0 * v 1 - u 1 * v 0) + (u 0 * w 1 - u 1 * w 0)
    ring

/-- Subtractivity of `cross` in the second argument. -/
private lemma cross_sub_right (u v w : EuclideanSpace ℝ (Fin 3)) :
    cross u (v - w) = cross u v - cross u w := by
  ext i
  fin_cases i
  · show u 1 * (v 2 - w 2) - u 2 * (v 1 - w 1) =
      (u 1 * v 2 - u 2 * v 1) - (u 1 * w 2 - u 2 * w 1)
    ring
  · show u 2 * (v 0 - w 0) - u 0 * (v 2 - w 2) =
      (u 2 * v 0 - u 0 * v 2) - (u 2 * w 0 - u 0 * w 2)
    ring
  · show u 0 * (v 1 - w 1) - u 1 * (v 0 - w 0) =
      (u 0 * v 1 - u 1 * v 0) - (u 0 * w 1 - u 1 * w 0)
    ring

/-- Subtractivity of `cross` in the first argument. -/
private lemma cross_sub_left (u v w : EuclideanSpace ℝ (Fin 3)) :
    cross (u - v) w = cross u w - cross v w := by
  ext i
  fin_cases i
  · show (u 1 - v 1) * w 2 - (u 2 - v 2) * w 1 =
      (u 1 * w 2 - u 2 * w 1) - (v 1 * w 2 - v 2 * w 1)
    ring
  · show (u 2 - v 2) * w 0 - (u 0 - v 0) * w 2 =
      (u 2 * w 0 - u 0 * w 2) - (v 2 * w 0 - v 0 * w 2)
    ring
  · show (u 0 - v 0) * w 1 - (u 1 - v 1) * w 0 =
      (u 0 * w 1 - u 1 * w 0) - (v 0 * w 1 - v 1 * w 0)
    ring

/-- Anticommutativity of `cross`. -/
private lemma cross_anticomm (u v : EuclideanSpace ℝ (Fin 3)) :
    cross u v = -cross v u := by
  ext i
  fin_cases i
  · show u 1 * v 2 - u 2 * v 1 = -(v 1 * u 2 - v 2 * u 1); ring
  · show u 2 * v 0 - u 0 * v 2 = -(v 2 * u 0 - v 0 * u 2); ring
  · show u 0 * v 1 - u 1 * v 0 = -(v 0 * u 1 - v 1 * u 0); ring

/-- Inner product of `cross u v` with `u` is zero. -/
private lemma euler_cross_orthogonal_left
    (u v : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (cross u v) u = 0 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three]
  show (u 0) * (u 1 * v 2 - u 2 * v 1) + (u 1) * (u 2 * v 0 - u 0 * v 2) +
    (u 2) * (u 0 * v 1 - u 1 * v 0) = 0
  ring

/-- Inner product of `cross u v` with `v` is zero. -/
private lemma euler_cross_orthogonal_right
    (u v : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (cross u v) v = 0 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three]
  show (v 0) * (u 1 * v 2 - u 2 * v 1) + (v 1) * (u 2 * v 0 - u 0 * v 2) +
    (v 2) * (u 0 * v 1 - u 1 * v 0) = 0
  ring

/-- For unit `n₁` orthogonal to `n₂`, `cross (cross n₁ n₂) n₁ = n₂`. (BAC-CAB rule.) -/
private lemma cross_cross_first
    (n₁ n₂ : EuclideanSpace ℝ (Fin 3))
    (hn₁ : ‖n₁‖ = 1) (hortho : inner ℝ n₁ n₂ = 0) :
    cross (cross n₁ n₂) n₁ = n₂ := by
  have hnorm : n₁ 0 ^ 2 + n₁ 1 ^ 2 + n₁ 2 ^ 2 = 1 := by
    have h2 : ‖n₁‖ ^ 2 = 1 := by rw [hn₁]; ring
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three] at h2
    simp only [Real.norm_eq_abs, sq_abs] at h2
    exact h2
  have hinner : n₁ 0 * n₂ 0 + n₁ 1 * n₂ 1 + n₁ 2 * n₂ 2 = 0 := by
    have h := hortho
    simp only [PiLp.inner_apply, Fin.sum_univ_three] at h
    show n₁ 0 * n₂ 0 + n₁ 1 * n₂ 1 + n₁ 2 * n₂ 2 = 0
    have heq : n₂ 0 * n₁ 0 + n₂ 1 * n₁ 1 + n₂ 2 * n₁ 2 = 0 := h
    linarith
  ext i
  fin_cases i
  · -- cross (cross n₁ n₂) n₁ 0 = cross n₁ n₂ 1 * n₁ 2 - cross n₁ n₂ 2 * n₁ 1
    -- = (n₁ 2 * n₂ 0 - n₁ 0 * n₂ 2) * n₁ 2 - (n₁ 0 * n₂ 1 - n₁ 1 * n₂ 0) * n₁ 1
    show (n₁ 2 * n₂ 0 - n₁ 0 * n₂ 2) * n₁ 2 - (n₁ 0 * n₂ 1 - n₁ 1 * n₂ 0) * n₁ 1 = n₂ 0
    linear_combination n₂ 0 * hnorm - n₁ 0 * hinner
  · show (n₁ 0 * n₂ 1 - n₁ 1 * n₂ 0) * n₁ 0 - (n₁ 1 * n₂ 2 - n₁ 2 * n₂ 1) * n₁ 2 = n₂ 1
    linear_combination n₂ 1 * hnorm - n₁ 1 * hinner
  · show (n₁ 1 * n₂ 2 - n₁ 2 * n₂ 1) * n₁ 1 - (n₁ 2 * n₂ 0 - n₁ 0 * n₂ 2) * n₁ 0 = n₂ 2
    linear_combination n₂ 2 * hnorm - n₁ 2 * hinner

/-- Orthogonal-axes expansion: R(n₁,α)R(n₂,β)R(n₁,γ) equals the scalar/vector formula -/
theorem euler_product_expansion
    (n₁ n₂ : EuclideanSpace ℝ (Fin 3))
    (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1)
    (hortho : inner ℝ n₁ n₂ = 0)
    (α β γ : ℝ) :
    axisRotation n₁ α * axisRotation n₂ β * axisRotation n₁ γ =
      su2Pair
        (Real.cos β * Real.cos (γ + α))
        ((Real.cos β * Real.sin (γ + α)) • n₁
          + (Real.sin β * Real.cos (γ - α)) • n₂
          + (Real.sin β * Real.sin (γ - α)) • cross n₁ n₂) := by
  -- Step 1: Expand axisRotations to su2Pair form
  rw [axisRotation_eq_su2Pair n₁ hn₁ α, axisRotation_eq_su2Pair n₂ hn₂ β,
      axisRotation_eq_su2Pair n₁ hn₁ γ]
  -- Step 2: Apply su2Pair_mul twice
  rw [su2Pair_mul, su2Pair_mul]
  -- Key facts about n₁, n₂, and cross n₁ n₂
  have hn₁n₁ : inner ℝ n₁ n₁ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq]; rw [hn₁]; ring
  have hortho_rev : inner ℝ n₂ n₁ = (0 : ℝ) := by rw [real_inner_comm]; exact hortho
  have h_cross_n₁n₂_n₁ : inner ℝ (cross n₁ n₂) n₁ = (0 : ℝ) := euler_cross_orthogonal_left n₁ n₂
  have h_cross_cross : cross (cross n₁ n₂) n₁ = n₂ := cross_cross_first n₁ n₂ hn₁ hortho
  -- Cross of (sin α • n₁) and (sin β • n₂) = (sin α * sin β) • cross n₁ n₂
  have hcross1 : cross (Real.sin α • n₁) (Real.sin β • n₂)
      = (Real.sin α * Real.sin β) • cross n₁ n₂ := by
    rw [cross_smul_left, cross_smul_right, smul_smul]
  rw [hcross1]
  -- inner (sin α • n₁) (sin β • n₂) = 0
  rw [show inner ℝ (Real.sin α • n₁) (Real.sin β • n₂) = (0 : ℝ) by
    rw [real_inner_smul_left, real_inner_smul_right, hortho]; ring]
  -- Cross of the combined vector with (sin γ • n₁)
  have hcross2 : cross (Real.cos α • (Real.sin β • n₂) + Real.cos β • (Real.sin α • n₁) -
                       (Real.sin α * Real.sin β) • cross n₁ n₂) (Real.sin γ • n₁) =
      -((Real.cos α * Real.sin β * Real.sin γ) • cross n₁ n₂) -
      (Real.sin α * Real.sin β * Real.sin γ) • n₂ := by
    simp only [cross_sub_left, cross_add_left, cross_smul_left, cross_smul_right, cross_self,
               smul_zero, add_zero]
    rw [show cross n₂ n₁ = -cross n₁ n₂ from cross_anticomm n₂ n₁]
    rw [h_cross_cross]
    module
  rw [hcross2]
  -- Inner of combined vector with (sin γ • n₁)
  have hinner_combined :
      inner ℝ (Real.cos α • (Real.sin β • n₂) + Real.cos β • (Real.sin α • n₁) -
                (Real.sin α * Real.sin β) • cross n₁ n₂) (Real.sin γ • n₁)
      = Real.cos β * Real.sin α * Real.sin γ := by
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_right]
    rw [hortho_rev, hn₁n₁, h_cross_n₁n₂_n₁]
    ring
  rw [hinner_combined]
  -- Split into scalar and vector parts
  congr 1
  · -- Scalar: (cos α * cos β - sin α * sin β * 0) * cos γ - cos β * sin α * sin γ = cos β * cos(γ + α)
    rw [Real.cos_add]; ring
  · -- Vector part
    rw [Real.sin_add, Real.cos_sub, Real.sin_sub]
    module

/-- Cross product is orthogonal to the first input. -/
private theorem cross_orthogonal_left
    (v w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (cross v w) v = 0 :=
  euler_cross_orthogonal_left v w

/-- Cross product is orthogonal to the second input. -/
private theorem cross_orthogonal_right
    (v w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (cross v w) w = 0 :=
  euler_cross_orthogonal_right v w

/-- The cross product of orthogonal unit vectors has norm 1. (Lagrange identity.) -/
private theorem cross_orthogonal_unit_is_unit
    (v w : EuclideanSpace ℝ (Fin 3))
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (horth : inner ℝ v w = 0) :
    ‖cross v w‖ = 1 := by
  have hv_sq : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    have h2 : ‖v‖ ^ 2 = 1 := by rw [hv]; ring
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three] at h2
    simp only [Real.norm_eq_abs, sq_abs] at h2
    exact h2
  have hw_sq : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 = 1 := by
    have h2 : ‖w‖ ^ 2 = 1 := by rw [hw]; ring
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three] at h2
    simp only [Real.norm_eq_abs, sq_abs] at h2
    exact h2
  have h_inner : v 0 * w 0 + v 1 * w 1 + v 2 * w 2 = 0 := by
    have h := horth
    simp only [PiLp.inner_apply, Fin.sum_univ_three] at h
    show v 0 * w 0 + v 1 * w 1 + v 2 * w 2 = 0
    have : w 0 * v 0 + w 1 * v 1 + w 2 * v 2 = 0 := h
    linarith
  have hsq : ‖cross v w‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
    show (cross v w 0)^2 + (cross v w 1)^2 + (cross v w 2)^2 = 1
    show (v 1 * w 2 - v 2 * w 1)^2 + (v 2 * w 0 - v 0 * w 2)^2 + (v 0 * w 1 - v 1 * w 0)^2 = 1
    linear_combination (w 0^2 + w 1^2 + w 2^2) * hv_sq + hw_sq -
                       (v 0 * w 0 + v 1 * w 1 + v 2 * w 2) * h_inner
  -- ‖x‖² = 1 ∧ ‖x‖ ≥ 0 → ‖x‖ = 1
  have hnn : 0 ≤ ‖cross v w‖ := norm_nonneg _
  nlinarith [hsq, hnn]

/-! ### Distance accumulation for products -/

theorem hsDistance_triple_mul_le {A A' B B' C C' : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hA' : A' ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hB' : B' ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hC : C ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hC' : C' ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    hsDistance (A * B * C) (A' * B' * C') ≤
      hsDistance A A' + hsDistance B B' + hsDistance C C' := by
  have hAB : A * B ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ hA hB
  have hAB' : A' * B' ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ hA' hB'
  have hd1 := hsDistance_mul_le (by norm_num : (0 : ℕ) < 2) (A * B) C (A' * B') C' hAB hC hAB' hC'
  have hd2 := hsDistance_mul_le (by norm_num : (0 : ℕ) < 2) A B A' B' hA hB hA' hB'
  linarith

/-! ## Specialization to Rz rotations -/

/-- Generalized Euler decomposition for two *orthogonal* rotation axes
(paper Lemma `generalized-euler-decomposition`, N&C Ex. 4.11), stated for the
`R_z` targets that the universality proof consumes: every rotation about the
standard `z`-axis is an exact three-factor product `R(n₁,α)·R(n₂,β)·R(n₁,γ)`. -/
theorem standardZ_axisRotation_orthogonal_euler
    (n₁ n₂ : EuclideanSpace ℝ (Fin 3))
    (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1) (hortho : inner ℝ n₁ n₂ = 0)
    (φ : ℝ) :
    ∃ α β γ : ℝ,
      axisRotation standardZAxis φ =
        axisRotation n₁ α *
          axisRotation n₂ β *
            axisRotation n₁ γ := by
  let n₃ := cross n₁ n₂
  have hn₃ : ‖n₃‖ = 1 :=
    cross_orthogonal_unit_is_unit n₁ n₂
      hn₁ hn₂ hortho
  have hortho13 : inner ℝ n₁ n₃ = 0 := by
    rw [real_inner_comm]
    exact cross_orthogonal_left n₁ n₂
  have hortho23 : inner ℝ n₂ n₃ = 0 := by
    rw [real_inner_comm]
    exact cross_orthogonal_right n₁ n₂
  let frame : Fin 3 → EuclideanSpace ℝ (Fin 3) := fun i =>
    match i with
    | 0 => n₁
    | 1 => n₂
    | 2 => n₃
  have hframe_orthonormal : Orthonormal ℝ frame := by
    constructor
    · intro i
      fin_cases i <;> simp [frame, hn₃, hn₁, hn₂]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [frame]
      · contradiction
      · exact hortho
      · exact hortho13
      · rw [real_inner_comm]
        exact hortho
      · contradiction
      · exact hortho23
      · rw [real_inner_comm]
        exact hortho13
      · rw [real_inner_comm]
        exact hortho23
      · contradiction
  have hframe_span : ⊤ ≤ Submodule.span ℝ (Set.range frame) := by
    rw [top_le_iff]
    have hli : LinearIndependent ℝ frame :=
      Orthonormal.linearIndependent hframe_orthonormal
    have hcard :
        Fintype.card (Fin 3) =
          Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
      rw [finrank_euclideanSpace_fin]
      norm_num
    exact LinearIndependent.span_eq_top_of_card_eq_finrank' hli hcard
  let b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
    OrthonormalBasis.mk hframe_orthonormal hframe_span
  have hb : ∀ i, b i = frame i := by
    intro i
    simp [b, OrthonormalBasis.coe_mk]
  let c₁ := inner ℝ standardZAxis n₁
  let c₂ := inner ℝ standardZAxis n₂
  let c₃ := inner ℝ standardZAxis n₃
  have hdecomp :
      c₁ • n₁ + c₂ • n₂ + c₃ • n₃ = standardZAxis := by
    simpa [Fin.sum_univ_three, hb, frame, c₁, c₂, c₃, real_inner_comm] using
      b.sum_repr' standardZAxis
  have hcoeff_sq : c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2 = 1 := by
    have hparseval :
        ∑ i : Fin 3, inner ℝ standardZAxis (b i) * inner ℝ (b i) standardZAxis =
          inner ℝ standardZAxis standardZAxis :=
      OrthonormalBasis.sum_inner_mul_inner b standardZAxis standardZAxis
    calc
      c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2 =
          inner ℝ standardZAxis n₁ * inner ℝ n₁ standardZAxis +
            inner ℝ standardZAxis n₂ * inner ℝ n₂ standardZAxis +
              inner ℝ standardZAxis n₃ * inner ℝ n₃ standardZAxis := by
                simp [c₁, c₂, c₃, real_inner_comm, sq]
      _ = ∑ i : Fin 3,
          inner ℝ standardZAxis (b i) * inner ℝ (b i) standardZAxis := by
            rw [Fin.sum_univ_three]
            simp [hb, frame]
      _ = inner ℝ standardZAxis standardZAxis := hparseval
      _ = 1 := by
        rw [real_inner_self_eq_norm_sq, standardZAxis_unit]
        norm_num
  let qz : ℂ := (c₂ : ℂ) + (c₃ : ℂ) * Complex.I
  let r : ℝ := ‖qz‖
  let q := Complex.arg qz
  let pz : ℂ := (Real.cos φ : ℂ) + ((c₁ * Real.sin φ : ℝ) : ℂ) * Complex.I
  let m : ℝ := ‖pz‖
  let p := Complex.arg pz
  let βz : ℂ := (m : ℂ) + ((r * Real.sin φ : ℝ) : ℂ) * Complex.I
  let β := Complex.arg βz
  let α := (p - q) / 2
  let γ := (p + q) / 2
  have hr_sq : r ^ 2 = c₂ ^ 2 + c₃ ^ 2 := by
    change ‖qz‖ ^ 2 = c₂ ^ 2 + c₃ ^ 2
    simp only [qz]
    rw [Complex.norm_add_mul_I, Real.sq_sqrt]
    positivity
  have hm_sq : m ^ 2 = (Real.cos φ) ^ 2 + (c₁ * Real.sin φ) ^ 2 := by
    change ‖pz‖ ^ 2 = (Real.cos φ) ^ 2 + (c₁ * Real.sin φ) ^ 2
    simp only [pz]
    rw [Complex.norm_add_mul_I, Real.sq_sqrt]
    positivity
  have hβz_sq : ‖βz‖ ^ 2 = 1 := by
    simp only [βz]
    rw [Complex.norm_add_mul_I, Real.sq_sqrt]
    · rw [hm_sq]
      nlinarith [hr_sq, hcoeff_sq, Real.sin_sq_add_cos_sq φ]
    · positivity
  have hβz_norm : ‖βz‖ = 1 := by
    nlinarith [hβz_sq, norm_nonneg βz]
  have hq_cos : r * Real.cos q = c₂ := by
    simpa only [r, q, qz, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero] using Complex.norm_mul_cos_arg qz
  have hq_sin : r * Real.sin q = c₃ := by
    simpa only [r, q, qz, Complex.add_im, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero,
      zero_add, mul_one] using Complex.norm_mul_sin_arg qz
  have hp_cos : m * Real.cos p = Real.cos φ := by
    simpa only [m, p, pz, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero] using Complex.norm_mul_cos_arg pz
  have hp_sin : m * Real.sin p = c₁ * Real.sin φ := by
    simpa only [m, p, pz, Complex.add_im, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero,
      zero_add, mul_one] using Complex.norm_mul_sin_arg pz
  have hβ_cos : Real.cos β = m := by
    have h := Complex.norm_mul_cos_arg βz
    rw [hβz_norm, one_mul] at h
    simpa only [β, βz, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero] using h
  have hβ_sin : Real.sin β = r * Real.sin φ := by
    have h := Complex.norm_mul_sin_arg βz
    rw [hβz_norm, one_mul] at h
    simpa only [β, βz, Complex.add_im, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero,
      zero_add, mul_one] using h
  have hsum : γ + α = p := by
    simp [γ, α]
    ring
  have hdiff : γ - α = q := by
    simp [γ, α]
    ring
  have hscalar : Real.cos φ = Real.cos β * Real.cos (γ + α) := by
    rw [hsum, hβ_cos]
    exact hp_cos.symm
  have hcoef₁ :
      Real.cos β * Real.sin (γ + α) = c₁ * Real.sin φ := by
    rw [hsum, hβ_cos]
    exact hp_sin
  have hcoef₂ :
      Real.sin β * Real.cos (γ - α) = c₂ * Real.sin φ := by
    rw [hdiff, hβ_sin]
    calc
      (r * Real.sin φ) * Real.cos q = Real.sin φ * (r * Real.cos q) := by ring
      _ = c₂ * Real.sin φ := by rw [hq_cos]; ring
  have hcoef₃ :
      Real.sin β * Real.sin (γ - α) = c₃ * Real.sin φ := by
    rw [hdiff, hβ_sin]
    calc
      (r * Real.sin φ) * Real.sin q = Real.sin φ * (r * Real.sin q) := by ring
      _ = c₃ * Real.sin φ := by rw [hq_sin]; ring
  refine ⟨α, β, γ, ?_⟩
  rw [axisRotation_eq_su2Pair standardZAxis standardZAxis_unit φ]
  rw [euler_product_expansion n₁ n₂
    hn₁ hn₂ hortho α β γ]
  rw [hscalar]
  congr 1
  rw [hcoef₁, hcoef₂, hcoef₃]
  change Real.sin φ • standardZAxis =
    (c₁ * Real.sin φ) • n₁ +
      (c₂ * Real.sin φ) • n₂ +
        (c₃ * Real.sin φ) • n₃
  rw [← hdecomp]
  module

/-! ## Traces of rotations -/

theorem trace_su2Pair (a : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    Matrix.trace (su2Pair a u) = 2 * (a : ℂ) := by
  rw [Matrix.trace_fin_two, su2Pair_00, su2Pair_11]
  ring

/-- Paper Lemma `trace-of-g1-and-trace-of-g2-expressed-via-alphas`:
the trace of a rotation by `φ` is `2 cos φ`. -/
theorem trace_axisRotation (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) (φ : ℝ) :
    Matrix.trace (axisRotation n φ) = 2 * (Real.cos φ : ℂ) := by
  rw [axisRotation_eq_su2Pair n hn φ, trace_su2Pair]

/-- Trace of a product of two rotations, exposing the inner product of the axes. -/
theorem trace_axisRotation_mul
    (n₁ n₂ : EuclideanSpace ℝ (Fin 3)) (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1) (α β : ℝ) :
    Matrix.trace (axisRotation n₁ α * axisRotation n₂ β) =
      2 * ((Real.cos α * Real.cos β
        - Real.sin α * Real.sin β * inner ℝ n₁ n₂ : ℝ) : ℂ) := by
  rw [axisRotation_eq_su2Pair n₁ hn₁ α, axisRotation_eq_su2Pair n₂ hn₂ β, su2Pair_mul,
    trace_su2Pair]
  norm_cast
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-! ## Global phase invariance of the distance -/

/-- Multiplying the right argument by a global phase does not change the
Hilbert-Schmidt distance (paper Lemma `hs-distance-and-global-phase`). -/
theorem hsDistance_smul_right {z : ℂ} (hz : ‖z‖ = 1)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    hsDistance A (z • B) = hsDistance A B := by
  unfold hsDistance
  rw [Matrix.mul_smul, Matrix.trace_smul, norm_smul, hz, one_mul]

/-! ## Density for phased rotations

A gate word evaluates to `z • R(n,θ)` with `‖z‖ = 1` (the word realizes the
rotation only up to a global phase).  The density theorem transfers because
`hsDistance` ignores global phases. -/

private theorem smul_axisRotation_inv {z : ℂ} (hz : z ≠ 0)
    (n : EuclideanSpace ℝ (Fin 3)) (θ : ℝ) :
    (z • axisRotation n θ)⁻¹ = z⁻¹ • axisRotation n (-θ) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← axisRotation_add,
    inv_mul_cancel₀ hz, neg_add_cancel, axisRotation_zero, one_smul]

private theorem zpowMatrix_smul_axisRotation
    {z : ℂ} (hz : ‖z‖ = 1) (n : EuclideanSpace ℝ (Fin 3)) (θ : ℝ) (k : ℤ) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      zpowMatrix (z • axisRotation n θ) k = w • axisRotation n ((k : ℝ) * θ) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  by_cases hk : k ≥ 0
  · refine ⟨z ^ k.natAbs, by rw [norm_pow, hz, one_pow], ?_⟩
    have hcast : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
      calc
        ((k.natAbs : ℕ) : ℝ) = (((k.natAbs : ℕ) : ℤ) : ℝ) := by norm_num
        _ = (k : ℝ) := by rw [Int.natAbs_of_nonneg hk]
    rw [zpowMatrix, if_pos hk, smul_pow, axisRotation_nat_pow, hcast]
  · refine ⟨(z⁻¹) ^ k.natAbs, ?_, ?_⟩
    · rw [norm_pow, norm_inv, hz]
      norm_num
    · have hcast : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
        calc
          ((k.natAbs : ℕ) : ℝ) = (((k.natAbs : ℕ) : ℤ) : ℝ) := by norm_num
          _ = ((-k : ℤ) : ℝ) := by
            rw [← Int.natAbs_neg k]
            rw [Int.natAbs_of_nonneg (by omega : 0 ≤ -k)]
          _ = -(k : ℝ) := by simp
      rw [zpowMatrix, if_neg hk, smul_axisRotation_inv hz0, smul_pow,
        axisRotation_nat_pow, hcast]
      ring_nf

/-- Density of integer powers for a *phased* irrational rotation
(paper Lemma `approximate-g-to-the-m-when-is-a-rotation-by-an-irr-multiple-of-pi`,
up to the global phase carried by the circuit word). -/
theorem axisRotation_powers_dense_smul
    (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1)
    (U : Matrix (Fin 2) (Fin 2) ℂ) {z : ℂ} (hz : ‖z‖ = 1) (θ α : ℝ)
    (hU : U = z • axisRotation n θ)
    (hirr : Irrational (θ / (2 * Real.pi)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℤ, hsDistance (axisRotation n α) (zpowMatrix U k) < ε := by
  obtain ⟨k, hk⟩ := axisRotation_powers_dense n hn (axisRotation n θ) θ α rfl hirr hε
  obtain ⟨w, hw, hzpow⟩ := zpowMatrix_smul_axisRotation hz n θ k
  refine ⟨k, ?_⟩
  rw [hU, hzpow, hsDistance_smul_right hw]
  rwa [zpowMatrix_axisRotation n θ k] at hk

end Lemma12
end Clifford
end TwoControl

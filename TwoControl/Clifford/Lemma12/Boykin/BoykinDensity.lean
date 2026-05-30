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
# Boykin-style density of HT circuits in SU(2)

This file proves that {H,T} circuits are dense in SU(2) by following the
Boykin et al. proof from "On Universal and Fault-Tolerant Quantum Computing".

The strategy:
1. Define Pauli matrices and axis rotations R(n,φ) = exp(iφ n·σ)
2. Construct two specific HT circuits A and B that generate irrational rotations
   about orthogonal axes
3. Prove the rotation angles are irrational, making powers of A and B dense
4. Use SU(2) Euler decomposition to approximate any target unitary
5. Specialize to Rz rotations to close Lemma 12

## References
- Boykin, Mor, Pulver, Roychowdhury, Vatan: "On Universal and Fault-Tolerant
  Quantum Computing", arXiv:quant-ph/9906054
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

/-! ## Boykin's construction -/

/-! ### The rotation angle lambda -/

/-- Boykin's angle lambda where cos(lambda·π) = (1/2)(1 + 1/√2). -/
noncomputable def boykinLambda : ℝ :=
  Real.arccos ((1 / 2 : ℝ) * (1 + 1 / Real.sqrt 2)) / Real.pi

/-! ### Power gates for defining A and B -/

/-- Real power of σ_z: diag(1, exp(iπα)). -/
noncomputable def sigmaZPow (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![1, 0], ![0, Complex.exp (Complex.I * (Real.pi * α))]]

/-- Real power of σ_x via conjugation: H σ_z^α H. -/
noncomputable def sigmaXPow (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  hadamard2 * sigmaZPow α * hadamard2

/-- Real power of σ_y via Boykin's similarity transform. -/
noncomputable def sigmaYPow (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  sigmaZPow (1 / 2) * sigmaXPow α * sigmaZPow (-(1 / 2))

/-! ### Boykin's matrices A and B -/

/-- Boykin's matrix A = σ_z^(-1/4) σ_x^(1/4). -/
noncomputable def boykinA : Matrix (Fin 2) (Fin 2) ℂ :=
  sigmaZPow (-(1 / 4)) * sigmaXPow (1 / 4)

/-- Helper for Boykin's B: define H^α = σ_y^(1/4) σ_z^α σ_y^(-1/4).
This is the proper definition from Boykin, not an arbitrary real power. -/
noncomputable def HPow (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  sigmaYPow (1 / 4) * sigmaZPow α * sigmaYPow (-(1 / 4))

/-- Boykin's matrix B = H^(-1/2) A H^(1/2). -/
noncomputable def boykinB : Matrix (Fin 2) (Fin 2) ℂ :=
  HPow (-(1 / 2)) * boykinA * HPow (1 / 2)

/-! ### Boykin's axes -/

/-- The first Boykin axis (unnormalized): n₁ = (√2 cot(π/8))·((z-x)/√2) + y.
From the paper: cot(π/8) = √2 + 1, so this simplifies to (-(√2+1), 1, √2+1). -/
noncomputable def boykinN₁_unnorm : EuclideanSpace ℝ (Fin 3) :=
  let c := Real.sqrt 2 + 1  -- cot(π/8)
  EuclideanSpace.equiv (Fin 3) ℝ |>.symm ![- c, 1, c]

/-- The second Boykin axis (unnormalized): n₂ = (√2 cot(π/8))·y - ((z-x)/√2).
Simplifies to (1/√2, 2+√2, -1/√2). -/
noncomputable def boykinN₂_unnorm : EuclideanSpace ℝ (Fin 3) :=
  let s := 1 / Real.sqrt 2  -- 1/√2
  let c := Real.sqrt 2 + 1  -- cot(π/8)
  EuclideanSpace.equiv (Fin 3) ℝ |>.symm ![s, Real.sqrt 2 * c, -s]

/-- The first normalized Boykin axis. -/
noncomputable def boykinAxis₁ : EuclideanSpace ℝ (Fin 3) :=
  (‖boykinN₁_unnorm‖)⁻¹ • boykinN₁_unnorm

/-- The second normalized Boykin axis. -/
noncomputable def boykinAxis₂ : EuclideanSpace ℝ (Fin 3) :=
  (‖boykinN₂_unnorm‖)⁻¹ • boykinN₂_unnorm

private lemma boykinN₁_unnorm_ne_zero : boykinN₁_unnorm ≠ 0 := by
  intro h
  -- Extract the middle component which is 1
  have : (boykinN₁_unnorm : Fin 3 → ℝ) 1 = 0 := by
    rw [h]
    rfl
  -- But by definition it's 1
  unfold boykinN₁_unnorm at this
  simp at this

private lemma boykinN₂_unnorm_ne_zero : boykinN₂_unnorm ≠ 0 := by
  intro h
  -- Extract a component
  have : (boykinN₂_unnorm : Fin 3 → ℝ) 1 = 0 := by
    rw [h]
    rfl
  unfold boykinN₂_unnorm at this
  simp at this
  -- this says √2 + 1 = 0, which is false
  have : Real.sqrt 2 + 1 > 0 := by
    have : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    linarith
  linarith

theorem boykin_axes_unit :
    ‖boykinAxis₁‖ = 1 ∧ ‖boykinAxis₂‖ = 1 := by
  constructor
  · -- boykinAxis₁
    unfold boykinAxis₁
    rw [norm_smul, norm_inv, norm_norm]
    have h : ‖boykinN₁_unnorm‖ ≠ 0 := norm_ne_zero_iff.mpr boykinN₁_unnorm_ne_zero
    field_simp [h]
  · -- boykinAxis₂
    unfold boykinAxis₂
    rw [norm_smul, norm_inv, norm_norm]
    have h : ‖boykinN₂_unnorm‖ ≠ 0 := norm_ne_zero_iff.mpr boykinN₂_unnorm_ne_zero
    field_simp [h]

-- Helper lemma to evaluate coordinates
private lemma euclideanSpace_coord (a b c : ℝ) (i : Fin 3) :
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm ![a, b, c]).ofLp i = ![a, b, c] i := by
  rfl

theorem boykin_axes_orthogonal :
    inner ℝ boykinAxis₁ boykinAxis₂ = 0 := by
  unfold boykinAxis₁ boykinAxis₂
  rw [inner_smul_left, inner_smul_right]
  suffices inner ℝ boykinN₁_unnorm boykinN₂_unnorm = 0 by simp [this]
  -- Express inner product as sum using PiLp
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_three]
  -- Unfold to get explicit coordinate expressions
  unfold boykinN₁_unnorm boykinN₂_unnorm
  -- Use our helper to extract coordinates
  simp only [euclideanSpace_coord]
  -- Simplify inner on ℝ - unfolds to RCLike.re of star products
  simp only [inner]
  -- For ℝ, RCLike.re is identity and starRingEnd is identity
  simp only [RCLike.re_to_real, starRingEnd_apply, star_id_of_comm]
  -- Evaluate matrix notation at all indices (0, 1, and 2)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  -- For index 2 (the third component), evaluate explicitly
  have h2_left : ![-(Real.sqrt 2 + 1), 1, Real.sqrt 2 + 1] (2 : Fin 3) = Real.sqrt 2 + 1 := by
    rfl
  have h2_right : ![1 / Real.sqrt 2, Real.sqrt 2 * (Real.sqrt 2 + 1), -(1 / Real.sqrt 2)] (2 : Fin 3) =
      -(1 / Real.sqrt 2) := by
    rfl
  rw [h2_left, h2_right]
  -- Algebraic simplification
  have h_sqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h_ne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [h_ne]
  rw [h_sqrt2]
  ring

private lemma boykinLambda_cos_axis :
    Real.cos (boykinLambda * Real.pi) = (1 / 2 : ℝ) * (1 + 1 / Real.sqrt 2) := by
  unfold boykinLambda
  rw [div_mul_cancel₀ _ Real.pi_ne_zero]
  apply Real.cos_arccos
  · have hs_pos : 0 < Real.sqrt 2 := by positivity
    nlinarith [show 0 < (1 : ℝ) / Real.sqrt 2 by positivity]
  · have hs_ge_one : 1 ≤ Real.sqrt 2 := by
      have hs_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      have hs_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith
    have hs_pos : 0 < Real.sqrt 2 := by positivity
    have hinv_le : 1 / Real.sqrt 2 ≤ 1 := by
      rw [div_le_one hs_pos]
      exact hs_ge_one
    nlinarith

private lemma boykinLambda_sin_nonneg :
    0 ≤ Real.sin (boykinLambda * Real.pi) := by
  unfold boykinLambda
  rw [div_mul_cancel₀ _ Real.pi_ne_zero, Real.sin_arccos]
  positivity

private lemma boykinN₁_norm_sq :
    ‖boykinN₁_unnorm‖ ^ 2 = 7 + 4 * Real.sqrt 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [boykinN₁_unnorm]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

private lemma boykinN₂_norm_sq :
    ‖boykinN₂_unnorm‖ ^ 2 = 7 + 4 * Real.sqrt 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  have hs_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hc_nonneg : 0 ≤ Real.sqrt 2 + 1 := by positivity
  simp [boykinN₂_unnorm, abs_of_nonneg, hs_nonneg, hc_nonneg]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hne]
  nlinarith

private lemma boykinLambda_sin_div_norm₁ :
    Real.sin (boykinLambda * Real.pi) / ‖boykinN₁_unnorm‖ =
      (1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) := by
  have hnorm_pos : 0 < ‖boykinN₁_unnorm‖ := by
    have hsq := boykinN₁_norm_sq
    nlinarith [Real.sqrt_nonneg 2, norm_nonneg boykinN₁_unnorm]
  have hnorm_ne : ‖boykinN₁_unnorm‖ ≠ 0 := ne_of_gt hnorm_pos
  have hsinsq :
      Real.sin (boykinLambda * Real.pi) ^ 2 =
        1 - (((1 / 2 : ℝ) * (1 + 1 / Real.sqrt 2)) ^ 2) := by
    have htrig := Real.sin_sq_add_cos_sq (boykinLambda * Real.pi)
    rw [boykinLambda_cos_axis] at htrig
    linarith
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hsq :
      (Real.sin (boykinLambda * Real.pi) / ‖boykinN₁_unnorm‖) ^ 2 =
        ((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) ^ 2 := by
    field_simp [hnorm_ne, hsqrt_ne]
    rw [hsinsq, boykinN₁_norm_sq]
    field_simp [hsqrt_ne]
    nlinarith
  have hleft : 0 ≤ Real.sin (boykinLambda * Real.pi) / ‖boykinN₁_unnorm‖ :=
    div_nonneg boykinLambda_sin_nonneg (norm_nonneg _)
  have hright : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) := by
    have hs_ge_one : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hinv_le : 1 / Real.sqrt 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hs_ge_one
    nlinarith
  nlinarith

private lemma boykinLambda_sin_div_norm₂ :
    Real.sin (boykinLambda * Real.pi) / ‖boykinN₂_unnorm‖ =
      (1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) := by
  have hnorm_pos : 0 < ‖boykinN₂_unnorm‖ := by
    have hsq := boykinN₂_norm_sq
    nlinarith [Real.sqrt_nonneg 2, norm_nonneg boykinN₂_unnorm]
  have hnorm_ne : ‖boykinN₂_unnorm‖ ≠ 0 := ne_of_gt hnorm_pos
  have hsinsq :
      Real.sin (boykinLambda * Real.pi) ^ 2 =
        1 - (((1 / 2 : ℝ) * (1 + 1 / Real.sqrt 2)) ^ 2) := by
    have htrig := Real.sin_sq_add_cos_sq (boykinLambda * Real.pi)
    rw [boykinLambda_cos_axis] at htrig
    linarith
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hsq :
      (Real.sin (boykinLambda * Real.pi) / ‖boykinN₂_unnorm‖) ^ 2 =
        ((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) ^ 2 := by
    field_simp [hnorm_ne, hsqrt_ne]
    rw [hsinsq, boykinN₂_norm_sq]
    field_simp [hsqrt_ne]
    nlinarith
  have hleft : 0 ≤ Real.sin (boykinLambda * Real.pi) / ‖boykinN₂_unnorm‖ :=
    div_nonneg boykinLambda_sin_nonneg (norm_nonneg _)
  have hright : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) := by
    have hs_ge_one : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hinv_le : 1 / Real.sqrt 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hs_ge_one
    nlinarith
  nlinarith

private lemma exp_I_pi_div_four :
    Complex.exp (Complex.I * (Real.pi / 4)) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [show Complex.I * (Real.pi / 4) = ((Real.pi / 4 : ℂ) * Complex.I) by ring,
    Complex.exp_mul_I]
  have hcast : (Real.pi / 4 : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) := by norm_num
  have hcos : Complex.cos (Real.pi / 4 : ℂ) = (((Real.sqrt 2) / 2 : ℝ) : ℂ) := by
    rw [hcast, ← Complex.ofReal_cos, Real.cos_pi_div_four]
  have hsin : Complex.sin (Real.pi / 4 : ℂ) = (((Real.sqrt 2) / 2 : ℝ) : ℂ) := by
    rw [hcast, ← Complex.ofReal_sin, Real.sin_pi_div_four]
  rw [hcos, hsin]

private lemma exp_I_pi_mul_quarter :
    Complex.exp (Complex.I * (Real.pi : ℂ) * (1 / 4)) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [show Complex.I * (Real.pi : ℂ) * (1 / 4) =
      Complex.I * (Real.pi / 4) by norm_num; ring]
  exact exp_I_pi_div_four

private lemma exp_neg_I_pi_div_four :
    Complex.exp (Complex.I * (-(Real.pi / 4))) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) - ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [show Complex.I * (-(Real.pi / 4)) = ((-(Real.pi / 4) : ℂ) * Complex.I) by ring,
    Complex.exp_mul_I]
  have hcast : (-(Real.pi / 4) : ℂ) = ((-(Real.pi / 4) : ℝ) : ℂ) := by norm_num
  have hcos :
      Complex.cos (-(Real.pi / 4) : ℂ) = (((Real.sqrt 2) / 2 : ℝ) : ℂ) := by
    rw [hcast, ← Complex.ofReal_cos, Real.cos_neg, Real.cos_pi_div_four]
  have hsin :
      Complex.sin (-(Real.pi / 4) : ℂ) = -(((Real.sqrt 2) / 2 : ℝ) : ℂ) := by
    rw [hcast, ← Complex.ofReal_sin, Real.sin_neg, Real.sin_pi_div_four]
    norm_num
  rw [hcos, hsin]
  ring

private lemma exp_I_pi_mul_neg_quarter :
    Complex.exp (Complex.I * (Real.pi : ℂ) * (-1 / 4)) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) - ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [show Complex.I * (Real.pi : ℂ) * (-1 / 4) =
      Complex.I * (-(Real.pi / 4)) by norm_num; ring]
  exact exp_neg_I_pi_div_four

private lemma exp_I_pi_div_two :
    Complex.exp (Complex.I * (Real.pi / 2)) = Complex.I := by
  rw [show Complex.I * (Real.pi / 2) = ((Real.pi / 2 : ℂ) * Complex.I) by ring,
    Complex.exp_mul_I]
  simp

private lemma exp_I_pi_mul_half :
    Complex.exp (Complex.I * (Real.pi : ℂ) * (1 / 2)) = Complex.I := by
  rw [show Complex.I * (Real.pi : ℂ) * (1 / 2) =
      Complex.I * (Real.pi / 2) by norm_num; ring]
  exact exp_I_pi_div_two

private lemma exp_neg_I_pi_div_two :
    Complex.exp (Complex.I * (-(Real.pi / 2))) = -Complex.I := by
  rw [show Complex.I * (-(Real.pi / 2)) = - (Complex.I * (Real.pi / 2)) by ring,
    Complex.exp_neg, exp_I_pi_div_two]
  simp [Complex.inv_I]

private lemma exp_I_pi_mul_neg_half :
    Complex.exp (Complex.I * (Real.pi : ℂ) * (-1 / 2)) = -Complex.I := by
  rw [show Complex.I * (Real.pi : ℂ) * (-1 / 2) =
      Complex.I * (-(Real.pi / 2)) by norm_num; ring]
  exact exp_neg_I_pi_div_two

private lemma complexI_pow_five : Complex.I ^ 5 = Complex.I := by
  rw [pow_succ, Complex.I_pow_four]
  simp

private lemma complexI_pow_six : Complex.I ^ 6 = -1 := by
  rw [pow_succ, complexI_pow_five]
  rw [Complex.I_mul_I]

private lemma complexI_pow_seven : Complex.I ^ 7 = -Complex.I := by
  rw [pow_succ, complexI_pow_six]
  ring

private lemma boykinLambda_sin_mul_axis₁_zero :
    Real.sin (boykinLambda * Real.pi) * boykinAxis₁ 0 =
      -((1 / 2 : ℝ) * (1 / Real.sqrt 2)) := by
  have hcoef :
      Real.sin (boykinLambda * Real.pi) * ‖boykinN₁_unnorm‖⁻¹ =
        (1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) := by
    simpa [div_eq_mul_inv] using boykinLambda_sin_div_norm₁
  calc
    Real.sin (boykinLambda * Real.pi) * boykinAxis₁ 0 =
        (Real.sin (boykinLambda * Real.pi) * ‖boykinN₁_unnorm‖⁻¹) *
          boykinN₁_unnorm 0 := by
            simp [boykinAxis₁]
            ring
    _ = ((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) * boykinN₁_unnorm 0 := by
      rw [hcoef]
    _ = -((1 / 2 : ℝ) * (1 / Real.sqrt 2)) := by
      simp [boykinN₁_unnorm]
      have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hne : Real.sqrt 2 ≠ 0 := by positivity
      field_simp [hne]
      nlinarith

private lemma boykinLambda_sin_mul_axis₁_one :
    Real.sin (boykinLambda * Real.pi) * boykinAxis₁ 1 =
      (1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) := by
  have hcoef :
      Real.sin (boykinLambda * Real.pi) * ‖boykinN₁_unnorm‖⁻¹ =
        (1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) := by
    simpa [div_eq_mul_inv] using boykinLambda_sin_div_norm₁
  calc
    Real.sin (boykinLambda * Real.pi) * boykinAxis₁ 1 =
        (Real.sin (boykinLambda * Real.pi) * ‖boykinN₁_unnorm‖⁻¹) *
          boykinN₁_unnorm 1 := by
            simp [boykinAxis₁]
            ring
    _ = ((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) * boykinN₁_unnorm 1 := by
      rw [hcoef]
    _ = (1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) := by
      simp [boykinN₁_unnorm]

private lemma boykinLambda_sin_mul_axis₁_two :
    Real.sin (boykinLambda * Real.pi) * boykinAxis₁ 2 =
      (1 / 2 : ℝ) * (1 / Real.sqrt 2) := by
  have hcoef :
      Real.sin (boykinLambda * Real.pi) * ‖boykinN₁_unnorm‖⁻¹ =
        (1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) := by
    simpa [div_eq_mul_inv] using boykinLambda_sin_div_norm₁
  calc
    Real.sin (boykinLambda * Real.pi) * boykinAxis₁ 2 =
        (Real.sin (boykinLambda * Real.pi) * ‖boykinN₁_unnorm‖⁻¹) *
          boykinN₁_unnorm 2 := by
            simp [boykinAxis₁]
            ring
    _ = ((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) * boykinN₁_unnorm 2 := by
      rw [hcoef]
    _ = (1 / 2 : ℝ) * (1 / Real.sqrt 2) := by
      simp [boykinN₁_unnorm]
      have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hne : Real.sqrt 2 ≠ 0 := by positivity
      field_simp [hne]
      nlinarith

private lemma boykinLambda_sin_mul_axis₂_zero :
    Real.sin (boykinLambda * Real.pi) * boykinAxis₂ 0 =
      ((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) / Real.sqrt 2 := by
  have hcoef :
      Real.sin (boykinLambda * Real.pi) * ‖boykinN₂_unnorm‖⁻¹ =
        (1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) := by
    simpa [div_eq_mul_inv] using boykinLambda_sin_div_norm₂
  calc
    Real.sin (boykinLambda * Real.pi) * boykinAxis₂ 0 =
        (Real.sin (boykinLambda * Real.pi) * ‖boykinN₂_unnorm‖⁻¹) *
          boykinN₂_unnorm 0 := by
            simp [boykinAxis₂]
            ring
    _ = ((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) * boykinN₂_unnorm 0 := by
      rw [hcoef]
    _ = ((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) / Real.sqrt 2 := by
      simp [boykinN₂_unnorm]
      ring

private lemma boykinLambda_sin_mul_axis₂_one :
    Real.sin (boykinLambda * Real.pi) * boykinAxis₂ 1 = (1 / 2 : ℝ) := by
  have hcoef :
      Real.sin (boykinLambda * Real.pi) * ‖boykinN₂_unnorm‖⁻¹ =
        (1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) := by
    simpa [div_eq_mul_inv] using boykinLambda_sin_div_norm₂
  calc
    Real.sin (boykinLambda * Real.pi) * boykinAxis₂ 1 =
        (Real.sin (boykinLambda * Real.pi) * ‖boykinN₂_unnorm‖⁻¹) *
          boykinN₂_unnorm 1 := by
            simp [boykinAxis₂]
            ring
    _ = ((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) * boykinN₂_unnorm 1 := by
      rw [hcoef]
    _ = (1 / 2 : ℝ) := by
      simp [boykinN₂_unnorm]
      have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hne : Real.sqrt 2 ≠ 0 := by positivity
      field_simp [hne]
      nlinarith

private lemma boykinLambda_sin_mul_axis₂_two :
    Real.sin (boykinLambda * Real.pi) * boykinAxis₂ 2 =
      -(((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) / Real.sqrt 2) := by
  have hcoef :
      Real.sin (boykinLambda * Real.pi) * ‖boykinN₂_unnorm‖⁻¹ =
        (1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) := by
    simpa [div_eq_mul_inv] using boykinLambda_sin_div_norm₂
  calc
    Real.sin (boykinLambda * Real.pi) * boykinAxis₂ 2 =
        (Real.sin (boykinLambda * Real.pi) * ‖boykinN₂_unnorm‖⁻¹) *
          boykinN₂_unnorm 2 := by
            simp [boykinAxis₂]
            ring
    _ = ((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) * boykinN₂_unnorm 2 := by
      rw [hcoef]
    _ = -(((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) / Real.sqrt 2) := by
      simp [boykinN₂_unnorm]
      ring

private lemma complexSin_boykinLambda_mul_axis₁_zero :
    Complex.sin ((Real.pi : ℂ) * (boykinLambda : ℂ)) * (boykinAxis₁ 0 : ℂ) =
      ((-((1 / 2 : ℝ) * (1 / Real.sqrt 2)) : ℝ) : ℂ) := by
  rw [show (Real.pi : ℂ) * (boykinLambda : ℂ) =
      ((Real.pi * boykinLambda : ℝ) : ℂ) by push_cast; rfl]
  rw [← Complex.ofReal_sin]
  exact_mod_cast (by simpa [mul_comm] using boykinLambda_sin_mul_axis₁_zero)

private lemma complexSin_boykinLambda_mul_axis₁_one :
    Complex.sin ((Real.pi : ℂ) * (boykinLambda : ℂ)) * (boykinAxis₁ 1 : ℂ) =
      (((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) : ℝ) : ℂ) := by
  rw [show (Real.pi : ℂ) * (boykinLambda : ℂ) =
      ((Real.pi * boykinLambda : ℝ) : ℂ) by push_cast; rfl]
  rw [← Complex.ofReal_sin]
  exact_mod_cast (by simpa [mul_comm] using boykinLambda_sin_mul_axis₁_one)

private lemma complexSin_boykinLambda_mul_axis₁_two :
    Complex.sin ((Real.pi : ℂ) * (boykinLambda : ℂ)) * (boykinAxis₁ 2 : ℂ) =
      (((1 / 2 : ℝ) * (1 / Real.sqrt 2) : ℝ) : ℂ) := by
  rw [show (Real.pi : ℂ) * (boykinLambda : ℂ) =
      ((Real.pi * boykinLambda : ℝ) : ℂ) by push_cast; rfl]
  rw [← Complex.ofReal_sin]
  exact_mod_cast (by simpa [mul_comm] using boykinLambda_sin_mul_axis₁_two)

private lemma complexSin_boykinLambda_mul_axis₂_zero :
    Complex.sin ((Real.pi : ℂ) * (boykinLambda : ℂ)) * (boykinAxis₂ 0 : ℂ) =
      ((((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [show (Real.pi : ℂ) * (boykinLambda : ℂ) =
      ((Real.pi * boykinLambda : ℝ) : ℂ) by push_cast; rfl]
  rw [← Complex.ofReal_sin]
  exact_mod_cast (by simpa [mul_comm] using boykinLambda_sin_mul_axis₂_zero)

private lemma complexSin_boykinLambda_mul_axis₂_one :
    Complex.sin ((Real.pi : ℂ) * (boykinLambda : ℂ)) * (boykinAxis₂ 1 : ℂ) =
      ((1 / 2 : ℝ) : ℂ) := by
  rw [show (Real.pi : ℂ) * (boykinLambda : ℂ) =
      ((Real.pi * boykinLambda : ℝ) : ℂ) by push_cast; rfl]
  rw [← Complex.ofReal_sin]
  exact_mod_cast (by simpa [mul_comm] using boykinLambda_sin_mul_axis₂_one)

private lemma complexSin_boykinLambda_mul_axis₂_two :
    Complex.sin ((Real.pi : ℂ) * (boykinLambda : ℂ)) * (boykinAxis₂ 2 : ℂ) =
      ((-(((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) / Real.sqrt 2) : ℝ) : ℂ) := by
  rw [show (Real.pi : ℂ) * (boykinLambda : ℂ) =
      ((Real.pi * boykinLambda : ℝ) : ℂ) by push_cast; rfl]
  rw [← Complex.ofReal_sin]
  exact_mod_cast (by simpa [mul_comm] using boykinLambda_sin_mul_axis₂_two)

private lemma mul_complexSin_boykinLambda_axis₁_zero (z : ℂ) :
    z * Complex.sin ((Real.pi : ℂ) * (boykinLambda : ℂ)) * (boykinAxis₁ 0 : ℂ) =
      z * ((-((1 / 2 : ℝ) * (1 / Real.sqrt 2)) : ℝ) : ℂ) := by
  rw [mul_assoc, complexSin_boykinLambda_mul_axis₁_zero]

private lemma mul_complexSin_boykinLambda_axis₁_one (z : ℂ) :
    z * Complex.sin ((Real.pi : ℂ) * (boykinLambda : ℂ)) * (boykinAxis₁ 1 : ℂ) =
      z * (((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2) : ℝ) : ℂ) := by
  rw [mul_assoc, complexSin_boykinLambda_mul_axis₁_one]

private lemma mul_complexSin_boykinLambda_axis₁_two (z : ℂ) :
    z * Complex.sin ((Real.pi : ℂ) * (boykinLambda : ℂ)) * (boykinAxis₁ 2 : ℂ) =
      z * (((1 / 2 : ℝ) * (1 / Real.sqrt 2) : ℝ) : ℂ) := by
  rw [mul_assoc, complexSin_boykinLambda_mul_axis₁_two]

private lemma mul_complexSin_boykinLambda_axis₂_zero (z : ℂ) :
    z * Complex.sin ((Real.pi : ℂ) * (boykinLambda : ℂ)) * (boykinAxis₂ 0 : ℂ) =
      z * ((((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [mul_assoc, complexSin_boykinLambda_mul_axis₂_zero]

private lemma mul_complexSin_boykinLambda_axis₂_one (z : ℂ) :
    z * Complex.sin ((Real.pi : ℂ) * (boykinLambda : ℂ)) * (boykinAxis₂ 1 : ℂ) =
      z * ((1 / 2 : ℝ) : ℂ) := by
  rw [mul_assoc, complexSin_boykinLambda_mul_axis₂_one]

private lemma mul_complexSin_boykinLambda_axis₂_two (z : ℂ) :
    z * Complex.sin ((Real.pi : ℂ) * (boykinLambda : ℂ)) * (boykinAxis₂ 2 : ℂ) =
      z * ((-(((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) / Real.sqrt 2) : ℝ) : ℂ) := by
  rw [mul_assoc, complexSin_boykinLambda_mul_axis₂_two]

private lemma complexSin_boykinLambda_mul_axis₂_zero_commuted :
    Complex.sin ((boykinLambda : ℂ) * (Real.pi : ℂ)) * (boykinAxis₂ 0 : ℂ) =
      ((((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [mul_comm (boykinLambda : ℂ) (Real.pi : ℂ)]
  exact complexSin_boykinLambda_mul_axis₂_zero

private lemma complexSin_boykinLambda_mul_axis₂_one_commuted :
    Complex.sin ((boykinLambda : ℂ) * (Real.pi : ℂ)) * (boykinAxis₂ 1 : ℂ) =
      ((1 / 2 : ℝ) : ℂ) := by
  rw [mul_comm (boykinLambda : ℂ) (Real.pi : ℂ)]
  exact complexSin_boykinLambda_mul_axis₂_one

private lemma complexSin_boykinLambda_mul_axis₂_two_commuted :
    Complex.sin ((boykinLambda : ℂ) * (Real.pi : ℂ)) * (boykinAxis₂ 2 : ℂ) =
      ((-(((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) / Real.sqrt 2) : ℝ) : ℂ) := by
  rw [mul_comm (boykinLambda : ℂ) (Real.pi : ℂ)]
  exact complexSin_boykinLambda_mul_axis₂_two

private lemma mul_complexSin_boykinLambda_axis₂_zero_commuted (z : ℂ) :
    z * Complex.sin ((boykinLambda : ℂ) * (Real.pi : ℂ)) * (boykinAxis₂ 0 : ℂ) =
      z * ((((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [mul_assoc, complexSin_boykinLambda_mul_axis₂_zero_commuted]

private lemma mul_complexSin_boykinLambda_axis₂_one_commuted (z : ℂ) :
    z * Complex.sin ((boykinLambda : ℂ) * (Real.pi : ℂ)) * (boykinAxis₂ 1 : ℂ) =
      z * ((1 / 2 : ℝ) : ℂ) := by
  rw [mul_assoc, complexSin_boykinLambda_mul_axis₂_one_commuted]

private lemma mul_complexSin_boykinLambda_axis₂_two_commuted (z : ℂ) :
    z * Complex.sin ((boykinLambda : ℂ) * (Real.pi : ℂ)) * (boykinAxis₂ 2 : ℂ) =
      z * ((-(((1 / 2 : ℝ) * (1 - 1 / Real.sqrt 2)) / Real.sqrt 2) : ℝ) : ℂ) := by
  rw [mul_assoc, complexSin_boykinLambda_mul_axis₂_two_commuted]

theorem boykinA_is_axisRotation :
    boykinA = axisRotation boykinAxis₁ (boykinLambda * Real.pi) := by
  rw [axisRotation_closed_form boykinAxis₁ boykin_axes_unit.1]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [boykinA, sigmaZPow, sigmaXPow, hadamard2, pauliVec, pauliX, pauliY,
      pauliZ, Matrix.mul_apply, Fin.sum_univ_two, boykinLambda_cos_axis]
    ring_nf
    try rw [mul_complexSin_boykinLambda_axis₁_zero]
    try rw [mul_complexSin_boykinLambda_axis₁_one]
    try rw [mul_complexSin_boykinLambda_axis₁_two]
    try rw [exp_I_pi_mul_quarter]
    try rw [exp_I_pi_mul_neg_quarter]
    push_cast
    ring_nf
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (Real.sqrt 2 : ℝ) ≠ 0 by positivity)
    field_simp [hne]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    ring_nf at hs ⊢
    try rw [hs]
    try rw [hI]
    ring

private lemma boykinA_matrix :
    boykinA =
      Matrix.of ![
        ![1 / 2 + (Real.sqrt 2 : ℂ) * (1 + Complex.I) / 4,
          1 / 2 - (Real.sqrt 2 : ℂ) * (1 + Complex.I) / 4],
        ![(1 - Complex.I) * (-1 + (Real.sqrt 2 : ℂ) - Complex.I) / 4,
          (1 - Complex.I) * (1 + (Real.sqrt 2 : ℂ) + Complex.I) / 4]] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [boykinA, sigmaZPow, sigmaXPow, hadamard2, Matrix.mul_apply, Fin.sum_univ_two]
    ring_nf
    try rw [exp_I_pi_mul_quarter]
    try rw [exp_I_pi_mul_neg_quarter]
    push_cast
    ring_nf
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (Real.sqrt 2 : ℝ) ≠ 0 by positivity)
    field_simp [hne]
    have hs3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℂ) := by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 *
            (Real.sqrt 2 : ℂ) := by ring
        _ = 2 * (Real.sqrt 2 : ℂ) := by rw [hs]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    ring_nf at hs ⊢
    try rw [hs3]
    try rw [hs]
    try rw [hI]
    ring

private lemma HPow_half_matrix :
    HPow (1 / 2) =
      Matrix.of ![
        ![(1 - Complex.I) * ((Real.sqrt 2 : ℂ) + 2 * Complex.I) / 4,
          (Real.sqrt 2 : ℂ) * (1 - Complex.I) / 4],
        ![(Real.sqrt 2 : ℂ) * (1 - Complex.I) / 4,
          (1 - Complex.I) * (-(Real.sqrt 2 : ℂ) + 2 * Complex.I) / 4]] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [HPow, sigmaYPow, sigmaZPow, sigmaXPow, hadamard2, Matrix.mul_apply,
      Fin.sum_univ_two]
    ring_nf
    repeat' first
    | rw [exp_I_pi_mul_quarter]
    | rw [exp_I_pi_mul_neg_quarter]
    | rw [exp_I_pi_mul_half]
    | rw [exp_I_pi_mul_neg_half]
    push_cast
    ring_nf
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (Real.sqrt 2 : ℝ) ≠ 0 by positivity)
    field_simp [hne]
    have hs3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℂ) := by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 *
            (Real.sqrt 2 : ℂ) := by ring
        _ = 2 * (Real.sqrt 2 : ℂ) := by rw [hs]
    have hs4 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 := by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) ^ 2 := by
          ring
        _ = 4 := by rw [hs]; ring
    have hs5 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 5 = 4 * (Real.sqrt 2 : ℂ) := by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 5 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 *
            (Real.sqrt 2 : ℂ) := by ring
        _ = 4 * (Real.sqrt 2 : ℂ) := by rw [hs4]
    ring_nf at hs ⊢
    repeat' first
    | rw [hs5]
    | rw [hs4]
    | rw [hs3]
    | rw [hs]
    repeat' first
    | rw [complexI_pow_seven]
    | rw [complexI_pow_six]
    | rw [complexI_pow_five]
    | rw [Complex.I_pow_four]
    | rw [Complex.I_pow_three]
    | rw [Complex.I_sq]
    ring

private lemma HPow_neg_half_matrix :
    HPow (-(1 / 2)) =
      Matrix.of ![
        ![(1 - Complex.I) * (2 + (Real.sqrt 2 : ℂ) * Complex.I) / 4,
          (Real.sqrt 2 : ℂ) * Complex.I * (1 - Complex.I) / 4],
        ![(Real.sqrt 2 : ℂ) * Complex.I * (1 - Complex.I) / 4,
          (1 - Complex.I) * (2 - (Real.sqrt 2 : ℂ) * Complex.I) / 4]] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [HPow, sigmaYPow, sigmaZPow, sigmaXPow, hadamard2, Matrix.mul_apply,
      Fin.sum_univ_two]
    ring_nf
    repeat' first
    | rw [exp_I_pi_mul_quarter]
    | rw [exp_I_pi_mul_neg_quarter]
    | rw [exp_I_pi_mul_half]
    | rw [exp_I_pi_mul_neg_half]
    push_cast
    ring_nf
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (Real.sqrt 2 : ℝ) ≠ 0 by positivity)
    field_simp [hne]
    have hs3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℂ) := by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 *
            (Real.sqrt 2 : ℂ) := by ring
        _ = 2 * (Real.sqrt 2 : ℂ) := by rw [hs]
    have hs4 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 := by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) ^ 2 := by
          ring
        _ = 4 := by rw [hs]; ring
    have hs5 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 5 = 4 * (Real.sqrt 2 : ℂ) := by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 5 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 *
            (Real.sqrt 2 : ℂ) := by ring
        _ = 4 * (Real.sqrt 2 : ℂ) := by rw [hs4]
    ring_nf at hs ⊢
    repeat' first
    | rw [hs5]
    | rw [hs4]
    | rw [hs3]
    | rw [hs]
    repeat' first
    | rw [complexI_pow_seven]
    | rw [complexI_pow_six]
    | rw [complexI_pow_five]
    | rw [Complex.I_pow_four]
    | rw [Complex.I_pow_three]
    | rw [Complex.I_sq]
    ring

theorem boykinB_is_axisRotation :
    boykinB = axisRotation boykinAxis₂ (boykinLambda * Real.pi) := by
  rw [boykinB, HPow_neg_half_matrix, boykinA_matrix, HPow_half_matrix]
  rw [axisRotation_closed_form boykinAxis₂ boykin_axes_unit.2]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [pauliVec, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
      boykinLambda_cos_axis]
    ring_nf
    try rw [mul_complexSin_boykinLambda_axis₂_zero]
    try rw [mul_complexSin_boykinLambda_axis₂_one]
    try rw [mul_complexSin_boykinLambda_axis₂_two]
    try rw [complexSin_boykinLambda_mul_axis₂_zero_commuted]
    try rw [complexSin_boykinLambda_mul_axis₂_one_commuted]
    try rw [complexSin_boykinLambda_mul_axis₂_two_commuted]
    try rw [mul_complexSin_boykinLambda_axis₂_zero_commuted]
    try rw [mul_complexSin_boykinLambda_axis₂_one_commuted]
    try rw [mul_complexSin_boykinLambda_axis₂_two_commuted]
    push_cast
    ring_nf
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (Real.sqrt 2 : ℝ) ≠ 0 by positivity)
    field_simp [hne]
    have hs3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℂ) := by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 *
            (Real.sqrt 2 : ℂ) := by ring
        _ = 2 * (Real.sqrt 2 : ℂ) := by rw [hs]
    have hs4 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 := by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) ^ 2 := by
          ring
        _ = 4 := by rw [hs]; ring
    have hs5 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 5 = 4 * (Real.sqrt 2 : ℂ) := by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 5 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 *
            (Real.sqrt 2 : ℂ) := by ring
        _ = 4 * (Real.sqrt 2 : ℂ) := by rw [hs4]
    ring_nf at hs ⊢
    repeat' first
    | rw [hs5]
    | rw [hs4]
    | rw [hs3]
    | rw [hs]
    repeat' first
    | rw [complexI_pow_seven]
    | rw [complexI_pow_six]
    | rw [complexI_pow_five]
    | rw [Complex.I_pow_four]
    | rw [Complex.I_pow_three]
    | rw [Complex.I_sq]
    ring

/-! ## Irrationality of lambda (Boykin's argument) -/

/-- The elementary direction of Boykin's cyclotomic/rational theorem:
if `c` is rational, then `exp(i 2πc)` is a root of unity. -/
private lemma rational_angle_is_rootOfUnity
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

/-- Compatibility name for the direction of Boykin's appendix theorem used here. -/
private lemma cyclotomic_rational_theorem
    (c : ℝ) (hc : ∃ q : ℚ, (q : ℝ) = c) :
    ∃ n : ℕ, 0 < n ∧
      (Complex.exp (Complex.I * (2 * Real.pi * c))) ^ n = 1 :=
  rational_angle_is_rootOfUnity c hc

/-- The phase ζ = exp(i·2πλ) from Boykin's construction. -/
noncomputable def boykinZeta : ℂ :=
  Complex.exp (2 * Real.pi * boykinLambda * Complex.I)

/-- Boykin's polynomial: x^4 + x^3 + (1/4)x^2 + x + 1.
This is the polynomial that ζ satisfies, according to Boykin et al. -/
noncomputable def boykinPolynomial : Polynomial ℚ :=
  Polynomial.X ^ 4 + Polynomial.X ^ 3 + (1 / 4 : ℚ) • (Polynomial.X ^ 2) + Polynomial.X + 1

/-- The defining cosine identity for Boykin's angle. -/
private lemma boykinLambda_cos :
    Real.cos (boykinLambda * Real.pi) = (1 / 2 : ℝ) * (1 + 1 / Real.sqrt 2) := by
  unfold boykinLambda
  rw [div_mul_cancel₀ _ Real.pi_ne_zero]
  apply Real.cos_arccos
  · have hs_pos : 0 < Real.sqrt 2 := by positivity
    nlinarith [show 0 < (1 : ℝ) / Real.sqrt 2 by positivity]
  · have hs_ge_one : 1 ≤ Real.sqrt 2 := by
      have hs_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      have hs_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith
    have hs_pos : 0 < Real.sqrt 2 := by positivity
    have hinv_le : 1 / Real.sqrt 2 ≤ 1 := by
      rw [div_le_one hs_pos]
      exact hs_ge_one
    nlinarith

/-- The trace of a complex phase written as `z + z⁻¹`. -/
private lemma exp_I_trace (θ : ℝ) :
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

/-- Boykin's phase satisfies `ζ + ζ⁻¹ = √2 - 1/2`. -/
private lemma boykinZeta_trace :
    boykinZeta + boykinZeta⁻¹ = (Real.sqrt 2 - 1 / 2 : ℂ) := by
  have htrace := exp_I_trace (2 * (boykinLambda * Real.pi))
  have hz : boykinZeta = Complex.exp (((2 * (boykinLambda * Real.pi) : ℝ) : ℂ) * Complex.I) := by
    simp [boykinZeta]
    ring_nf
  rw [← hz] at htrace
  calc boykinZeta + boykinZeta⁻¹
      = (2 * Real.cos (2 * (boykinLambda * Real.pi)) : ℂ) := htrace
    _ = (Real.sqrt 2 - 1 / 2 : ℂ) := by
      have hreal : 2 * Real.cos (2 * (boykinLambda * Real.pi)) = Real.sqrt 2 - 1 / 2 := by
        rw [Real.cos_two_mul, boykinLambda_cos]
        have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        have hne : Real.sqrt 2 ≠ 0 := by positivity
        field_simp [hne]
        nlinarith [hs]
      have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
      simpa using hc

/-- Key lemma from Boykin: ζ = exp(i·2πλ) is a root of the polynomial
x^4 + x^3 + (1/4)x^2 + x + 1. -/
private lemma boykinZeta_satisfies_polynomial :
    Polynomial.aeval boykinZeta boykinPolynomial = 0 := by
  have hz : boykinZeta ≠ 0 := by
    simp [boykinZeta]
  have htrace : boykinZeta + boykinZeta⁻¹ = (Real.sqrt 2 - 1 / 2 : ℂ) :=
    boykinZeta_trace
  have hx : (Real.sqrt 2 - 1 / 2 : ℂ) ^ 2 + (Real.sqrt 2 - 1 / 2 : ℂ) = (7 / 4 : ℂ) := by
    have hreal : (Real.sqrt 2 - 1 / 2 : ℝ) ^ 2 + (Real.sqrt 2 - 1 / 2) = 7 / 4 := by
      have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith [hs]
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
    simpa using hc
  have hpoly : boykinZeta ^ 4 + boykinZeta ^ 3 + (1 / 4 : ℂ) * boykinZeta ^ 2 +
      boykinZeta + 1 = 0 := by
    rw [← htrace] at hx
    field_simp [hz] at hx ⊢
    ring_nf at hx ⊢
    linear_combination hx
  simpa [boykinPolynomial, Algebra.smul_def] using hpoly

/-- The rational number `7 / 4` is not an algebraic integer. -/
private lemma not_isIntegral_seven_div_four_complex : ¬ IsIntegral ℤ (7 / 4 : ℂ) := by
  intro h
  have hq : IsIntegral ℤ (7 / 4 : ℚ) := by
    refine (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).mp ?_
    simpa using h
  obtain ⟨z, hz⟩ :=
    IsIntegrallyClosed.algebraMap_eq_of_integral (R := ℤ) (K := ℚ) hq
  norm_num at hz
  have hz' : (4 : ℚ) * (z : ℚ) = 7 := by nlinarith
  have hzint : (4 : ℤ) * z = 7 := by exact_mod_cast hz'
  omega

/-- Dividing Boykin's polynomial by `z²` gives an equation for `z + z⁻¹`. -/
private lemma boykinPolynomial_trace_eq (z : ℂ) (hz : z ≠ 0)
    (h : Polynomial.aeval z boykinPolynomial = 0) :
    (z + z⁻¹) ^ 2 + (z + z⁻¹) = (7 / 4 : ℂ) := by
  have h' : z ^ 4 + z ^ 3 + (1 / 4 : ℂ) * z ^ 2 + z + 1 = 0 := by
    simpa [boykinPolynomial, Algebra.smul_def] using h
  field_simp [hz] at h' ⊢
  ring_nf at h' ⊢
  linear_combination h'

/-- Boykin's concrete contradiction: the phase `ζ = exp(i 2πλ)` is not a root of unity. -/
theorem boykin_zeta_not_rootOfUnity :
    ¬ ∃ n : ℕ, 0 < n ∧
      (Complex.exp (Complex.I * (2 * Real.pi * boykinLambda))) ^ n = 1 := by
  rintro ⟨n, hnpos, hroot⟩
  have hroot' : boykinZeta ^ n = 1 := by
    convert hroot using 2
    simp [boykinZeta]
    ring_nf
  have hz_ne : boykinZeta ≠ 0 := by
    simp [boykinZeta]
  have hz_int : IsIntegral ℤ boykinZeta := by
    exact IsIntegral.of_pow hnpos (by rw [hroot']; exact isIntegral_one)
  have hz_inv_eq : boykinZeta⁻¹ = boykinZeta ^ (n - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hnpos, hroot']
  let x : ℂ := boykinZeta + boykinZeta⁻¹
  have hx_int : IsIntegral ℤ x := by
    dsimp [x]
    rw [hz_inv_eq]
    exact hz_int.add (hz_int.pow (n - 1))
  have hx_eq : x ^ 2 + x = (7 / 4 : ℂ) := by
    simpa [x] using
      boykinPolynomial_trace_eq boykinZeta hz_ne boykinZeta_satisfies_polynomial
  apply not_isIntegral_seven_div_four_complex
  rw [← hx_eq]
  exact (hx_int.pow 2).add hx_int

/-- Boykin's irrationality argument: λ is irrational because exp(i·2πλ)
satisfies a non-cyclotomic polynomial (having coefficient 1/4 ∉ ℤ). -/
theorem boykinLambda_irrational : Irrational boykinLambda := by
  intro ⟨q, hq⟩
  exact boykin_zeta_not_rootOfUnity
    (cyclotomic_rational_theorem boykinLambda ⟨q, hq⟩)

/-! ## HT circuit realization -/

private theorem HTCircuit_eval_append (left right : HTCircuit) :
    HTCircuit.eval (left ++ right) = HTCircuit.eval left * HTCircuit.eval right := by
  simpa [HTCircuit.eval] using oneQubitHTCircuitMatrix_append left right

/-- Circuit consisting of `n` copies of the `T` gate. -/
def tPowCircuit (n : ℕ) : HTCircuit :=
  List.replicate n .t

private theorem eval_tPowCircuit (n : ℕ) :
    HTCircuit.eval (tPowCircuit n) = phaseT ^ n := by
  induction n with
  | zero =>
      simp [tPowCircuit]
  | succ n ih =>
      change HTCircuit.eval (.t :: tPowCircuit n) = phaseT ^ (n + 1)
      rw [HTCircuit.eval_cons, ih]
      simp [OneQubitHTPrimitive.eval, pow_succ']

private lemma phaseT_pow_one : phaseT = sigmaZPow (1 / 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phaseT, sigmaZPow, diag2]
  ring_nf

private lemma phaseT_pow_two : phaseT ^ 2 = sigmaZPow (1 / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseT, sigmaZPow, diag2, Matrix.diagonal_pow]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring_nf

private lemma phaseT_pow_six : phaseT ^ 6 = sigmaZPow (-(1 / 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseT, sigmaZPow, diag2, Matrix.diagonal_pow]
  rw [← Complex.exp_nat_mul]
  change Complex.exp ((6 : ℂ) * (Complex.I * (↑Real.pi / 4))) =
    Complex.exp (-(Complex.I * (↑Real.pi * 2⁻¹)))
  have harg : (6 : ℂ) * (Complex.I * (↑Real.pi / 4)) =
      -(Complex.I * (↑Real.pi * 2⁻¹)) + (1 : ℤ) * (2 * ↑Real.pi * Complex.I) := by
    norm_num
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp

private lemma phaseT_pow_seven : phaseT ^ 7 = sigmaZPow (-(1 / 4)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseT, sigmaZPow, diag2, Matrix.diagonal_pow]
  rw [← Complex.exp_nat_mul]
  change Complex.exp ((7 : ℂ) * (Complex.I * (↑Real.pi / 4))) =
    Complex.exp (-(Complex.I * (↑Real.pi * 4⁻¹)))
  have harg : (7 : ℂ) * (Complex.I * (↑Real.pi / 4)) =
      -(Complex.I * (↑Real.pi * 4⁻¹)) + (1 : ℤ) * (2 * ↑Real.pi * Complex.I) := by
    norm_num
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp

private lemma phaseT_pow_eight :
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

private lemma hadamard2_sq_eq_one :
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

def sigmaZPow_quarter_circuit : HTCircuit := tPowCircuit 1
def sigmaZPow_neg_quarter_circuit : HTCircuit := tPowCircuit 7
def sigmaZPow_half_circuit : HTCircuit := tPowCircuit 2
def sigmaZPow_neg_half_circuit : HTCircuit := tPowCircuit 6

private theorem eval_sigmaZPow_quarter_circuit :
    HTCircuit.eval sigmaZPow_quarter_circuit = sigmaZPow (1 / 4) := by
  simp [sigmaZPow_quarter_circuit, eval_tPowCircuit, phaseT_pow_one]

private theorem eval_sigmaZPow_neg_quarter_circuit :
    HTCircuit.eval sigmaZPow_neg_quarter_circuit = sigmaZPow (-(1 / 4)) := by
  simp [sigmaZPow_neg_quarter_circuit, eval_tPowCircuit, phaseT_pow_seven]

private theorem eval_sigmaZPow_half_circuit :
    HTCircuit.eval sigmaZPow_half_circuit = sigmaZPow (1 / 2) := by
  simp [sigmaZPow_half_circuit, eval_tPowCircuit, phaseT_pow_two]

private theorem eval_sigmaZPow_neg_half_circuit :
    HTCircuit.eval sigmaZPow_neg_half_circuit = sigmaZPow (-(1 / 2)) := by
  simp [sigmaZPow_neg_half_circuit, eval_tPowCircuit, phaseT_pow_six]

def sigmaXPow_quarter_circuit : HTCircuit :=
  [.h] ++ sigmaZPow_quarter_circuit ++ [.h]

def sigmaXPow_neg_quarter_circuit : HTCircuit :=
  [.h] ++ sigmaZPow_neg_quarter_circuit ++ [.h]

def sigmaXPow_half_circuit : HTCircuit :=
  [.h] ++ sigmaZPow_half_circuit ++ [.h]

def sigmaXPow_neg_half_circuit : HTCircuit :=
  [.h] ++ sigmaZPow_neg_half_circuit ++ [.h]

private theorem eval_sigmaXPow_quarter_circuit :
    HTCircuit.eval sigmaXPow_quarter_circuit = sigmaXPow (1 / 4) := by
  rw [sigmaXPow_quarter_circuit, HTCircuit_eval_append, HTCircuit_eval_append,
    eval_sigmaZPow_quarter_circuit]
  simp [HTCircuit.eval, oneQubitHTCircuitMatrix, OneQubitHTPrimitive.eval, sigmaXPow, mul_assoc]

private theorem eval_sigmaXPow_neg_quarter_circuit :
    HTCircuit.eval sigmaXPow_neg_quarter_circuit = sigmaXPow (-(1 / 4)) := by
  rw [sigmaXPow_neg_quarter_circuit, HTCircuit_eval_append, HTCircuit_eval_append,
    eval_sigmaZPow_neg_quarter_circuit]
  simp [HTCircuit.eval, oneQubitHTCircuitMatrix, OneQubitHTPrimitive.eval, sigmaXPow, mul_assoc]

private theorem eval_sigmaXPow_half_circuit :
    HTCircuit.eval sigmaXPow_half_circuit = sigmaXPow (1 / 2) := by
  rw [sigmaXPow_half_circuit, HTCircuit_eval_append, HTCircuit_eval_append,
    eval_sigmaZPow_half_circuit]
  simp [HTCircuit.eval, oneQubitHTCircuitMatrix, OneQubitHTPrimitive.eval, sigmaXPow, mul_assoc]

private theorem eval_sigmaXPow_neg_half_circuit :
    HTCircuit.eval sigmaXPow_neg_half_circuit = sigmaXPow (-(1 / 2)) := by
  rw [sigmaXPow_neg_half_circuit, HTCircuit_eval_append, HTCircuit_eval_append,
    eval_sigmaZPow_neg_half_circuit]
  simp [HTCircuit.eval, oneQubitHTCircuitMatrix, OneQubitHTPrimitive.eval, sigmaXPow, mul_assoc]

def sigmaYPow_quarter_circuit : HTCircuit :=
  sigmaZPow_half_circuit ++ sigmaXPow_quarter_circuit ++ sigmaZPow_neg_half_circuit

def sigmaYPow_neg_quarter_circuit : HTCircuit :=
  sigmaZPow_half_circuit ++ sigmaXPow_neg_quarter_circuit ++ sigmaZPow_neg_half_circuit

private theorem eval_sigmaYPow_quarter_circuit :
    HTCircuit.eval sigmaYPow_quarter_circuit = sigmaYPow (1 / 4) := by
  rw [sigmaYPow_quarter_circuit, HTCircuit_eval_append, HTCircuit_eval_append,
    eval_sigmaZPow_half_circuit, eval_sigmaXPow_quarter_circuit,
    eval_sigmaZPow_neg_half_circuit]
  simp [sigmaYPow, mul_assoc]

private theorem eval_sigmaYPow_neg_quarter_circuit :
    HTCircuit.eval sigmaYPow_neg_quarter_circuit = sigmaYPow (-(1 / 4)) := by
  rw [sigmaYPow_neg_quarter_circuit, HTCircuit_eval_append, HTCircuit_eval_append,
    eval_sigmaZPow_half_circuit, eval_sigmaXPow_neg_quarter_circuit,
    eval_sigmaZPow_neg_half_circuit]
  simp [sigmaYPow, mul_assoc]

def hPow_half_circuit : HTCircuit :=
  sigmaYPow_quarter_circuit ++ sigmaZPow_half_circuit ++ sigmaYPow_neg_quarter_circuit

def hPow_neg_half_circuit : HTCircuit :=
  sigmaYPow_quarter_circuit ++ sigmaZPow_neg_half_circuit ++ sigmaYPow_neg_quarter_circuit

private theorem eval_hPow_half_circuit :
    HTCircuit.eval hPow_half_circuit = HPow (1 / 2) := by
  rw [hPow_half_circuit, HTCircuit_eval_append, HTCircuit_eval_append,
    eval_sigmaYPow_quarter_circuit, eval_sigmaZPow_half_circuit,
    eval_sigmaYPow_neg_quarter_circuit]
  simp [HPow, mul_assoc]

private theorem eval_hPow_neg_half_circuit :
    HTCircuit.eval hPow_neg_half_circuit = HPow (-(1 / 2)) := by
  rw [hPow_neg_half_circuit, HTCircuit_eval_append, HTCircuit_eval_append,
    eval_sigmaYPow_quarter_circuit, eval_sigmaZPow_neg_half_circuit,
    eval_sigmaYPow_neg_quarter_circuit]
  simp [HPow, mul_assoc]

/-- HT circuit for Boykin matrix A. -/
def boykinA_circuit : HTCircuit :=
  sigmaZPow_neg_quarter_circuit ++ sigmaXPow_quarter_circuit

/-- HT circuit for Boykin matrix B. -/
def boykinB_circuit : HTCircuit :=
  hPow_neg_half_circuit ++ boykinA_circuit ++ hPow_half_circuit

theorem boykinA_circuit_eval :
    HTCircuit.eval boykinA_circuit = boykinA := by
  rw [boykinA_circuit, HTCircuit_eval_append, eval_sigmaZPow_neg_quarter_circuit,
    eval_sigmaXPow_quarter_circuit]
  rfl

theorem boykinB_circuit_eval :
    HTCircuit.eval boykinB_circuit = boykinB := by
  rw [boykinB_circuit, HTCircuit_eval_append, HTCircuit_eval_append,
    eval_hPow_neg_half_circuit, boykinA_circuit_eval, eval_hPow_half_circuit]
  simp [boykinB, mul_assoc]

/-! ### Integer powers of Boykin matrices -/

/-- The inverse word for one HT primitive, using `H⁻¹ = H` and `T⁻¹ = T^7`. -/
def primitiveInvCircuit : OneQubitHTPrimitive → HTCircuit
  | .h => [.h]
  | .t => tPowCircuit 7

private theorem primitiveInvCircuit_eval (gate : OneQubitHTPrimitive) :
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

/-- Reverse a circuit and replace each gate by its Boykin HT inverse word. -/
def circuitInverse : HTCircuit → HTCircuit
  | [] => []
  | gate :: gates => circuitInverse gates ++ primitiveInvCircuit gate

private theorem circuitInverse_eval (gates : HTCircuit) :
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

private theorem circuitPower_eval (C : HTCircuit) (n : ℕ) :
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

def boykinA_power_circuit (n : ℤ) : HTCircuit :=
  if n ≥ 0 then circuitPower boykinA_circuit n.natAbs
  else circuitPower (circuitInverse boykinA_circuit) n.natAbs

def boykinB_power_circuit (n : ℤ) : HTCircuit :=
  if n ≥ 0 then circuitPower boykinB_circuit n.natAbs
  else circuitPower (circuitInverse boykinB_circuit) n.natAbs

theorem eval_boykinA_power_circuit (n : ℤ) :
    HTCircuit.eval (boykinA_power_circuit n) = zpowMatrix boykinA n := by
  by_cases hn : n ≥ 0
  · simp [boykinA_power_circuit, zpowMatrix, hn, circuitPower_eval, boykinA_circuit_eval]
  · simp [boykinA_power_circuit, zpowMatrix, hn, circuitPower_eval, circuitInverse_eval,
      boykinA_circuit_eval]

theorem eval_boykinB_power_circuit (n : ℤ) :
    HTCircuit.eval (boykinB_power_circuit n) = zpowMatrix boykinB n := by
  by_cases hn : n ≥ 0
  · simp [boykinB_power_circuit, zpowMatrix, hn, circuitPower_eval, boykinB_circuit_eval]
  · simp [boykinB_power_circuit, zpowMatrix, hn, circuitPower_eval, circuitInverse_eval,
      boykinB_circuit_eval]

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

private theorem axisRotation_powers_dense
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

theorem boykinA_powers_dense_axis₁ (α : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℤ, hsDistance (axisRotation boykinAxis₁ α) (zpowMatrix boykinA n) < ε := by
  have hirr : Irrational ((boykinLambda * Real.pi) / (2 * Real.pi)) := by
    have hratio :
        (boykinLambda * Real.pi) / (2 * Real.pi) = boykinLambda / (2 : ℝ) := by
      field_simp [Real.pi_ne_zero]
    rw [hratio]
    simpa using boykinLambda_irrational.div_ratCast (by norm_num : (2 : ℚ) ≠ 0)
  exact axisRotation_powers_dense boykinAxis₁ boykin_axes_unit.1 boykinA
    (boykinLambda * Real.pi) α boykinA_is_axisRotation hirr hε

theorem boykinB_powers_dense_axis₂ (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℤ, hsDistance (axisRotation boykinAxis₂ β) (zpowMatrix boykinB n) < ε := by
  have hirr : Irrational ((boykinLambda * Real.pi) / (2 * Real.pi)) := by
    have hratio :
        (boykinLambda * Real.pi) / (2 * Real.pi) = boykinLambda / (2 : ℝ) := by
      field_simp [Real.pi_ne_zero]
    rw [hratio]
    simpa using boykinLambda_irrational.div_ratCast (by norm_num : (2 : ℚ) ≠ 0)
  exact axisRotation_powers_dense boykinAxis₂ boykin_axes_unit.2 boykinB
    (boykinLambda * Real.pi) β boykinB_is_axisRotation hirr hε

/-! ## Boykin Euler decomposition -/

private noncomputable def standardZAxis : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.equiv (Fin 3) ℝ |>.symm ![0, 0, 1]

private lemma standardZAxis_unit : ‖standardZAxis‖ = 1 := by
  have hsq : ‖standardZAxis‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    have h2 : ![(0 : ℝ), 0, 1] (2 : Fin 3) = 1 := by
      rfl
    simp [standardZAxis, h2]
  nlinarith [norm_nonneg standardZAxis]

private lemma rz_eq_axisRotation_standardZ (θ : ℝ) :
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

/-- Boykin's expansion: R(n₁,α)R(n₂,β)R(n₁,γ) equals the scalar/vector formula -/
theorem boykin_euler_product_expansion
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

/-! ## Boykin Euler-product approximation -/

/-- Approximate an Euler product by HT circuits. -/
theorem boykin_HT_approx_euler_product (α β γ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : HTCircuit,
      hsDistance
        (axisRotation boykinAxis₁ α * axisRotation boykinAxis₂ β * axisRotation boykinAxis₁ γ)
        (HTCircuit.eval C)
        < ε := by
  -- Divide error budget into three equal parts
  have hε3 : 0 < ε / 3 := by positivity

  -- Approximate each rotation using density theorems
  obtain ⟨n₁, hn₁⟩ := boykinA_powers_dense_axis₁ α hε3
  obtain ⟨n₂, hn₂⟩ := boykinB_powers_dense_axis₂ β hε3
  obtain ⟨n₃, hn₃⟩ := boykinA_powers_dense_axis₁ γ hε3

  -- Construct combined circuit
  let C := boykinA_power_circuit n₁ ++ boykinB_power_circuit n₂ ++ boykinA_power_circuit n₃
  use C

  -- The circuit evaluates to the product A^n₁ · B^n₂ · A^n₃
  have hC_eval : HTCircuit.eval C = zpowMatrix boykinA n₁ * zpowMatrix boykinB n₂ * zpowMatrix boykinA n₃ := by
    simp [C, HTCircuit_eval_append]
    rw [eval_boykinA_power_circuit, eval_boykinB_power_circuit, eval_boykinA_power_circuit]
    rw [mul_assoc]

  -- Zpow preserves unitary group membership
  have hA : boykinA ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [boykinA_is_axisRotation]
    exact axisRotation_mem_unitaryGroup boykinAxis₁ boykin_axes_unit.1 (boykinLambda * Real.pi)
  have hB : boykinB ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [boykinB_is_axisRotation]
    exact axisRotation_mem_unitaryGroup boykinAxis₂ boykin_axes_unit.2 (boykinLambda * Real.pi)

  have hA_n₁ : zpowMatrix boykinA n₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    unfold zpowMatrix
    by_cases hn : n₁ ≥ 0
    · simp only [hn, ite_true]
      -- boykinA^n is unitary when boykinA is unitary
      rw [boykinA_is_axisRotation]
      exact (Matrix.unitaryGroup (Fin 2) ℂ).pow_mem (axisRotation_mem_unitaryGroup boykinAxis₁ boykin_axes_unit.1 (boykinLambda * Real.pi)) n₁.natAbs
    · simp only [hn, ite_false]
      -- boykinA⁻¹ ^ n is unitary
      rw [boykinA_is_axisRotation, axisRotation_inv]
      exact (Matrix.unitaryGroup (Fin 2) ℂ).pow_mem (axisRotation_mem_unitaryGroup boykinAxis₁ boykin_axes_unit.1 (-(boykinLambda * Real.pi))) n₁.natAbs
  have hB_n₂ : zpowMatrix boykinB n₂ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    unfold zpowMatrix
    by_cases hn : n₂ ≥ 0
    · simp only [hn, ite_true]
      rw [boykinB_is_axisRotation]
      exact (Matrix.unitaryGroup (Fin 2) ℂ).pow_mem (axisRotation_mem_unitaryGroup boykinAxis₂ boykin_axes_unit.2 (boykinLambda * Real.pi)) n₂.natAbs
    · simp only [hn, ite_false]
      rw [boykinB_is_axisRotation, axisRotation_inv]
      exact (Matrix.unitaryGroup (Fin 2) ℂ).pow_mem (axisRotation_mem_unitaryGroup boykinAxis₂ boykin_axes_unit.2 (-(boykinLambda * Real.pi))) n₂.natAbs
  have hA_n₃ : zpowMatrix boykinA n₃ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    unfold zpowMatrix
    by_cases hn : n₃ ≥ 0
    · simp only [hn, ite_true]
      rw [boykinA_is_axisRotation]
      exact (Matrix.unitaryGroup (Fin 2) ℂ).pow_mem (axisRotation_mem_unitaryGroup boykinAxis₁ boykin_axes_unit.1 (boykinLambda * Real.pi)) n₃.natAbs
    · simp only [hn, ite_false]
      rw [boykinA_is_axisRotation, axisRotation_inv]
      exact (Matrix.unitaryGroup (Fin 2) ℂ).pow_mem (axisRotation_mem_unitaryGroup boykinAxis₁ boykin_axes_unit.1 (-(boykinLambda * Real.pi))) n₃.natAbs

  -- Apply triangle inequality for products
  calc hsDistance (axisRotation boykinAxis₁ α * axisRotation boykinAxis₂ β * axisRotation boykinAxis₁ γ)
                  (HTCircuit.eval C)
      = hsDistance (axisRotation boykinAxis₁ α * axisRotation boykinAxis₂ β * axisRotation boykinAxis₁ γ)
                   (zpowMatrix boykinA n₁ * zpowMatrix boykinB n₂ * zpowMatrix boykinA n₃) := by
          rw [hC_eval]
    _ ≤ hsDistance (axisRotation boykinAxis₁ α) (zpowMatrix boykinA n₁) +
        hsDistance (axisRotation boykinAxis₂ β) (zpowMatrix boykinB n₂) +
        hsDistance (axisRotation boykinAxis₁ γ) (zpowMatrix boykinA n₃) := by
          apply hsDistance_triple_mul_le
          · exact axisRotation_mem_unitaryGroup boykinAxis₁ boykin_axes_unit.1 α
          · exact hA_n₁
          · exact axisRotation_mem_unitaryGroup boykinAxis₂ boykin_axes_unit.2 β
          · exact hB_n₂
          · exact axisRotation_mem_unitaryGroup boykinAxis₁ boykin_axes_unit.1 γ
          · exact hA_n₃
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith [hn₁, hn₂, hn₃]
    _ = ε := by ring

/-! ## Specialization to Rz rotations -/

/-- The standard `z`-axis rotation only needs the Boykin two-axis Euler
decomposition, not the full density theorem for every `SU(2)` matrix. -/
private theorem standardZ_axisRotation_boykin_euler (φ : ℝ) :
    ∃ α β γ : ℝ,
      axisRotation standardZAxis φ =
        axisRotation boykinAxis₁ α *
          axisRotation boykinAxis₂ β *
            axisRotation boykinAxis₁ γ := by
  let n₃ := cross boykinAxis₁ boykinAxis₂
  have hn₃ : ‖n₃‖ = 1 :=
    cross_orthogonal_unit_is_unit boykinAxis₁ boykinAxis₂
      boykin_axes_unit.1 boykin_axes_unit.2 boykin_axes_orthogonal
  have hortho13 : inner ℝ boykinAxis₁ n₃ = 0 := by
    rw [real_inner_comm]
    exact cross_orthogonal_left boykinAxis₁ boykinAxis₂
  have hortho23 : inner ℝ boykinAxis₂ n₃ = 0 := by
    rw [real_inner_comm]
    exact cross_orthogonal_right boykinAxis₁ boykinAxis₂
  let frame : Fin 3 → EuclideanSpace ℝ (Fin 3) := fun i =>
    match i with
    | 0 => boykinAxis₁
    | 1 => boykinAxis₂
    | 2 => n₃
  have hframe_orthonormal : Orthonormal ℝ frame := by
    constructor
    · intro i
      fin_cases i <;> simp [frame, hn₃, boykin_axes_unit]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [frame]
      · contradiction
      · exact boykin_axes_orthogonal
      · exact hortho13
      · rw [real_inner_comm]
        exact boykin_axes_orthogonal
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
  let c₁ := inner ℝ standardZAxis boykinAxis₁
  let c₂ := inner ℝ standardZAxis boykinAxis₂
  let c₃ := inner ℝ standardZAxis n₃
  have hdecomp :
      c₁ • boykinAxis₁ + c₂ • boykinAxis₂ + c₃ • n₃ = standardZAxis := by
    simpa [Fin.sum_univ_three, hb, frame, c₁, c₂, c₃, real_inner_comm] using
      b.sum_repr' standardZAxis
  have hcoeff_sq : c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2 = 1 := by
    have hparseval :
        ∑ i : Fin 3, inner ℝ standardZAxis (b i) * inner ℝ (b i) standardZAxis =
          inner ℝ standardZAxis standardZAxis :=
      OrthonormalBasis.sum_inner_mul_inner b standardZAxis standardZAxis
    calc
      c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2 =
          inner ℝ standardZAxis boykinAxis₁ * inner ℝ boykinAxis₁ standardZAxis +
            inner ℝ standardZAxis boykinAxis₂ * inner ℝ boykinAxis₂ standardZAxis +
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
  rw [boykin_euler_product_expansion boykinAxis₁ boykinAxis₂
    boykin_axes_unit.1 boykin_axes_unit.2 boykin_axes_orthogonal α β γ]
  rw [hscalar]
  congr 1
  rw [hcoef₁, hcoef₂, hcoef₃]
  change Real.sin φ • standardZAxis =
    (c₁ * Real.sin φ) • boykinAxis₁ +
      (c₂ * Real.sin φ) • boykinAxis₂ +
        (c₃ * Real.sin φ) • n₃
  rw [← hdecomp]
  module

/-- HT circuits approximate any Rz rotation. -/
theorem HT_Rz_dense (θ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : HTCircuit, hsDistance (rz θ) (HTCircuit.eval C) < ε := by
  obtain ⟨α, β, γ, hEuler⟩ :=
    standardZ_axisRotation_boykin_euler (-(θ / 2))
  obtain ⟨C, hC⟩ := boykin_HT_approx_euler_product α β γ hε
  refine ⟨C, ?_⟩
  rw [rz_eq_axisRotation_standardZ]
  simpa [hEuler] using hC

end Lemma12
end Clifford
end TwoControl

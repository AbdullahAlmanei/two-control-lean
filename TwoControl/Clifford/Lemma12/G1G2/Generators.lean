import TwoControl.Clifford.Lemma12.G1G2.AxisRotation

namespace TwoControl
namespace Clifford
namespace Lemma12
namespace G1G2

open Universal
open Matrix

/-!
# The gates `G₁, G₂` of `universal_new_gates.tex` (July 2026)

The paper defines

  `G₁ = e^{-3iπ/8} · THTHT`,
  `G₂ = (HT⁴) · G₁ · (HT⁴)†`

and proves (Lemma `properties-of-g1-g2`) that both have determinant `1` and
trace `√(1 + 1/√2)`, and (Lemma `a1-and-a2-anticommute`) that their rotation
axes are orthogonal.

This file provides the finite `2×2` computations behind those claims:

* `g1_mem_unitaryGroup`, `g2_mem_unitaryGroup`, `g1_det`, `g2_det`;
* the *squared* traces `g1_trace_sq`, `g2_trace_sq` (the identification of
  the rotation angle in `AngleIdentification.lean` only ever consumes the
  square, which keeps every computation inside `ℚ(i,√2)` — no `π/8`
  trigonometry);
* the product trace `g1_g2_trace`, which pins the axis inner product in
  `Orthogonality.lean`;
* the `{H,T}` words realizing `G₁` and `G₂` up to the global phase
  `gPhase = e^{-3iπ/8}` (`g1Word_eval`, `g2Word_eval`).
-/

/-! ## Definitions -/

/-- The global phase `e^{-3iπ/8}` of the paper's `G₁`. -/
noncomputable def gPhase : ℂ :=
  Complex.exp (-(Complex.I * (3 * Real.pi / 8)))

/-- The raw five-letter word `THTHT`. -/
noncomputable def gWordMatrix1 : Square 2 :=
  phaseT * hadamard2 * phaseT * hadamard2 * phaseT

/-- The paper's gate `G₁ = e^{-3iπ/8} · THTHT`. -/
noncomputable def g1 : Square 2 :=
  gPhase • gWordMatrix1

/-- The conjugator `HT⁴`. -/
noncomputable def gConj : Square 2 :=
  hadamard2 * phaseT ^ 4

/-- The inverse conjugator `(HT⁴)† = T⁴H` (using `T⁸ = 1`, `H² = 1`). -/
noncomputable def gConjInv : Square 2 :=
  phaseT ^ 4 * hadamard2

/-- The raw conjugated word `(HT⁴) · THTHT · (T⁴H)`. -/
noncomputable def gWordMatrix2 : Square 2 :=
  gConj * gWordMatrix1 * gConjInv

/-- The paper's gate `G₂ = (HT⁴) · G₁ · (HT⁴)†`. -/
noncomputable def g2 : Square 2 :=
  gConj * g1 * gConjInv

/-! ## Complex constants -/

private lemma csqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

private lemma csqrt2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (show (Real.sqrt 2 : ℝ) ≠ 0 by positivity)

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

private lemma exp_neg_I_three_pi_div_four :
    Complex.exp (-(Complex.I * (3 * Real.pi / 4))) =
      -((Real.sqrt 2 / 2 : ℝ) : ℂ) - ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [show -(Complex.I * (3 * Real.pi / 4)) =
      ((-(3 * Real.pi / 4) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  have h34 : (3 * Real.pi / 4 : ℝ) = Real.pi - Real.pi / 4 := by ring
  have hcos : Complex.cos ((-(3 * Real.pi / 4) : ℝ) : ℂ) =
      -(((Real.sqrt 2) / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cos, Real.cos_neg, h34, Real.cos_pi_sub, Real.cos_pi_div_four]
    push_cast
    ring
  have hsin : Complex.sin ((-(3 * Real.pi / 4) : ℝ) : ℂ) =
      -(((Real.sqrt 2) / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin, Real.sin_neg, h34, Real.sin_pi_sub, Real.sin_pi_div_four]
    push_cast
    ring
  rw [hcos, hsin]
  ring

private lemma gPhase_sq :
    gPhase ^ 2 =
      -((Real.sqrt 2 / 2 : ℝ) : ℂ) - ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [gPhase, sq, ← Complex.exp_add,
    show -(Complex.I * (3 * Real.pi / 8)) + -(Complex.I * (3 * Real.pi / 8)) =
      -(Complex.I * (3 * Real.pi / 4)) by ring]
  exact exp_neg_I_three_pi_div_four

lemma gPhase_norm : ‖gPhase‖ = 1 := by
  rw [gPhase, Complex.norm_exp]
  simp

lemma gPhase_ne : gPhase ≠ 0 := by
  intro h
  have := gPhase_norm
  rw [h] at this
  simp at this

lemma gPhase_inv_norm : ‖gPhase⁻¹‖ = 1 := by
  rw [norm_inv, gPhase_norm]
  norm_num

/-! ## The conjugator is its own inverse pair -/

private lemma phaseT_pow_four_sq : phaseT ^ 4 * phaseT ^ 4 = 1 := by
  rw [← pow_add]
  norm_num
  exact phaseT_pow_eight

lemma gConj_mul_gConjInv : gConj * gConjInv = 1 := by
  rw [gConj, gConjInv, mul_assoc, ← mul_assoc (phaseT ^ 4), phaseT_pow_four_sq,
    one_mul, hadamard2_sq_eq_one]

lemma gConjInv_mul_gConj : gConjInv * gConj = 1 := by
  rw [gConj, gConjInv, mul_assoc, ← mul_assoc hadamard2, hadamard2_sq_eq_one,
    one_mul, phaseT_pow_four_sq]

/-! ## Unitarity -/

private theorem smul_mem_unitaryGroup {z : ℂ} (hz : ‖z‖ = 1) {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    z • U ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hU ⊢
  have hzz : (starRingEnd ℂ) z * z = 1 := by
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    rw [← Complex.sq_norm, hz]
    norm_num
  calc star (z • U) * (z • U)
      = ((starRingEnd ℂ) z * z) • (star U * U) := by
        rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rfl
    _ = 1 := by rw [hzz, hU, one_smul]

private theorem gWordMatrix1_mem_unitaryGroup :
    gWordMatrix1 ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  exact Submonoid.mul_mem _
    (Submonoid.mul_mem _
      (Submonoid.mul_mem _
        (Submonoid.mul_mem _ phaseT_mem_unitaryGroup hadamard2_mem_unitaryGroup)
        phaseT_mem_unitaryGroup)
      hadamard2_mem_unitaryGroup)
    phaseT_mem_unitaryGroup

private theorem gConj_mem_unitaryGroup :
    gConj ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Submonoid.mul_mem _ hadamard2_mem_unitaryGroup
    (Submonoid.pow_mem _ phaseT_mem_unitaryGroup 4)

private theorem gConjInv_mem_unitaryGroup :
    gConjInv ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Submonoid.mul_mem _ (Submonoid.pow_mem _ phaseT_mem_unitaryGroup 4)
    hadamard2_mem_unitaryGroup

theorem g1_mem_unitaryGroup : g1 ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  smul_mem_unitaryGroup gPhase_norm gWordMatrix1_mem_unitaryGroup

theorem g2_mem_unitaryGroup : g2 ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Submonoid.mul_mem _
    (Submonoid.mul_mem _ gConj_mem_unitaryGroup g1_mem_unitaryGroup)
    gConjInv_mem_unitaryGroup

/-! ## Determinants (paper Lemma `properties-of-g1-g2`, first clause) -/

private lemma det_phaseT : phaseT.det = Complex.exp (Complex.I * (Real.pi / 4)) := by
  simp [phaseT, diag2, Matrix.det_fin_two, Matrix.diagonal]

private lemma det_hadamard2 : hadamard2.det = -1 := by
  rw [Matrix.det_fin_two]
  simp [hadamard2]
  ring_nf
  rw [inv_pow, csqrt2_sq]
  norm_num

theorem g1_det : g1.det = 1 := by
  rw [g1, Matrix.det_smul, gWordMatrix1]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    det_phaseT, det_hadamard2]
  rw [Fintype.card_fin]
  rw [show gPhase ^ 2 *
      (Complex.exp (Complex.I * (Real.pi / 4)) * -1 *
        Complex.exp (Complex.I * (Real.pi / 4)) * -1 *
        Complex.exp (Complex.I * (Real.pi / 4))) =
      gPhase ^ 2 *
        (Complex.exp (Complex.I * (Real.pi / 4)) *
          Complex.exp (Complex.I * (Real.pi / 4)) *
          Complex.exp (Complex.I * (Real.pi / 4))) by ring]
  rw [← Complex.exp_add, ← Complex.exp_add, gPhase, sq, ← Complex.exp_add,
    ← Complex.exp_add]
  rw [show -(Complex.I * (3 * Real.pi / 8)) + -(Complex.I * (3 * Real.pi / 8)) +
      (Complex.I * (Real.pi / 4) + Complex.I * (Real.pi / 4) +
        Complex.I * (Real.pi / 4)) = 0 by ring]
  exact Complex.exp_zero

theorem g2_det : g2.det = 1 := by
  rw [g2, Matrix.det_mul, Matrix.det_mul]
  have h : gConj.det * gConjInv.det = 1 := by
    rw [← Matrix.det_mul, gConj_mul_gConjInv, Matrix.det_one]
  calc gConj.det * g1.det * gConjInv.det
      = gConj.det * gConjInv.det * g1.det := by ring
    _ = 1 := by rw [h, g1_det, one_mul]

/-! ## Explicit matrices -/

set_option maxHeartbeats 1600000 in
private lemma gWordMatrix1_matrix :
    gWordMatrix1 =
      Matrix.of ![
        ![(2 + (Real.sqrt 2 : ℂ) + (Real.sqrt 2 : ℂ) * Complex.I) / 4,
          ((Real.sqrt 2 : ℂ) - 2 * Complex.I + (Real.sqrt 2 : ℂ) * Complex.I) / 4],
        ![((Real.sqrt 2 : ℂ) - 2 * Complex.I + (Real.sqrt 2 : ℂ) * Complex.I) / 4,
          (-(Real.sqrt 2 : ℂ) + 2 * Complex.I + (Real.sqrt 2 : ℂ) * Complex.I) / 4]] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [gWordMatrix1, phaseT, diag2, Matrix.diagonal, hadamard2, Matrix.mul_apply,
      Fin.sum_univ_two]
    ring_nf
    try rw [exp_I_pi_div_four]
    try rw [exp_I_pi_mul_quarter]
    push_cast
    ring_nf
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := csqrt2_sq
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := csqrt2_ne
    field_simp [hne]
    have hs3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℂ) := by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 *
            (Real.sqrt 2 : ℂ) := by ring
        _ = 2 * (Real.sqrt 2 : ℂ) := by rw [csqrt2_sq]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    have hI3 : Complex.I ^ 3 = -Complex.I := by
      rw [pow_succ, Complex.I_sq]
      ring
    ring_nf at hs ⊢
    try rw [hs3]
    try rw [hs]
    try rw [hI3]
    try rw [hI]
    ring

private lemma phaseT_pow_four : phaseT ^ 4 = Matrix.of ![![(1 : ℂ), 0], ![0, -1]] := by
  have hexp : Complex.exp (Complex.I * (Real.pi / 4)) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul,
      show ((4 : ℕ) : ℂ) * (Complex.I * (Real.pi / 4)) = Real.pi * Complex.I by
        push_cast; ring]
    exact Complex.exp_pi_mul_I
  rw [phaseT, diag2, Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Pi.pow_apply, hexp]

set_option maxHeartbeats 1600000 in
private lemma gWordMatrix2_matrix :
    gWordMatrix2 =
      Matrix.of ![
        ![(1 - (Real.sqrt 2 : ℂ) + 3 * Complex.I) / 4,
          (1 + (Real.sqrt 2 : ℂ) - Complex.I) / 4],
        ![(1 + (Real.sqrt 2 : ℂ) - Complex.I) / 4,
          (1 + (Real.sqrt 2 : ℂ) - Complex.I + 2 * (Real.sqrt 2 : ℂ) * Complex.I) / 4]] := by
  rw [gWordMatrix2, gConj, gConjInv, phaseT_pow_four, gWordMatrix1_matrix]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [hadamard2, Matrix.mul_apply, Fin.sum_univ_two]
    try ring_nf
    try push_cast
    try ring_nf
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := csqrt2_sq
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := csqrt2_ne
    try field_simp [hne]
    have hs3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℂ) := by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 *
            (Real.sqrt 2 : ℂ) := by ring
        _ = 2 * (Real.sqrt 2 : ℂ) := by rw [csqrt2_sq]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    have hI3 : Complex.I ^ 3 = -Complex.I := by
      rw [pow_succ, Complex.I_sq]
      ring
    try ring_nf at hs ⊢
    try rw [hs3]
    try rw [hs]
    try rw [hI3]
    try rw [hI]
    ring

/-! ## Traces -/

private lemma trace_gWordMatrix1 :
    Matrix.trace gWordMatrix1 =
      (1 + Complex.I + (Real.sqrt 2 : ℂ) * Complex.I) / 2 := by
  rw [gWordMatrix1_matrix, Matrix.trace_fin_two]
  show (2 + (Real.sqrt 2 : ℂ) + (Real.sqrt 2 : ℂ) * Complex.I) / 4 +
      (-(Real.sqrt 2 : ℂ) + 2 * Complex.I + (Real.sqrt 2 : ℂ) * Complex.I) / 4 =
      (1 + Complex.I + (Real.sqrt 2 : ℂ) * Complex.I) / 2
  ring

set_option maxHeartbeats 800000 in
private lemma trace_gWordMatrix1_mul_gWordMatrix2 :
    Matrix.trace (gWordMatrix1 * gWordMatrix2) =
      (-(Real.sqrt 2 : ℂ) - 1 + (Real.sqrt 2 : ℂ) * Complex.I + Complex.I) / 4 := by
  rw [gWordMatrix1_matrix, gWordMatrix2_matrix, Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := csqrt2_sq
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  ring_nf
  ring_nf at hs
  rw [hs, hI]
  ring

/-- The squared trace of `G₁` (paper: `Tr(G₁) = √(1 + 1/√2)`, squared to stay
inside `ℚ(i,√2)`). -/
theorem g1_trace_sq :
    Matrix.trace g1 ^ 2 = ((1 + Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  rw [g1, Matrix.trace_smul, smul_eq_mul, mul_pow, gPhase_sq, trace_gWordMatrix1]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := csqrt2_sq
  have hs3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℂ) := by
    calc
      ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 *
          (Real.sqrt 2 : ℂ) := by ring
      _ = 2 * (Real.sqrt 2 : ℂ) := by rw [csqrt2_sq]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  push_cast
  ring_nf
  ring_nf at hs
  try rw [hs3]
  try rw [hs]
  try rw [hI3]
  try rw [hI]
  ring

/-- `Tr(G₂) = Tr(G₁)` by similarity. -/
theorem g2_trace_eq_g1_trace : Matrix.trace g2 = Matrix.trace g1 := by
  rw [g2, Matrix.trace_mul_cycle, gConjInv_mul_gConj, one_mul]

theorem g2_trace_sq :
    Matrix.trace g2 ^ 2 = ((1 + Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  rw [g2_trace_eq_g1_trace]
  exact g1_trace_sq

private lemma g2_eq_smul : g2 = gPhase • gWordMatrix2 := by
  rw [g2, g1, gWordMatrix2, Matrix.mul_smul, Matrix.smul_mul]

/-- The product trace `Tr(G₁G₂) = 1/2 + √2/4`, the input to the axis
orthogonality argument. -/
theorem g1_g2_trace :
    Matrix.trace (g1 * g2) = (((2 + Real.sqrt 2) / 4 : ℝ) : ℂ) := by
  have hmul : g1 * g2 = gPhase ^ 2 • (gWordMatrix1 * gWordMatrix2) := by
    rw [g1, g2_eq_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
  rw [hmul, Matrix.trace_smul, smul_eq_mul, gPhase_sq,
    trace_gWordMatrix1_mul_gWordMatrix2]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := csqrt2_sq
  have hs3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℂ) := by
    calc
      ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 *
          (Real.sqrt 2 : ℂ) := by ring
      _ = 2 * (Real.sqrt 2 : ℂ) := by rw [csqrt2_sq]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  push_cast
  ring_nf
  ring_nf at hs
  try rw [hs3]
  try rw [hs]
  try rw [hI3]
  try rw [hI]
  ring

/-! ## Circuit words -/

/-- The five-letter `{H,T}` word for `G₁` (up to the phase `gPhase`). -/
def g1Word : HTCircuit := [.t, .h, .t, .h, .t]

/-- The `{H,T}` word for `G₂ = (HT⁴)·G₁·(T⁴H)` (up to the phase `gPhase`). -/
def g2Word : HTCircuit :=
  [.h, .t, .t, .t, .t] ++ g1Word ++ [.t, .t, .t, .t, .h]

theorem g1Word_eval : HTCircuit.eval g1Word = gPhase⁻¹ • g1 := by
  have heval : HTCircuit.eval g1Word = gWordMatrix1 := by
    simp [g1Word, HTCircuit.eval, oneQubitHTCircuitMatrix, OneQubitHTPrimitive.eval,
      gWordMatrix1, mul_assoc]
  rw [heval, g1, smul_smul, inv_mul_cancel₀ gPhase_ne, one_smul]

theorem g2Word_eval : HTCircuit.eval g2Word = gPhase⁻¹ • g2 := by
  have heval : HTCircuit.eval g2Word = gWordMatrix2 := by
    simp [g2Word, g1Word, HTCircuit.eval, oneQubitHTCircuitMatrix,
      OneQubitHTPrimitive.eval, gWordMatrix2, gWordMatrix1, gConj, gConjInv,
      mul_assoc, pow_succ]
  rw [heval, g2_eq_smul, smul_smul, inv_mul_cancel₀ gPhase_ne, one_smul]

end G1G2
end Lemma12
end Clifford
end TwoControl

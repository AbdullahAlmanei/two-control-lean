import TwoControl.Clifford.Definitions
import TwoControl.CosineSine.Statements
import TwoControl.StateHelpers
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Matrix

namespace TwoControl
namespace Clifford

private noncomputable def ryBridgeCore (θ : ℝ) : Square 2 :=
  Matrix.of ![![Complex.cos ((θ : ℂ) * (2⁻¹ : ℂ)), Complex.sin ((θ : ℂ) * (2⁻¹ : ℂ)) * Complex.I],
              ![Complex.sin ((θ : ℂ) * (2⁻¹ : ℂ)) * Complex.I, Complex.cos ((θ : ℂ) * (2⁻¹ : ℂ))]]

private lemma inv_sqrt_two_mul_inv_sqrt_two :
    ((↑(Real.sqrt 2) : ℂ)⁻¹) * ((↑(Real.sqrt 2) : ℂ)⁻¹) = (1 / 2 : ℂ) := by
  calc
    ((↑(Real.sqrt 2) : ℂ)⁻¹) * ((↑(Real.sqrt 2) : ℂ)⁻¹)
        = (((↑(Real.sqrt 2) : ℂ) * (↑(Real.sqrt 2) : ℂ))⁻¹) := by
            exact (mul_inv_rev (↑(Real.sqrt 2) : ℂ) (↑(Real.sqrt 2) : ℂ)).symm
    _ = ((2 : ℂ))⁻¹ := by
          congr 1
          have hsq' : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
          have hsq : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := by
            calc
              (Real.sqrt 2 : ℝ) * Real.sqrt 2 = (Real.sqrt 2 : ℝ) ^ 2 := by ring
              _ = 2 := hsq'
          exact_mod_cast hsq
    _ = (1 / 2 : ℂ) := by
          norm_num

private lemma inv_sqrt_two_sq :
    ((↑(Real.sqrt 2) : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
  simpa [pow_two] using inv_sqrt_two_mul_inv_sqrt_two

private lemma complex_half_eq_div_two (θ : ℝ) :
    ((θ : ℂ) * (2⁻¹ : ℂ)) = ((θ : ℂ) / 2) := by
  ring

private lemma exp_half_pos (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ) * (2⁻¹ : ℂ)) =
      Complex.cos ((θ : ℂ) * (2⁻¹ : ℂ)) +
        Complex.sin ((θ : ℂ) * (2⁻¹ : ℂ)) * Complex.I := by
  rw [show Complex.I * (θ : ℂ) * (2⁻¹ : ℂ) = ((θ : ℂ) * (2⁻¹ : ℂ)) * Complex.I by ring,
    Complex.exp_mul_I]

private lemma exp_half_neg (θ : ℝ) :
    Complex.exp (-(Complex.I * (θ : ℂ) * (2⁻¹ : ℂ))) =
      Complex.cos ((θ : ℂ) * (2⁻¹ : ℂ)) -
        Complex.sin ((θ : ℂ) * (2⁻¹ : ℂ)) * Complex.I := by
  rw [show -(Complex.I * (θ : ℂ) * (2⁻¹ : ℂ)) = (-((θ : ℂ) * (2⁻¹ : ℂ))) * Complex.I by ring,
    Complex.exp_mul_I,
    Complex.cos_neg,
    Complex.sin_neg]
  ring

private lemma rz_neg_eq (θ : ℝ) :
    rz (-θ) =
      diag2 (Complex.exp (Complex.I * (θ : ℂ) * (2⁻¹ : ℂ)))
        (Complex.exp (-(Complex.I * (θ : ℂ) * (2⁻¹ : ℂ)))) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rz, diag2]
  · congr 1
    ring
  · congr 1
    ring

private lemma hadamard_mul_rz_neg_mul_hadamard_eq_core (θ : ℝ) :
    hadamard2 * rz (-θ) * hadamard2 = ryBridgeCore θ := by
  ext i j
  fin_cases i <;> fin_cases j
  · rw [rz_neg_eq]
    simp [hadamard2, ryBridgeCore, Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_two, diag2]
    rw [exp_half_pos, exp_half_neg]
    ring_nf
    rw [inv_sqrt_two_sq]
    ring
  · rw [rz_neg_eq]
    simp [hadamard2, ryBridgeCore, Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_two, diag2]
    rw [exp_half_pos, exp_half_neg]
    ring_nf
    rw [inv_sqrt_two_sq]
    ring
  · rw [rz_neg_eq]
    simp [hadamard2, ryBridgeCore, Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_two, diag2]
    rw [exp_half_pos, exp_half_neg]
    ring_nf
    rw [inv_sqrt_two_sq]
    ring
  · rw [rz_neg_eq]
    simp [hadamard2, ryBridgeCore, Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_two, diag2]
    rw [exp_half_pos, exp_half_neg]
    ring_nf
    rw [inv_sqrt_two_sq]
    ring

private lemma phaseSdagger_mul_core_mul_phaseS_eq_ry (θ : ℝ) :
    phaseSdagger * ryBridgeCore θ * phaseS = CosineSine.ry θ := by
  have hhalf : ((θ : ℂ) * (2⁻¹ : ℂ)) = ((θ : ℂ) / 2) := by
    ring
  ext i j
  fin_cases i <;> fin_cases j
  · simp [phaseS, phaseSdagger, ryBridgeCore, CosineSine.ry, Matrix.mul_apply, Fin.sum_univ_two, diag2]
    rw [hhalf]
  · simp [phaseS, phaseSdagger, ryBridgeCore, CosineSine.ry, Matrix.mul_apply, Fin.sum_univ_two, diag2]
    rw [hhalf]
    calc
      Complex.sin (↑θ / 2) * Complex.I * Complex.I
          = (Complex.I * Complex.I) * Complex.sin (↑θ / 2) := by ring
        _ = -Complex.sin (↑θ / 2) := by simp
  · simp [phaseS, phaseSdagger, ryBridgeCore, CosineSine.ry, Matrix.mul_apply, Fin.sum_univ_two, diag2]
    rw [hhalf]
    calc
      -(Complex.I * (Complex.sin (↑θ / 2) * Complex.I))
          = -((Complex.I * Complex.I) * Complex.sin (↑θ / 2)) := by ring
        _ = Complex.sin (↑θ / 2) := by simp
  · simp [phaseS, phaseSdagger, ryBridgeCore, CosineSine.ry, Matrix.mul_apply, Fin.sum_univ_two, diag2]
    rw [hhalf]
    calc
      -(Complex.I * Complex.cos (↑θ / 2) * Complex.I)
          = -((Complex.I * Complex.I) * Complex.cos (↑θ / 2)) := by ring
        _ = Complex.cos (↑θ / 2) := by simp

private noncomputable def unitCircleOfNormOne (z : ℂ) (hz : ‖z‖ = 1) : Circle :=
  ⟨z, mem_sphere_zero_iff_norm.2 hz⟩

private lemma complex_eq_exp_arg_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) :
    z = Complex.exp (Complex.arg (unitCircleOfNormOne z hz : ℂ) * Complex.I) := by
  change ((unitCircleOfNormOne z hz : Circle) : ℂ) =
      ((Circle.exp (Complex.arg (unitCircleOfNormOne z hz : ℂ)) : Circle) : ℂ)
  exact congrArg ((↑) : Circle → ℂ) (Circle.exp_arg (unitCircleOfNormOne z hz)).symm

private lemma diag4_mul_diag4 (a b c d e f g h : ℂ) :
    diag4 a b c d * diag4 e f g h = diag4 (a * e) (b * f) (c * g) (d * h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag4, Matrix.mul_apply, Fin.sum_univ_four]

private lemma diag2_mul_diag2 (a b c d : ℂ) :
    diag2 a b * diag2 c d = diag2 (a * c) (b * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag2, Matrix.mul_apply, Fin.sum_univ_two]

private lemma conj_mul_eq_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    star z * z = 1 := by
  calc
    star z * z = (((‖z‖ ^ 2 : ℝ) : ℂ)) := by
      rw [← Complex.normSq_eq_norm_sq]
      simpa using (Complex.normSq_eq_conj_mul_self (z := z)).symm
    _ = 1 := by simp [hz]

private lemma mul_conj_eq_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    z * star z = 1 := by
  simpa [mul_comm] using conj_mul_eq_one_of_norm_eq_one hz

private lemma norm_eq_one_of_conj_mul_eq_one {z : ℂ} (hz : star z * z = 1) :
    ‖z‖ = 1 := by
  have hsq : ‖z‖ ^ 2 = 1 := by
    have hsq_complex : (((‖z‖ ^ 2 : ℝ) : ℂ)) = 1 := by
      calc
        (((‖z‖ ^ 2 : ℝ) : ℂ)) = star z * z := by
          rw [← Complex.normSq_eq_norm_sq]
          simpa using (Complex.normSq_eq_conj_mul_self (z := z))
        _ = 1 := hz
    exact_mod_cast hsq_complex
  nlinarith [norm_nonneg z]

private lemma rz_unitary (θ : ℝ) :
    rz θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply diag2_unitary
  · simpa [rz, mul_comm, mul_left_comm, mul_assoc] using
      Complex.norm_exp_ofReal_mul_I (-(θ / 2))
  · simpa [rz, mul_comm, mul_left_comm, mul_assoc] using
      Complex.norm_exp_ofReal_mul_I (θ / 2)

private lemma exp_neg_I_half (θ : ℝ) :
    Complex.exp (-Complex.I * (θ / 2 : ℂ)) =
      Complex.exp (((-θ) / 2 : ℝ) * Complex.I) := by
  congr 1
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

private lemma exp_pos_I_half (θ : ℝ) :
    Complex.exp (Complex.I * (θ / 2 : ℂ)) =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) := by
  congr 1
  simp [mul_comm]

private lemma ry_mulVec_ket0 (β : ℝ) :
    (CosineSine.ry β).mulVec ket0 =
      ![((Real.cos (β / 2)) : ℂ), ((Real.sin (β / 2)) : ℂ)] := by
  ext i
  fin_cases i <;> simp [CosineSine.ry, ket0, Matrix.mulVec, Fin.sum_univ_two]

private lemma rz_mul_ry_mulVec_ket0 (α β : ℝ) :
    (rz α * CosineSine.ry β).mulVec ket0 =
      ![Complex.exp (((-α) / 2) * Complex.I) * ((Real.cos (β / 2)) : ℂ),
        Complex.exp ((α / 2) * Complex.I) * ((Real.sin (β / 2)) : ℂ)] := by
  calc
    (rz α * CosineSine.ry β).mulVec ket0
        = (rz α).mulVec ((CosineSine.ry β).mulVec ket0) := by
            simpa using (Matrix.mulVec_mulVec (rz α) (CosineSine.ry β) ket0)
    _ = ![Complex.exp (((-α) / 2) * Complex.I) * ((Real.cos (β / 2)) : ℂ),
          Complex.exp ((α / 2) * Complex.I) * ((Real.sin (β / 2)) : ℂ)] := by
          rw [ry_mulVec_ket0]
          ext i
          fin_cases i
          · rw [rz, Matrix.mulVec, diag2, exp_neg_I_half α]
            simp [Fin.sum_univ_two]
          · rw [rz, Matrix.mulVec, diag2, exp_pos_I_half α]
            simp [Fin.sum_univ_two]

private lemma qubit_prepare_rz_ry (ψ : Vec 2) (hψ : IsQubit ψ) :
    ∃ α β : ℝ, ∃ z : ℂ, ‖z‖ = 1 ∧
      (rz α * CosineSine.ry β).mulVec ket0 = z • ψ := by
  let a : ℂ := ψ 0
  let b : ℂ := ψ 1
  have hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
    simpa [a, b, IsQubit, Fin.sum_univ_two] using hψ
  have ha_ge_neg_one : -1 ≤ ‖a‖ := by
    nlinarith [norm_nonneg a]
  have ha_le_one : ‖a‖ ≤ 1 := by
    nlinarith [hnorm, sq_nonneg ‖b‖]
  have hcos : Real.cos ((2 * Real.arccos ‖a‖) / 2) = ‖a‖ := by
    rw [show ((2 * Real.arccos ‖a‖) / 2 : ℝ) = Real.arccos ‖a‖ by ring]
    exact Real.cos_arccos ha_ge_neg_one ha_le_one
  have hsin : Real.sin ((2 * Real.arccos ‖a‖) / 2) = ‖b‖ := by
    rw [show ((2 * Real.arccos ‖a‖) / 2 : ℝ) = Real.arccos ‖a‖ by ring, Real.sin_arccos]
    have hsq : 1 - ‖a‖ ^ 2 = ‖b‖ ^ 2 := by nlinarith [hnorm]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg b)]
  have harg_a : a = ((‖a‖ : ℂ) * Complex.exp (Complex.arg a * Complex.I)) := by
    simpa [mul_comm] using (Complex.norm_mul_exp_arg_mul_I a).symm
  have harg_b : b = ((‖b‖ : ℂ) * Complex.exp (Complex.arg b * Complex.I)) := by
    simpa [mul_comm] using (Complex.norm_mul_exp_arg_mul_I b).symm
  let α : ℝ := Complex.arg b - Complex.arg a
  let β : ℝ := 2 * Real.arccos ‖a‖
  let z : ℂ := Complex.exp ((-(Complex.arg a + Complex.arg b)) / 2 * Complex.I)
  have hz_a_expand :
      z * a = z * (((‖a‖ : ℂ) * Complex.exp (Complex.arg a * Complex.I))) := by
    exact congrArg (fun x => z * x) harg_a
  have hz_b_expand :
      z * b = z * (((‖b‖ : ℂ) * Complex.exp (Complex.arg b * Complex.I))) := by
    exact congrArg (fun x => z * x) harg_b
  have hz_a :
      z * a = Complex.exp (((-α) / 2) * Complex.I) * ((‖a‖ : ℂ)) := by
    calc
      z * a = z * (((‖a‖ : ℂ) * Complex.exp (Complex.arg a * Complex.I))) := hz_a_expand
      _ = Complex.exp ((-(Complex.arg a + Complex.arg b)) / 2 * Complex.I) *
            (((‖a‖ : ℂ) * Complex.exp (Complex.arg a * Complex.I))) := by
            rfl
      _ = ((‖a‖ : ℂ)) *
            (Complex.exp ((-(Complex.arg a + Complex.arg b)) / 2 * Complex.I) *
              Complex.exp (Complex.arg a * Complex.I)) := by
            ring
      _ = ((‖a‖ : ℂ)) *
            Complex.exp (((( -(Complex.arg a + Complex.arg b)) / 2) + Complex.arg a) * Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            ring
      _ = ((‖a‖ : ℂ)) * Complex.exp (((-α) / 2) * Complex.I) := by
            have hαa :
                (((-(Complex.arg a + Complex.arg b)) / 2) + Complex.arg a : ℝ) = (-α) / 2 := by
              dsimp [α]
              ring
            have hαaC :
                (((( -(Complex.arg a + Complex.arg b)) / 2) + Complex.arg a : ℝ) : ℂ) * Complex.I =
                  (((-α) / 2 : ℝ) : ℂ) * Complex.I := by
              exact congrArg (fun x : ℂ => x * Complex.I) (by exact_mod_cast hαa)
            congr 1
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              congrArg Complex.exp hαaC
      _ = Complex.exp (((-α) / 2) * Complex.I) * ((‖a‖ : ℂ)) := by
            ring
  have hz_b :
      z * b = Complex.exp ((α / 2) * Complex.I) * ((‖b‖ : ℂ)) := by
    calc
      z * b = z * (((‖b‖ : ℂ) * Complex.exp (Complex.arg b * Complex.I))) := hz_b_expand
      _ = Complex.exp ((-(Complex.arg a + Complex.arg b)) / 2 * Complex.I) *
            (((‖b‖ : ℂ) * Complex.exp (Complex.arg b * Complex.I))) := by
            rfl
      _ = ((‖b‖ : ℂ)) *
            (Complex.exp ((-(Complex.arg a + Complex.arg b)) / 2 * Complex.I) *
              Complex.exp (Complex.arg b * Complex.I)) := by
            ring
      _ = ((‖b‖ : ℂ)) *
            Complex.exp (((( -(Complex.arg a + Complex.arg b)) / 2) + Complex.arg b) * Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            ring
      _ = ((‖b‖ : ℂ)) * Complex.exp ((α / 2) * Complex.I) := by
            have hαb :
                (((-(Complex.arg a + Complex.arg b)) / 2) + Complex.arg b : ℝ) = α / 2 := by
              dsimp [α]
              ring
            have hαbC :
                (((( -(Complex.arg a + Complex.arg b)) / 2) + Complex.arg b : ℝ) : ℂ) * Complex.I =
                  ((α / 2 : ℝ) : ℂ) * Complex.I := by
              exact congrArg (fun x : ℂ => x * Complex.I) (by exact_mod_cast hαb)
            congr 1
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              congrArg Complex.exp hαbC
      _ = Complex.exp ((α / 2) * Complex.I) * ((‖b‖ : ℂ)) := by
            ring
  refine ⟨α, β, z, ?_, ?_⟩
  · simpa [z] using Complex.norm_exp_ofReal_mul_I ((-(Complex.arg a + Complex.arg b)) / 2)
  · rw [rz_mul_ry_mulVec_ket0]
    ext i
    fin_cases i
    · rw [show Real.cos (β / 2) = ‖a‖ by simpa [β] using hcos]
      change Complex.exp (((-α) / 2) * Complex.I) * ((‖a‖ : ℂ)) = z * a
      exact hz_a.symm
    · rw [show Real.sin (β / 2) = ‖b‖ by simpa [β] using hsin]
      change Complex.exp ((α / 2) * Complex.I) * ((‖b‖ : ℂ)) = z * b
      exact hz_b.symm

@[simp] private lemma mulVec_ket0_entry (D : Square 2) (i : Fin 2) :
    D.mulVec ket0 i = D i 0 := by
  rw [show ket0 = Pi.single 0 1 by
    ext j
    fin_cases j <;> simp [ket0]]
  rw [Matrix.mulVec_single_one]
  rfl

@[simp] private lemma mulVec_ket1_entry (D : Square 2) (i : Fin 2) :
    D.mulVec ket1 i = D i 1 := by
  rw [show ket1 = Pi.single 1 1 by
    ext j
    fin_cases j <;> simp [ket1]]
  rw [Matrix.mulVec_single_one]
  rfl

private lemma unitary_first_column_scalar_is_diag (D : Square 2)
    (hD : D ∈ Matrix.unitaryGroup (Fin 2) ℂ) (phase : ℂ)
    (h0 : D.mulVec ket0 = phase • ket0) :
    ∃ μ : ℂ, ‖phase‖ = 1 ∧ ‖μ‖ = 1 ∧ D = diag2 phase μ := by
  have hPhaseSq : star phase * phase = 1 := by
    have hcol0 := GateHelpers.unitary_column0_norm D hD
    rw [h0] at hcol0
    simpa [ket0] using hcol0
  have hPhaseNorm : ‖phase‖ = 1 := norm_eq_one_of_conj_mul_eq_one hPhaseSq
  have hPhaseNe : phase ≠ 0 := by
    intro hzero
    rw [hzero] at hPhaseNorm
    norm_num at hPhaseNorm
  have hstarPhaseNe : star phase ≠ 0 := by
    intro hzero
    apply hPhaseNe
    simpa using congrArg star hzero
  have horth := GateHelpers.unitary_columns_orthogonal_right D hD
  rw [h0] at horth
  have h01 : (D.mulVec ket1) 0 = 0 := by
    have htmp : star phase * (D.mulVec ket1) 0 = 0 := by
      simpa [ket0] using horth
    exact (mul_eq_zero.mp htmp).resolve_left hstarPhaseNe
  have h00 : D 0 0 = phase := by
    simpa [Matrix.mulVec, ket0, Fin.sum_univ_two] using congrFun h0 0
  have h10 : D 1 0 = 0 := by
    simpa [Matrix.mulVec, ket0, Fin.sum_univ_two] using congrFun h0 1
  have h01entry : D 0 1 = 0 := by
    simpa [Matrix.mulVec, ket1, Fin.sum_univ_two] using h01
  let μ : ℂ := D 1 1
  have hμsq : star μ * μ = 1 := by
    have hcol1 := GateHelpers.unitary_column1_norm D hD
    simpa [μ, h01entry] using hcol1
  have hμnorm : ‖μ‖ = 1 := norm_eq_one_of_conj_mul_eq_one hμsq
  refine ⟨μ, hPhaseNorm, hμnorm, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [diag2] using h00
  · simpa [diag2] using h01entry
  · simpa [diag2] using h10
  · simp [μ, diag2]

private lemma diag2_eq_global_phase_rz (phase μ : ℂ)
    (hPhase : ‖phase‖ = 1) (hμ : ‖μ‖ = 1) :
    ∃ γ : ℝ, ∃ z : ℂ, ‖z‖ = 1 ∧ diag2 phase μ = z • rz γ := by
  let w : ℂ := star phase * μ
  have hPhaseStar : ‖star phase‖ = 1 := by simpa using hPhase
  have hw : ‖w‖ = 1 := by
    calc
      ‖w‖ = ‖star phase * μ‖ := by rfl
      _ = ‖star phase‖ * ‖μ‖ := by rw [norm_mul]
      _ = 1 := by rw [hPhaseStar, hμ]; norm_num
  let γ : ℝ := Complex.arg w
  let z : ℂ := phase * Complex.exp ((γ / 2) * Complex.I)
  have hwexp : Complex.exp (γ * Complex.I) = w := by
    simpa [γ, hw] using Complex.norm_mul_exp_arg_mul_I w
  have hPhaseMul : phase * star phase = 1 := mul_conj_eq_one_of_norm_eq_one hPhase
  have hμeq : μ = phase * w := by
    calc
      μ = 1 * μ := by simp
      _ = (phase * star phase) * μ := by rw [hPhaseMul]
      _ = phase * (star phase * μ) := by ring
      _ = phase * w := by rfl
  refine ⟨γ, z, ?_, ?_⟩
  · calc
      ‖z‖ = ‖phase * Complex.exp ((γ / 2) * Complex.I)‖ := by rfl
      _ = ‖phase‖ * ‖Complex.exp ((γ / 2) * Complex.I)‖ := by rw [norm_mul]
      _ = 1 * 1 := by
            have hnormExp : ‖Complex.exp ((γ : ℂ) / 2 * Complex.I)‖ = 1 := by
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
                Complex.norm_exp_ofReal_mul_I (γ / 2)
            rw [hPhase, hnormExp]
      _ = 1 := by norm_num
  · ext i j
    fin_cases i <;> fin_cases j
    · change phase = z * Complex.exp (-Complex.I * (γ / 2))
      dsimp [z]
      calc
        phase = phase * Complex.exp (0 : ℂ) := by simp
        _ = phase * (Complex.exp ((γ / 2) * Complex.I) * Complex.exp (-Complex.I * (γ / 2))) := by
              congr 1
              rw [← Complex.exp_add]
              congr 1
              ring
        _ = phase * Complex.exp ((γ / 2) * Complex.I) * Complex.exp (-Complex.I * (γ / 2)) := by
              simp [mul_assoc]
    · simp [rz, diag2]
    · simp [rz, diag2]
    · change μ = z * Complex.exp (Complex.I * (γ / 2))
      dsimp [z]
      calc
        μ = phase * w := hμeq
        _ = phase * Complex.exp (γ * Complex.I) := by rw [← hwexp]
        _ = phase * (Complex.exp ((γ / 2) * Complex.I) * Complex.exp (Complex.I * (γ / 2))) := by
              congr 1
              rw [← Complex.exp_add]
              congr 1
              ring
        _ = phase * Complex.exp ((γ / 2) * Complex.I) * Complex.exp (Complex.I * (γ / 2)) := by
              simp [mul_assoc]

private lemma controlledGate_rz_eq (α : ℝ) :
    controlledGate (rz α) =
      diag4 1 1 (Complex.exp (-Complex.I * (α / 2))) (Complex.exp (Complex.I * (α / 2))) := by
  rw [rz, controlledGate_diag2_eq]

private lemma localOnFirst_phaseShift_eq (φ : ℝ) :
    localOnFirst (phaseShift φ) =
      diag4 1 1 (Complex.exp (Complex.I * φ)) (Complex.exp (Complex.I * φ)) := by
  rw [localOnFirst, phaseShift, DiagonalizationHelpers.diag2_one_right_kron]

private lemma localOnFirst_rz_eq (θ : ℝ) :
    localOnFirst (rz θ) =
      diag4 (Complex.exp (((-θ) / 2) * Complex.I))
        (Complex.exp (((-θ) / 2) * Complex.I))
        (Complex.exp ((θ / 2) * Complex.I))
        (Complex.exp ((θ / 2) * Complex.I)) := by
  have hneg : Complex.exp (-Complex.I * (θ / 2 : ℂ)) =
      Complex.exp (((-θ) / 2 : ℝ) * Complex.I) := by
    congr 1
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  have hpos : Complex.exp (Complex.I * (θ / 2 : ℂ)) =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) := by
    congr 1
    simp [mul_comm]
  rw [localOnFirst, rz, hneg, hpos, ← diag2_one_one]
  simpa using
    (diag2_kron_diag2
      (Complex.exp (((-θ) / 2) * Complex.I))
      (Complex.exp ((θ / 2) * Complex.I))
      (1 : ℂ) (1 : ℂ))

private lemma localOnSecond_mul_blockDiag2 (Q A B : Square 2) :
    localOnSecond Q * CosineSine.blockDiag2 A B =
      CosineSine.blockDiag2 (Q * A) (Q * B) := by
  rw [localOnSecond, CosineSine.blockDiag2, Matrix.mul_add]
  rw [← kron_mul_two, ← kron_mul_two]
  simp [CosineSine.blockDiag2]

private lemma blockDiag2_mul_localOnSecond (A B P : Square 2) :
    CosineSine.blockDiag2 A B * localOnSecond P =
      CosineSine.blockDiag2 (A * P) (B * P) := by
  rw [localOnSecond, CosineSine.blockDiag2, Matrix.add_mul]
  rw [← kron_mul_two, ← kron_mul_two]
  simp [CosineSine.blockDiag2]

private lemma localOnSecond_mul_blockDiag2_mul_localOnSecond (Q A B P : Square 2) :
    localOnSecond Q * CosineSine.blockDiag2 A B * localOnSecond P =
      CosineSine.blockDiag2 (Q * A * P) (Q * B * P) := by
  calc
    localOnSecond Q * CosineSine.blockDiag2 A B * localOnSecond P
        = localOnSecond Q * (CosineSine.blockDiag2 A B * localOnSecond P) := by
            simp [mul_assoc]
    _ = localOnSecond Q * CosineSine.blockDiag2 (A * P) (B * P) := by
      rw [blockDiag2_mul_localOnSecond]
    _ = CosineSine.blockDiag2 (Q * (A * P)) (Q * (B * P)) := by
      rw [localOnSecond_mul_blockDiag2]
    _ = CosineSine.blockDiag2 (Q * A * P) (Q * B * P) := by
      simp [mul_assoc]

private lemma proj0_eq_diag2 : proj0 = diag2 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, ketbra, ket0, diag2]

private lemma proj1_eq_diag2 : proj1 = diag2 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, ketbra, ket1, diag2]

private lemma blockDiag2_diag2_eq_diag4 (a b c d : ℂ) :
    CosineSine.blockDiag2 (diag2 a b) (diag2 c d) = diag4 a b c d := by
  rw [CosineSine.blockDiag2, proj0_eq_diag2, proj1_eq_diag2, diag2_kron_diag2, diag2_kron_diag2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag4]

private lemma controlledRzPair_eq_diag4 (α₀ α₁ : ℝ) :
    controlledRzPair α₀ α₁ =
      diag4 (Complex.exp (((-α₀) / 2) * Complex.I))
        (Complex.exp (((-α₁) / 2) * Complex.I))
        (Complex.exp ((α₀ / 2) * Complex.I))
        (Complex.exp ((α₁ / 2) * Complex.I)) := by
  have hneg₀ : Complex.exp (-Complex.I * (α₀ / 2 : ℂ)) =
      Complex.exp (((-α₀) / 2 : ℝ) * Complex.I) := by
    congr 1
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  have hneg₁ : Complex.exp (-Complex.I * (α₁ / 2 : ℂ)) =
      Complex.exp (((-α₁) / 2 : ℝ) * Complex.I) := by
    congr 1
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  rw [controlledRzPair, proj0_eq_diag2, proj1_eq_diag2, rz, rz, hneg₀, hneg₁]
  rw [diag2_kron_diag2, diag2_kron_diag2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag4, mul_comm]

private lemma controlledRzPair_eq_blockDiag2 (α₀ α₁ : ℝ) :
    controlledRzPair α₀ α₁ =
      CosineSine.blockDiag2
        (diag2 (Complex.exp (((-α₀) / 2) * Complex.I))
          (Complex.exp (((-α₁) / 2) * Complex.I)))
        (diag2 (Complex.exp ((α₀ / 2) * Complex.I))
          (Complex.exp ((α₁ / 2) * Complex.I))) := by
  rw [controlledRzPair_eq_diag4, blockDiag2_diag2_eq_diag4]

private lemma localOnFirst_mul (A B : Square 2) :
    localOnFirst A * localOnFirst B = localOnFirst (A * B) := by
  unfold localOnFirst
  rw [← kron_mul_two]
  simp

private lemma localOnFirst_mul_controlledRzPair_mul_localOnFirst
    (A B : Square 2) (α₀ α₁ : ℝ) :
    localOnFirst A * controlledRzPair α₀ α₁ * localOnFirst B =
      (A * rz α₀ * B) ⊗ₖ proj0 + (A * rz α₁ * B) ⊗ₖ proj1 := by
  unfold localOnFirst controlledRzPair
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [← kron_mul_two, ← kron_mul_two, ← kron_mul_two, ← kron_mul_two]
  simp [mul_assoc]

/-- Clifford-paper Lemma 3. -/
theorem lemma3_ry_via_rz (θ : ℝ) :
  CosineSine.ry θ = phaseSdagger * hadamard2 * rz (-θ) * hadamard2 * phaseS := by
  calc
    CosineSine.ry θ = phaseSdagger * ryBridgeCore θ * phaseS := by
      symm
      exact phaseSdagger_mul_core_mul_phaseS_eq_ry θ
    _ = phaseSdagger * (hadamard2 * rz (-θ) * hadamard2) * phaseS := by
      rw [← hadamard_mul_rz_neg_mul_hadamard_eq_core θ]
    _ = phaseSdagger * hadamard2 * rz (-θ) * hadamard2 * phaseS := by
      simp [mul_assoc]

private lemma conditionalRy_eq_local_controlledRz (θ₀ θ₁ : ℝ) :
    CosineSine.conditionalRy θ₀ θ₁ =
      localOnFirst (phaseSdagger * hadamard2) *
        controlledRzPair (-θ₀) (-θ₁) *
        localOnFirst (hadamard2 * phaseS) := by
  symm
  calc
    localOnFirst (phaseSdagger * hadamard2) *
          controlledRzPair (-θ₀) (-θ₁) *
          localOnFirst (hadamard2 * phaseS)
        =
          (phaseSdagger * hadamard2 * rz (-θ₀) * (hadamard2 * phaseS)) ⊗ₖ proj0 +
          (phaseSdagger * hadamard2 * rz (-θ₁) * (hadamard2 * phaseS)) ⊗ₖ proj1 := by
            rw [localOnFirst_mul_controlledRzPair_mul_localOnFirst]
    _ =
          (phaseSdagger * hadamard2 * rz (-θ₀) * hadamard2 * phaseS) ⊗ₖ proj0 +
          (phaseSdagger * hadamard2 * rz (-θ₁) * hadamard2 * phaseS) ⊗ₖ proj1 := by
            simp [mul_assoc]
    _ = CosineSine.conditionalRy θ₀ θ₁ := by
          rw [← lemma3_ry_via_rz θ₀, ← lemma3_ry_via_rz θ₁]
          rfl

private lemma phaseT_sq_eq_phaseS :
    phaseT * phaseT = phaseS := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [phaseT, phaseS, diag2, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [phaseT, phaseS, diag2, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [phaseT, phaseS, diag2, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [phaseT, phaseS, diag2, Matrix.mul_apply, Fin.sum_univ_two]
    calc
      Complex.exp (Complex.I * (Real.pi / 4)) * Complex.exp (Complex.I * (Real.pi / 4))
          = Complex.exp (Real.pi / 2 * Complex.I) := by
              rw [← Complex.exp_add]
              congr 1
              ring
      _ = Complex.I := by simpa [mul_comm] using Complex.exp_pi_div_two_mul_I

private lemma phaseS_cubed_eq_phaseSdagger :
    phaseS * phaseS * phaseS = phaseSdagger := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseS, phaseSdagger, diag2, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

private lemma phaseT_six_eq_phaseSdagger :
    phaseT * phaseT * phaseT * phaseT * phaseT * phaseT = phaseSdagger := by
  calc
    phaseT * phaseT * phaseT * phaseT * phaseT * phaseT
        = phaseS * phaseS * phaseS := by
            simpa [phaseT_sq_eq_phaseS, mul_assoc] using
              (show phaseT * phaseT * phaseT * phaseT * phaseT * phaseT =
                  (phaseT * phaseT) * ((phaseT * phaseT) * (phaseT * phaseT)) by
                    simp [mul_assoc])
    _ = phaseSdagger := phaseS_cubed_eq_phaseSdagger

private noncomputable def standardRyGates (θ : ℝ) : List OneQubitPrimitive :=
  [.t, .t, .t, .t, .t, .t, .h, .rz (-θ), .h, .t, .t]

private lemma standardRyGates_matrix (θ : ℝ) :
    oneQubitCircuitMatrix (standardRyGates θ) = CosineSine.ry θ := by
  calc
    oneQubitCircuitMatrix (standardRyGates θ)
        = (phaseT * phaseT * phaseT * phaseT * phaseT * phaseT) *
            hadamard2 * rz (-θ) * hadamard2 * (phaseT * phaseT) := by
              simp [standardRyGates, oneQubitCircuitMatrix, OneQubitPrimitive.eval, mul_assoc]
    _ = phaseSdagger * hadamard2 * rz (-θ) * hadamard2 * phaseS := by
          rw [phaseT_six_eq_phaseSdagger, phaseT_sq_eq_phaseS]
    _ = CosineSine.ry θ := by
          symm
          exact lemma3_ry_via_rz θ

/-- Two-qubit specialization of Clifford-paper Lemma 4. -/
theorem lemma4_demultiplex_two_qubit (V₀ V₁ : Square 2)
    (hV₀ : V₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hV₁ : V₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (P Q : Square 2) (α₀ α₁ : ℝ),
      P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      CosineSine.blockDiag2 V₀ V₁ =
        localOnSecond Q * controlledRzPair α₀ α₁ * localOnSecond P := by
  have hRel : V₁ * V₀† ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    exact Submonoid.mul_mem _ hV₁ (conjTranspose_mem_unitaryGroup hV₀)
  rcases unitary_diag2_exists (V₁ * V₀†) hRel with ⟨u₀, u₁, Q, hu₀, hu₁, hQ, hQdiag⟩
  let z₀ : Circle := unitCircleOfNormOne u₀ hu₀
  let z₁ : Circle := unitCircleOfNormOne u₁ hu₁
  let α₀ : ℝ := Complex.arg (z₀ : ℂ)
  let α₁ : ℝ := Complex.arg (z₁ : ℂ)
  let D₀ : Square 2 :=
    diag2 (Complex.exp (((-α₀) / 2) * Complex.I)) (Complex.exp (((-α₁) / 2) * Complex.I))
  let D₁ : Square 2 :=
    diag2 (Complex.exp ((α₀ / 2) * Complex.I)) (Complex.exp ((α₁ / 2) * Complex.I))
  let P : Square 2 := D₀† * Q† * V₀
  have hu₀exp : u₀ = Complex.exp (α₀ * Complex.I) := by
    simpa [z₀, α₀] using complex_eq_exp_arg_of_norm_one u₀ hu₀
  have hu₁exp : u₁ = Complex.exp (α₁ * Complex.I) := by
    simpa [z₁, α₁] using complex_eq_exp_arg_of_norm_one u₁ hu₁
  have hD₀ : D₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    refine diag2_unitary _ _ ?_ ?_
    · simpa [D₀] using Complex.norm_exp_ofReal_mul_I ((-α₀) / 2)
    · simpa [D₀] using Complex.norm_exp_ofReal_mul_I ((-α₁) / 2)
  have hP : P ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    exact Submonoid.mul_mem _
      (Submonoid.mul_mem _ (conjTranspose_mem_unitaryGroup hD₀) (conjTranspose_mem_unitaryGroup hQ))
      hV₀
  have hD₀right : D₀ * D₀† = (1 : Square 2) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hD₀)
  have hQright : Q * Q† = (1 : Square 2) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hQ)
  have hV₀left : V₀† * V₀ = (1 : Square 2) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hV₀)
  have hQdagV₀' : D₀ * P = Q† * V₀ := by
    calc
      D₀ * P = D₀ * (D₀† * Q† * V₀) := by rfl
      _ = (D₀ * D₀†) * Q† * V₀ := by simp [mul_assoc]
      _ = Q† * V₀ := by rw [hD₀right]; simp
  have hQdagV₀ : Q† * V₀ = D₀ * P := hQdagV₀'.symm
  have hV₀eq' : Q * D₀ * P = V₀ := by
    calc
      Q * D₀ * P = Q * (D₀ * P) := by simp [mul_assoc]
      _ = Q * (Q† * V₀) := by rw [hQdagV₀]
      _ = (Q * Q†) * V₀ := by simp [mul_assoc]
      _ = V₀ := by rw [hQright]; simp
  have hV₀eq : V₀ = Q * D₀ * P := hV₀eq'.symm
  have hDiagStep : diag2 u₀ u₁ * D₀ = D₁ := by
    ext i j
    fin_cases i <;> fin_cases j
    · rw [hu₀exp]
      simp [D₀, D₁, diag2]
      rw [← Complex.exp_add]
      congr 1
      ring
    · simp [D₀, D₁, diag2]
    · simp [D₀, D₁, diag2]
    · rw [hu₁exp]
      simp [D₀, D₁, diag2]
      rw [← Complex.exp_add]
      congr 1
      ring
  have hV₁eq' : Q * D₁ * P = V₁ := by
    calc
      Q * D₁ * P = Q * (diag2 u₀ u₁ * D₀) * P := by rw [← hDiagStep]
      _ = Q * diag2 u₀ u₁ * (D₀ * P) := by simp [mul_assoc]
      _ = Q * diag2 u₀ u₁ * (Q† * V₀) := by rw [hQdagV₀]
      _ = (Q * diag2 u₀ u₁ * Q†) * V₀ := by simp [mul_assoc]
      _ = (V₁ * V₀†) * V₀ := by rw [hQdiag]
      _ = V₁ * (V₀† * V₀) := by simp [mul_assoc]
      _ = V₁ := by rw [hV₀left]; simp
  have hV₁eq : V₁ = Q * D₁ * P := hV₁eq'.symm
  refine ⟨P, Q, α₀, α₁, hP, hQ, ?_⟩
  calc
    CosineSine.blockDiag2 V₀ V₁ = CosineSine.blockDiag2 (Q * D₀ * P) (Q * D₁ * P) := by
      rw [hV₀eq, hV₁eq]
    _ = localOnSecond Q * controlledRzPair α₀ α₁ * localOnSecond P := by
      symm
      rw [controlledRzPair_eq_blockDiag2, localOnSecond_mul_blockDiag2_mul_localOnSecond]

/-- Exact one-qubit diagonalization, reusing the repo's existing helper theorem. -/
theorem one_qubit_diagonalization (U : Square 2)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (u₀ u₁ : ℂ) (V : Square 2),
      ‖u₀‖ = 1 ∧
      ‖u₁‖ = 1 ∧
      V ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      U = V * diag2 u₀ u₁ * V† := by
  simpa using unitary_diag2_exists U hU

/-- Paper-facing controlled-diagonal factorization from `lemmadiag`. -/
theorem controlled_diag_via_phase_and_controlled_rz (d₀ d₁ : ℂ)
    (hd₀ : ‖d₀‖ = 1) (hd₁ : ‖d₁‖ = 1) :
    ∃ (φ α : ℝ),
      controlledGate (diag2 d₀ d₁) =
        controlledGate (rz α) * localOnFirst (phaseShift φ) := by
  let z₀ : Circle := unitCircleOfNormOne d₀ hd₀
  let z₁ : Circle := unitCircleOfNormOne d₁ hd₁
  let φ : ℝ := (Complex.arg (z₀ : ℂ) + Complex.arg (z₁ : ℂ)) / 2
  let α : ℝ := Complex.arg (z₁ : ℂ) - Complex.arg (z₀ : ℂ)
  refine ⟨φ, α, ?_⟩
  have hd₀exp : d₀ = Complex.exp (Complex.arg (z₀ : ℂ) * Complex.I) := by
    simpa [z₀, unitCircleOfNormOne] using complex_eq_exp_arg_of_norm_one d₀ hd₀
  have hd₁exp : d₁ = Complex.exp (Complex.arg (z₁ : ℂ) * Complex.I) := by
    simpa [z₁, unitCircleOfNormOne] using complex_eq_exp_arg_of_norm_one d₁ hd₁
  have hd₀split :
      Complex.exp (Complex.arg (z₀ : ℂ) * Complex.I) =
        Complex.exp (-Complex.I * (α / 2)) * Complex.exp (Complex.I * φ) := by
    rw [← Complex.exp_add]
    congr 1
    simp [φ, α]
    ring
  have hd₁split :
      Complex.exp (Complex.arg (z₁ : ℂ) * Complex.I) =
        Complex.exp (Complex.I * (α / 2)) * Complex.exp (Complex.I * φ) := by
    rw [← Complex.exp_add]
    congr 1
    simp [φ, α]
    ring
  calc
    controlledGate (diag2 d₀ d₁)
        = diag4 1 1 d₀ d₁ := controlledGate_diag2_eq d₀ d₁
    _ = diag4 1 1
          (Complex.exp (-Complex.I * (α / 2)) * Complex.exp (Complex.I * φ))
          (Complex.exp (Complex.I * (α / 2)) * Complex.exp (Complex.I * φ)) := by
          rw [hd₀exp, hd₁exp, hd₀split, hd₁split]
    _ = controlledGate (rz α) * localOnFirst (phaseShift φ) := by
          rw [controlledGate_rz_eq, localOnFirst_phaseShift_eq, diag4_mul_diag4]
          simp

/-- Exact-synthesis corollary for the special controlled-`R_z` pairs used in Lemma 11. -/
theorem controlled_rz_pair_uses_standard_gates (α₀ α₁ : ℝ) :
    ∃ gates : List TwoQubitPrimitive,
      twoQubitCircuitMatrix gates = controlledRzPair α₀ α₁ := by
  let beta : ℝ := (α₀ - α₁) / 2
  let gamma : ℝ := (α₀ + α₁) / 2
  refine ⟨[TwoQubitPrimitive.cnot,
      TwoQubitPrimitive.onFirst (OneQubitPrimitive.rz beta),
      TwoQubitPrimitive.cnot,
      TwoQubitPrimitive.onFirst (OneQubitPrimitive.rz gamma)], ?_⟩
  have hconj :
      cnot * localOnFirst (rz beta) * cnot =
        diag4 (Complex.exp (((-beta) / 2) * Complex.I))
          (Complex.exp ((beta / 2) * Complex.I))
          (Complex.exp ((beta / 2) * Complex.I))
          (Complex.exp (((-beta) / 2) * Complex.I)) := by
    calc
      cnot * localOnFirst (rz beta) * cnot
          = cnot *
              diag4 (Complex.exp (((-beta) / 2) * Complex.I))
                (Complex.exp (((-beta) / 2) * Complex.I))
                (Complex.exp ((beta / 2) * Complex.I))
                (Complex.exp ((beta / 2) * Complex.I)) * cnot := by
              rw [localOnFirst_rz_eq]
      _ = diag4 (Complex.exp (((-beta) / 2) * Complex.I))
            (Complex.exp ((beta / 2) * Complex.I))
            (Complex.exp ((beta / 2) * Complex.I))
            (Complex.exp (((-beta) / 2) * Complex.I)) := by
            simpa [cnot, GateHelpers.notc_conjTranspose] using
              (GateHelpers.notc_conj_diag4
                (Complex.exp (((-beta) / 2) * Complex.I))
                (Complex.exp (((-beta) / 2) * Complex.I))
                (Complex.exp ((beta / 2) * Complex.I))
                (Complex.exp ((beta / 2) * Complex.I)))
  calc
    twoQubitCircuitMatrix [TwoQubitPrimitive.cnot,
        TwoQubitPrimitive.onFirst (OneQubitPrimitive.rz beta),
        TwoQubitPrimitive.cnot,
        TwoQubitPrimitive.onFirst (OneQubitPrimitive.rz gamma)]
        = cnot * localOnFirst (rz beta) * cnot * localOnFirst (rz gamma) := by
            simp [twoQubitCircuitMatrix, TwoQubitPrimitive.eval, OneQubitPrimitive.eval, mul_assoc]
    _ = diag4 (Complex.exp (((-beta) / 2) * Complex.I))
          (Complex.exp ((beta / 2) * Complex.I))
          (Complex.exp ((beta / 2) * Complex.I))
          (Complex.exp (((-beta) / 2) * Complex.I)) *
          diag4 (Complex.exp (((-gamma) / 2) * Complex.I))
            (Complex.exp (((-gamma) / 2) * Complex.I))
            (Complex.exp ((gamma / 2) * Complex.I))
            (Complex.exp ((gamma / 2) * Complex.I)) := by
          rw [hconj, localOnFirst_rz_eq]
    _ = diag4
          (Complex.exp (((-beta) / 2) * Complex.I) * Complex.exp (((-gamma) / 2) * Complex.I))
          (Complex.exp ((beta / 2) * Complex.I) * Complex.exp (((-gamma) / 2) * Complex.I))
          (Complex.exp ((beta / 2) * Complex.I) * Complex.exp ((gamma / 2) * Complex.I))
          (Complex.exp (((-beta) / 2) * Complex.I) * Complex.exp ((gamma / 2) * Complex.I)) := by
          rw [diag4_mul_diag4]
    _ = controlledRzPair α₀ α₁ := by
          rw [controlledRzPair_eq_diag4]
          congr
          · rw [← Complex.exp_add]
            congr 1
            simp [beta, gamma]
            ring
          · rw [← Complex.exp_add]
            congr 1
            simp [beta, gamma]
            ring
          · rw [← Complex.exp_add]
            congr 1
            simp [beta, gamma]
            ring
          · rw [← Complex.exp_add]
            congr 1
            simp [beta, gamma]
            ring

def GlobalPhaseEquivalent {n : ℕ} (A B : Square n) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ A = z • B

theorem GlobalPhaseEquivalent.of_eq {n : ℕ} {A B : Square n} (h : A = B) :
    GlobalPhaseEquivalent A B := by
  refine ⟨1, by simp, ?_⟩
  simpa [h]

theorem GlobalPhaseEquivalent.refl {n : ℕ} (A : Square n) :
    GlobalPhaseEquivalent A A :=
  GlobalPhaseEquivalent.of_eq rfl

theorem GlobalPhaseEquivalent.trans {n : ℕ} {A B C : Square n}
    (hAB : GlobalPhaseEquivalent A B) (hBC : GlobalPhaseEquivalent B C) :
    GlobalPhaseEquivalent A C := by
  rcases hAB with ⟨z, hz, hA⟩
  rcases hBC with ⟨w, hw, hB⟩
  refine ⟨z * w, ?_, ?_⟩
  · rw [norm_mul, hz, hw, one_mul]
  · calc
      A = z • B := hA
      _ = z • (w • C) := by rw [hB]
      _ = (z * w) • C := by simp [smul_smul]

theorem GlobalPhaseEquivalent.mul {n : ℕ} {A B C D : Square n}
    (hAC : GlobalPhaseEquivalent A C) (hBD : GlobalPhaseEquivalent B D) :
    GlobalPhaseEquivalent (A * B) (C * D) := by
  rcases hAC with ⟨z, hz, hA⟩
  rcases hBD with ⟨w, hw, hB⟩
  refine ⟨z * w, ?_, ?_⟩
  · rw [norm_mul, hz, hw, one_mul]
  · calc
      A * B = (z • C) * (w • D) := by rw [hA, hB]
      _ = (z * w) • (C * D) := by
            rw [Matrix.smul_mul, Matrix.mul_smul]
            simp [smul_smul]

private lemma localOnFirst_smul (z : ℂ) (A : Square 2) :
    localOnFirst (z • A) = z • localOnFirst A := by
  unfold localOnFirst
  rw [kron_smul_left]

private lemma localOnSecond_smul (z : ℂ) (A : Square 2) :
    localOnSecond (z • A) = z • localOnSecond A := by
  unfold localOnSecond
  rw [KronHelpers.kron_smul_right]

theorem GlobalPhaseEquivalent.localOnFirst {A B : Square 2}
    (hAB : GlobalPhaseEquivalent A B) :
    GlobalPhaseEquivalent (localOnFirst A) (localOnFirst B) := by
  rcases hAB with ⟨z, hz, hA⟩
  refine ⟨z, hz, ?_⟩
  rw [hA, localOnFirst_smul]

theorem GlobalPhaseEquivalent.localOnSecond {A B : Square 2}
    (hAB : GlobalPhaseEquivalent A B) :
    GlobalPhaseEquivalent (localOnSecond A) (localOnSecond B) := by
  rcases hAB with ⟨z, hz, hA⟩
  refine ⟨z, hz, ?_⟩
  rw [hA, localOnSecond_smul]

/-- Derived one-qubit synthesis corollary over `{H, T, R_z(θ)}`, up to global phase. -/
theorem one_qubit_exact_h_t_rz (U : Square 2)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ gates : List OneQubitPrimitive,
      GlobalPhaseEquivalent U (oneQubitCircuitMatrix gates) := by
  let ψ : Vec 2 := U.mulVec ket0
  have hψ : IsQubit ψ := StateHelpers.isQubit_mulVec_of_unitary U hU StateHelpers.isQubit_ket0
  rcases qubit_prepare_rz_ry ψ hψ with ⟨α, β, phase, hPhaseNorm, hprep⟩
  let C : Square 2 := rz α * CosineSine.ry β
  have hC : C ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    dsimp [C]
    exact Submonoid.mul_mem _ (rz_unitary α) (CosineSine.ry_unitary β)
  have hCket0 : C.mulVec ket0 = (rz α).mulVec ((CosineSine.ry β).mulVec ket0) := by
    dsimp [C]
    simpa using (Matrix.mulVec_mulVec (rz α) (CosineSine.ry β) ket0)
  let D : Square 2 := C† * U
  have hD : D ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    dsimp [D]
    exact Submonoid.mul_mem _ (conjTranspose_mem_unitaryGroup hC) hU
  have hPhaseSq : star phase * phase = 1 := conj_mul_eq_one_of_norm_eq_one hPhaseNorm
  have hUcol0 : U.mulVec ket0 = star phase • C.mulVec ket0 := by
    calc
      U.mulVec ket0 = (1 : ℂ) • U.mulVec ket0 := by simp
      _ = (star phase * phase) • U.mulVec ket0 := by rw [hPhaseSq]
      _ = star phase • (phase • U.mulVec ket0) := by simp [smul_smul]
      _ = star phase • C.mulVec ket0 := by rw [← hprep]
  have hDcol0 : D.mulVec ket0 = star phase • ket0 := by
    calc
      D.mulVec ket0 = C†.mulVec (U.mulVec ket0) := by
        dsimp [D]
        rw [Matrix.mulVec_mulVec]
      _ = C†.mulVec (star phase • C.mulVec ket0) := by rw [hUcol0]
      _ = star phase • C†.mulVec (C.mulVec ket0) := by
        rw [Matrix.mulVec_smul]
      _ = star phase • C†.mulVec ((rz α).mulVec ((CosineSine.ry β).mulVec ket0)) := by
        simpa using congrArg (fun v => star phase • C†.mulVec v) hCket0
      _ = star phase • (C† * C).mulVec ket0 := by
        have hmul :
            C†.mulVec ((rz α).mulVec ((CosineSine.ry β).mulVec ket0)) =
              (C† * C).mulVec ket0 := by
          have hinner :
              (rz α).mulVec ((CosineSine.ry β).mulVec ket0) =
                (rz α * CosineSine.ry β).mulVec ket0 := by
            simpa using (Matrix.mulVec_mulVec (rz α) (CosineSine.ry β) ket0).symm
          dsimp [C]
          calc
            (rz α * CosineSine.ry β)†.mulVec ((rz α).mulVec ((CosineSine.ry β).mulVec ket0))
                = (rz α * CosineSine.ry β)†.mulVec ((rz α * CosineSine.ry β).mulVec ket0) := by
                    rw [hinner]
            _ = ((rz α * CosineSine.ry β)† * (rz α * CosineSine.ry β)).mulVec ket0 := by
                  simpa using
                    (Matrix.mulVec_mulVec
                      ((rz α * CosineSine.ry β)†)
                      (rz α * CosineSine.ry β)
                      ket0).symm
        simpa using congrArg (fun v => star phase • v) hmul
      _ = star phase • ket0 := by
        have hleft : C† * C = (1 : Square 2) := Matrix.mem_unitaryGroup_iff'.mp hC
        rw [hleft, Matrix.one_mulVec]
  rcases unitary_first_column_scalar_is_diag D hD (star phase) hDcol0 with ⟨μ, hPhaseDagNorm, hμnorm, hDiag⟩
  rcases diag2_eq_global_phase_rz (star phase) μ hPhaseDagNorm hμnorm with ⟨γ, z, hznorm, hDz⟩
  let gates : List OneQubitPrimitive :=
    [OneQubitPrimitive.rz α] ++ standardRyGates β ++ [OneQubitPrimitive.rz γ]
  have hGates : oneQubitCircuitMatrix gates = C * rz γ := by
    dsimp [gates, C]
    simp [standardRyGates_matrix, oneQubitCircuitMatrix_append, OneQubitPrimitive.eval, mul_assoc]
  have hUeq : U = z • (C * rz γ) := by
    calc
      U = C * D := by
        dsimp [D]
        have hright : C * C† = (1 : Square 2) := Matrix.mem_unitaryGroup_iff.mp hC
        calc
          U = (1 : Square 2) * U := by simp
          _ = (C * C†) * U := by rw [hright]
          _ = C * (C† * U) := by simp [mul_assoc]
      _ = C * (z • rz γ) := by rw [hDiag, hDz]
      _ = z • (C * rz γ) := by
        simpa using (Matrix.mul_smul C z (rz γ))
  refine ⟨gates, z, hznorm, ?_⟩
  rw [hGates]
  exact hUeq

private theorem conditionalRy_uses_standard_gates (θ₀ θ₁ : ℝ) :
    ∃ gates : List TwoQubitPrimitive,
      twoQubitCircuitMatrix gates = CosineSine.conditionalRy θ₀ θ₁ := by
  rcases controlled_rz_pair_uses_standard_gates (-θ₀) (-θ₁) with ⟨gCtrl, hgCtrl⟩
  let pre : List OneQubitPrimitive :=
    [.t, .t, .t, .t, .t, .t, .h]
  let post : List OneQubitPrimitive :=
    [.h, .t, .t]
  let gates : List TwoQubitPrimitive :=
    (liftFirst pre ++ gCtrl) ++ liftFirst post
  have hpre : oneQubitCircuitMatrix pre = phaseSdagger * hadamard2 := by
    dsimp [pre]
    calc
      oneQubitCircuitMatrix
          [OneQubitPrimitive.t, OneQubitPrimitive.t, OneQubitPrimitive.t,
            OneQubitPrimitive.t, OneQubitPrimitive.t, OneQubitPrimitive.t,
            OneQubitPrimitive.h]
          =
            (phaseT * phaseT * phaseT * phaseT * phaseT * phaseT) *
              hadamard2 := by
              simp [oneQubitCircuitMatrix, OneQubitPrimitive.eval, mul_assoc]
      _ = phaseSdagger * hadamard2 := by
            rw [phaseT_six_eq_phaseSdagger]
  have hpost : oneQubitCircuitMatrix post = hadamard2 * phaseS := by
    dsimp [post]
    calc
      oneQubitCircuitMatrix [OneQubitPrimitive.h, OneQubitPrimitive.t, OneQubitPrimitive.t]
          = hadamard2 * (phaseT * phaseT) := by
              simp [oneQubitCircuitMatrix, OneQubitPrimitive.eval]
      _ = hadamard2 * phaseS := by
            rw [phaseT_sq_eq_phaseS]
  refine ⟨gates, ?_⟩
  calc
    twoQubitCircuitMatrix gates =
        localOnFirst (phaseSdagger * hadamard2) *
          controlledRzPair (-θ₀) (-θ₁) *
          localOnFirst (hadamard2 * phaseS) := by
          dsimp [gates]
          rw [twoQubitCircuitMatrix_append, twoQubitCircuitMatrix_append]
          rw [twoQubitCircuitMatrix_liftFirst, twoQubitCircuitMatrix_liftFirst]
          rw [hgCtrl, hpre, hpost]
    _ = CosineSine.conditionalRy θ₀ θ₁ := by
          rw [← conditionalRy_eq_local_controlledRz]

private theorem blockDiag2_uses_standard_gates_up_to_global_phase
    (V₀ V₁ : Square 2)
    (hV₀ : V₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hV₁ : V₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ gates : List TwoQubitPrimitive,
      GlobalPhaseEquivalent
        (CosineSine.blockDiag2 V₀ V₁)
        (twoQubitCircuitMatrix gates) := by
  rcases lemma4_demultiplex_two_qubit V₀ V₁ hV₀ hV₁ with
    ⟨P, Q, α₀, α₁, hP, hQ, hBlock⟩
  rcases one_qubit_exact_h_t_rz P hP with ⟨gP, hgP⟩
  rcases one_qubit_exact_h_t_rz Q hQ with ⟨gQ, hgQ⟩
  rcases controlled_rz_pair_uses_standard_gates α₀ α₁ with ⟨gCtrl, hgCtrl⟩
  let gates : List TwoQubitPrimitive :=
    (liftSecond gQ ++ gCtrl) ++ liftSecond gP
  have hMatrix :
      twoQubitCircuitMatrix gates =
        twoQubitCircuitMatrix (liftSecond gQ) *
          twoQubitCircuitMatrix gCtrl *
          twoQubitCircuitMatrix (liftSecond gP) := by
    dsimp [gates]
    rw [twoQubitCircuitMatrix_append, twoQubitCircuitMatrix_append]
  have hQcirc :
      GlobalPhaseEquivalent
        (localOnSecond Q)
        (twoQubitCircuitMatrix (liftSecond gQ)) :=
    GlobalPhaseEquivalent.trans
      (GlobalPhaseEquivalent.localOnSecond hgQ)
      (GlobalPhaseEquivalent.of_eq (twoQubitCircuitMatrix_liftSecond gQ).symm)
  have hPcirc :
      GlobalPhaseEquivalent
        (localOnSecond P)
        (twoQubitCircuitMatrix (liftSecond gP)) :=
    GlobalPhaseEquivalent.trans
      (GlobalPhaseEquivalent.localOnSecond hgP)
      (GlobalPhaseEquivalent.of_eq (twoQubitCircuitMatrix_liftSecond gP).symm)
  have hCtrlCirc :
      GlobalPhaseEquivalent
        (controlledRzPair α₀ α₁)
        (twoQubitCircuitMatrix gCtrl) :=
    GlobalPhaseEquivalent.of_eq hgCtrl.symm
  have hProduct :
      GlobalPhaseEquivalent
        (localOnSecond Q * controlledRzPair α₀ α₁ * localOnSecond P)
        (twoQubitCircuitMatrix (liftSecond gQ) *
          twoQubitCircuitMatrix gCtrl *
          twoQubitCircuitMatrix (liftSecond gP)) :=
    GlobalPhaseEquivalent.mul
      (GlobalPhaseEquivalent.mul hQcirc hCtrlCirc)
      hPcirc
  refine ⟨gates, ?_⟩
  exact
    GlobalPhaseEquivalent.trans
      (GlobalPhaseEquivalent.of_eq hBlock)
      (GlobalPhaseEquivalent.trans hProduct
        (GlobalPhaseEquivalent.of_eq hMatrix.symm))

/-- Target theorem for the first Clifford-paper blueprint track. -/
theorem lemma11_two_qubit_synthesis (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ gates : List TwoQubitPrimitive,
      GlobalPhaseEquivalent U (twoQubitCircuitMatrix gates) := by
  rcases CosineSine.cosinesine_exists U hU with
    ⟨P₀, P₁, Q₀, Q₁, θ₀, θ₁, hP₀, hP₁, hQ₀, hQ₁, hUeq⟩
  rcases blockDiag2_uses_standard_gates_up_to_global_phase P₀ P₁ hP₀ hP₁ with
    ⟨gP, hgP⟩
  rcases conditionalRy_uses_standard_gates θ₀ θ₁ with ⟨gR, hgR⟩
  rcases blockDiag2_uses_standard_gates_up_to_global_phase Q₀ Q₁ hQ₀ hQ₁ with
    ⟨gQ, hgQ⟩
  let gates : List TwoQubitPrimitive := (gP ++ gR) ++ gQ
  have hMatrix :
      twoQubitCircuitMatrix gates =
        twoQubitCircuitMatrix gP * twoQubitCircuitMatrix gR * twoQubitCircuitMatrix gQ := by
    dsimp [gates]
    rw [twoQubitCircuitMatrix_append, twoQubitCircuitMatrix_append]
  have hR :
      GlobalPhaseEquivalent
        (CosineSine.conditionalRy θ₀ θ₁)
        (twoQubitCircuitMatrix gR) :=
    GlobalPhaseEquivalent.of_eq hgR.symm
  have hProduct :
      GlobalPhaseEquivalent
        (CosineSine.blockDiag2 P₀ P₁ *
          CosineSine.conditionalRy θ₀ θ₁ *
          CosineSine.blockDiag2 Q₀ Q₁)
        (twoQubitCircuitMatrix gP *
          twoQubitCircuitMatrix gR *
          twoQubitCircuitMatrix gQ) :=
    GlobalPhaseEquivalent.mul
      (GlobalPhaseEquivalent.mul hgP hR)
      hgQ
  refine ⟨gates, ?_⟩
  exact
    GlobalPhaseEquivalent.trans
      (GlobalPhaseEquivalent.of_eq hUeq)
      (GlobalPhaseEquivalent.trans hProduct
        (GlobalPhaseEquivalent.of_eq hMatrix.symm))

end Clifford
end TwoControl

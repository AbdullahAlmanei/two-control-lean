import TwoControl.Clifford.Lemma12.Common.HTCircuit
import RossSelinger.Basic

namespace RossSelinger

open TwoControl
open TwoControl.Clifford
open TwoControl.Clifford.Universal
open TwoControl.Clifford.Lemma12

/-!
Translate the one-qubit Clifford+T circuits produced by Ross-Selinger into the
project's `{H,T}` circuit language.  The key obligations are the standard
identities `S = T^2` and `ω I = (T^2 H)^3`.

This file belongs to the conditional Ross-Selinger compiler leg.  It must not
be imported by anything in `Lemma12/Universal/`.
-/

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

private lemma inv_sqrt_two_sq :
    ((↑(Real.sqrt 2) : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
  have hsqrt_ne : (↑(Real.sqrt 2) : ℂ) ≠ 0 := by
    exact_mod_cast (show (Real.sqrt 2 : ℝ) ≠ 0 by positivity)
  have hsq_real : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hsq : ((↑(Real.sqrt 2) : ℂ)) ^ 2 = (2 : ℂ) := by
    exact_mod_cast hsq_real
  field_simp [pow_two, hsqrt_ne]
  simpa using hsq.symm

private lemma inv_sqrt_two_cube :
    ((↑(Real.sqrt 2) : ℂ)⁻¹) ^ 3 = (1 / 2 : ℂ) * ((↑(Real.sqrt 2) : ℂ)⁻¹) := by
  calc
    ((↑(Real.sqrt 2) : ℂ)⁻¹) ^ 3 = ((↑(Real.sqrt 2) : ℂ)⁻¹) ^ 2 * ((↑(Real.sqrt 2) : ℂ)⁻¹) := by
      ring
    _ = (1 / 2 : ℂ) * ((↑(Real.sqrt 2) : ℂ)⁻¹) := by rw [inv_sqrt_two_sq]

private lemma inv_sqrt_two_cubed_inv :
    (((↑(Real.sqrt 2) : ℂ) ^ 3)⁻¹) = (1 / 2 : ℂ) * ((↑(Real.sqrt 2) : ℂ)⁻¹) := by
  simpa [inv_pow] using inv_sqrt_two_cube

private lemma sqrt_two_div_two_eq_inv_sqrt_two :
    (((Real.sqrt 2) / 2 : ℝ) : ℂ) = ((↑(Real.sqrt 2) : ℂ)⁻¹) := by
  have hsqrt_ne : (Real.sqrt 2 : ℝ) ≠ 0 := by
    positivity
  have hreal : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
    field_simp [hsqrt_ne]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  exact_mod_cast hreal

private lemma exp_pi_div_four_mul_I :
    Complex.exp (Complex.I * (Real.pi / 4)) =
      ((↑(Real.sqrt 2) : ℂ)⁻¹) + ((↑(Real.sqrt 2) : ℂ)⁻¹) * Complex.I := by
  rw [show Complex.I * (Real.pi / 4) = ((Real.pi / 4 : ℂ) * Complex.I) by ring,
    Complex.exp_mul_I]
  have hcast : (Real.pi / 4 : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) := by
    norm_num
  have hcos : Complex.cos (Real.pi / 4 : ℂ) = (((Real.sqrt 2) / 2 : ℝ) : ℂ) := by
    rw [hcast, ← Complex.ofReal_cos, Real.cos_pi_div_four]
  have hsin : Complex.sin (Real.pi / 4 : ℂ) = (((Real.sqrt 2) / 2 : ℝ) : ℂ) := by
    rw [hcast, ← Complex.ofReal_sin, Real.sin_pi_div_four]
  rw [hcos, hsin, sqrt_two_div_two_eq_inv_sqrt_two]

private lemma phaseS_hadamard_cube_eq_omega :
    (phaseS * hadamard2) * (phaseS * hadamard2) * (phaseS * hadamard2) =
      Complex.exp (Complex.I * (Real.pi / 4)) • (1 : Square 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseS, hadamard2, diag2, Matrix.mul_apply, Fin.sum_univ_two,
      exp_pi_div_four_mul_I]
  all_goals
    ring_nf
    simp [Complex.I_sq, Complex.I_pow_three, inv_sqrt_two_cubed_inv]
    try ring

/-- The standard `{H,T}` word for the scalar `ω I`, following
`(T^2 H)^3 = ω I`. -/
def omegaWord : HTCircuit :=
  [.t, .t, .h, .t, .t, .h, .t, .t, .h]

/-- Translate a single Ross-Selinger primitive into an `{H,T}` word. -/
def RossSelingerPrimitive.toHT : RossSelingerPrimitive → HTCircuit
  | .h => [.h]
  | .s => [.t, .t]
  | .t => [.t]
  | .omega => omegaWord

/-- Translate a Ross-Selinger circuit gate-by-gate into an `{H,T}` circuit. -/
def CliffordTCircuit.toHT (gates : CliffordTCircuit) : HTCircuit :=
  gates.foldr (fun gate acc => RossSelingerPrimitive.toHT gate ++ acc) []

/-- Matrix correctness of the chosen `ω` word. -/
theorem omegaWord_eval :
    HTCircuit.eval omegaWord = RossSelingerPrimitive.eval .omega := by
  have hword :
      HTCircuit.eval omegaWord =
        (phaseT * phaseT * hadamard2) *
          (phaseT * phaseT * hadamard2) *
          (phaseT * phaseT * hadamard2) := by
    simp [omegaWord, HTCircuit.eval, oneQubitHTCircuitMatrix,
      OneQubitHTPrimitive.eval, mul_assoc]
  rw [hword]
  simpa [RossSelingerPrimitive.eval, phaseT_sq_eq_phaseS, mul_assoc] using
    phaseS_hadamard_cube_eq_omega

/-- Single-gate correctness of the Ross-Selinger-to-`{H,T}` translation. -/
theorem RossSelingerPrimitive.eval_toHT (gate : RossSelingerPrimitive) :
    HTCircuit.eval (RossSelingerPrimitive.toHT gate) = RossSelingerPrimitive.eval gate := by
  cases gate
  · simp [RossSelingerPrimitive.toHT, HTCircuit.eval, oneQubitHTCircuitMatrix,
      OneQubitHTPrimitive.eval, RossSelingerPrimitive.eval]
  · simpa [RossSelingerPrimitive.toHT, HTCircuit.eval, oneQubitHTCircuitMatrix,
      OneQubitHTPrimitive.eval, RossSelingerPrimitive.eval] using phaseT_sq_eq_phaseS
  · simp [RossSelingerPrimitive.toHT, HTCircuit.eval, oneQubitHTCircuitMatrix,
      OneQubitHTPrimitive.eval, RossSelingerPrimitive.eval]
  · simpa [RossSelingerPrimitive.toHT] using omegaWord_eval

/-- Circuit-level correctness of the Ross-Selinger-to-`{H,T}` translation. -/
theorem CliffordTCircuit.eval_toHT (gates : CliffordTCircuit) :
    HTCircuit.eval (CliffordTCircuit.toHT gates) = CliffordTCircuit.eval gates := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
      calc
        HTCircuit.eval (CliffordTCircuit.toHT (gate :: gates))
            = HTCircuit.eval (RossSelingerPrimitive.toHT gate ++ CliffordTCircuit.toHT gates) := by
                rfl
        _ = HTCircuit.eval (RossSelingerPrimitive.toHT gate) * HTCircuit.eval (CliffordTCircuit.toHT gates) := by
                simpa [HTCircuit.eval] using
                  oneQubitHTCircuitMatrix_append (RossSelingerPrimitive.toHT gate)
                    (CliffordTCircuit.toHT gates)
        _ = RossSelingerPrimitive.eval gate * CliffordTCircuit.eval gates := by
                rw [RossSelingerPrimitive.eval_toHT, ih]
        _ = CliffordTCircuit.eval (gate :: gates) := by
                rfl

end RossSelinger

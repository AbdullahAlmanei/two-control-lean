import TwoControl.Clifford.Universal.CliffordRz
import TwoControl.Clifford.Universal.RecursiveBounds

namespace TwoControl
namespace Clifford
namespace Universal

/-!
Bounded exact Clifford+`R_z` synthesis.

This file is the endpoint for stage 1 of the bound project.  It proves, as a
fixed API target, that the existing exact Lemma 1 route can be converted into a
Clifford+`R_z` circuit with length bounded by a function of `n` alone.

No theorem in this file mentions Lemma 12, `{H,T}` approximation of `R_z`, or
an approximation parameter `ε`.
-/

/-- A deliberately coarse constant upper bound for the existing two-qubit
Lemma 11 construction.  The current construction is much smaller; the point of
this constant is only that it is independent of `n`. -/
def lemma11Bound : ℕ := 128

/-- One easy-gate factor expands to at most this many Clifford+`R_z` factors.

The maximum accounts for arbitrary embedded two-qubit gates via Lemma 11 and
for the embedded `S† = T^6` case. -/
def easyFactorToCliffordRzBound : ℕ :=
  max lemma11Bound 6

/-- Stage-one exact Clifford+`R_z` circuit length bound. -/
def cliffordRzBound (n : ℕ) : ℕ :=
  easyFactorToCliffordRzBound * easyBound n

private lemma phaseT_sq_eq_phaseS_bound :
    phaseT * phaseT = phaseS := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [phaseT, phaseS, diag2, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [phaseT, phaseS, diag2, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [phaseT, phaseS, diag2, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [phaseT, phaseS, diag2, Matrix.mul_apply, Fin.sum_univ_two]
    calc
      Complex.exp (Complex.I * (Real.pi / 4)) *
          Complex.exp (Complex.I * (Real.pi / 4))
          = Complex.exp (Real.pi / 2 * Complex.I) := by
              rw [← Complex.exp_add]
              congr 1
              ring
      _ = Complex.I := by simpa [mul_comm] using Complex.exp_pi_div_two_mul_I

private lemma phaseS_cubed_eq_phaseSdagger_bound :
    phaseS * phaseS * phaseS = phaseSdagger := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseS, phaseSdagger, diag2, Matrix.mul_apply, Fin.sum_univ_two]

private lemma phaseT_six_eq_phaseSdagger_bound :
    phaseT * phaseT * phaseT * phaseT * phaseT * phaseT = phaseSdagger := by
  calc
    phaseT * phaseT * phaseT * phaseT * phaseT * phaseT
        = (phaseT * phaseT) * ((phaseT * phaseT) * (phaseT * phaseT)) := by
            simp [mul_assoc]
    _ = phaseS * (phaseS * phaseS) := by rw [phaseT_sq_eq_phaseS_bound]
    _ = phaseSdagger := by simpa [mul_assoc] using phaseS_cubed_eq_phaseSdagger_bound

private lemma localOnFirst_mul_bound (A B : Square 2) :
    localOnFirst (A * B) = localOnFirst A * localOnFirst B := by
  unfold localOnFirst
  simpa using
    (KronHelpers.kron_mul_reindex (A := A) (B := B)
      (C := (1 : Square 2)) (D := (1 : Square 2)))

private lemma localOnSecond_mul_bound (A B : Square 2) :
    localOnSecond (A * B) = localOnSecond A * localOnSecond B := by
  unfold localOnSecond
  simpa using
    (KronHelpers.kron_mul_reindex (A := (1 : Square 2)) (B := (1 : Square 2))
      (C := A) (D := B))

private lemma oneQubitCircuitMatrix_phaseS_bound :
    oneQubitCircuitMatrix [.t, .t] = phaseS := by
  simpa [oneQubitCircuitMatrix, OneQubitPrimitive.eval] using phaseT_sq_eq_phaseS_bound

private lemma oneQubitCircuitMatrix_phaseSdagger_bound :
    oneQubitCircuitMatrix [.t, .t, .t, .t, .t, .t] = phaseSdagger := by
  calc
    oneQubitCircuitMatrix [.t, .t, .t, .t, .t, .t]
        = phaseT * phaseT * phaseT * phaseT * phaseT * phaseT := by
            simp [oneQubitCircuitMatrix, OneQubitPrimitive.eval, mul_assoc]
    _ = phaseSdagger := phaseT_six_eq_phaseSdagger_bound

private lemma twoQubitCircuitMatrix_onFirst_phaseS_bound :
    twoQubitCircuitMatrix [.onFirst .t, .onFirst .t] =
      localOnFirst phaseS := by
  calc
    twoQubitCircuitMatrix [.onFirst .t, .onFirst .t]
        = localOnFirst phaseT * localOnFirst phaseT := by
            simp [twoQubitCircuitMatrix, TwoQubitPrimitive.eval, OneQubitPrimitive.eval]
    _ = localOnFirst (phaseT * phaseT) := by rw [← localOnFirst_mul_bound]
    _ = localOnFirst phaseS := by rw [phaseT_sq_eq_phaseS_bound]

private lemma twoQubitCircuitMatrix_onSecond_phaseS_bound :
    twoQubitCircuitMatrix [.onSecond .t, .onSecond .t] =
      localOnSecond phaseS := by
  calc
    twoQubitCircuitMatrix [.onSecond .t, .onSecond .t]
        = localOnSecond phaseT * localOnSecond phaseT := by
            simp [twoQubitCircuitMatrix, TwoQubitPrimitive.eval, OneQubitPrimitive.eval]
    _ = localOnSecond (phaseT * phaseT) := by rw [← localOnSecond_mul_bound]
    _ = localOnSecond phaseS := by rw [phaseT_sq_eq_phaseS_bound]

private lemma twoQubitCircuitMatrix_onFirst_phaseSdagger_bound :
    twoQubitCircuitMatrix
        [.onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t] =
      localOnFirst phaseSdagger := by
  calc
    twoQubitCircuitMatrix
        [.onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t]
        = localOnFirst phaseT *
            (localOnFirst phaseT *
              (localOnFirst phaseT *
                (localOnFirst phaseT * (localOnFirst phaseT * localOnFirst phaseT)))) := by
            simp [twoQubitCircuitMatrix, TwoQubitPrimitive.eval, OneQubitPrimitive.eval]
    _ = localOnFirst
            (phaseT * (phaseT * (phaseT * (phaseT * (phaseT * phaseT))))) := by
            repeat rw [← localOnFirst_mul_bound]
    _ = localOnFirst (phaseT * phaseT * phaseT * phaseT * phaseT * phaseT) := by
            congr 1
            simp [mul_assoc]
    _ = localOnFirst phaseSdagger := by rw [phaseT_six_eq_phaseSdagger_bound]

private lemma twoQubitCircuitMatrix_onSecond_phaseSdagger_bound :
    twoQubitCircuitMatrix
        [.onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t,
          .onSecond .t] =
      localOnSecond phaseSdagger := by
  calc
    twoQubitCircuitMatrix
        [.onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t,
          .onSecond .t]
        = localOnSecond phaseT *
            (localOnSecond phaseT *
              (localOnSecond phaseT *
                (localOnSecond phaseT * (localOnSecond phaseT * localOnSecond phaseT)))) := by
            simp [twoQubitCircuitMatrix, TwoQubitPrimitive.eval, OneQubitPrimitive.eval]
    _ = localOnSecond
            (phaseT * (phaseT * (phaseT * (phaseT * (phaseT * phaseT))))) := by
            repeat rw [← localOnSecond_mul_bound]
    _ = localOnSecond (phaseT * phaseT * phaseT * phaseT * phaseT * phaseT) := by
            congr 1
            simp [mul_assoc]
    _ = localOnSecond phaseSdagger := by rw [phaseT_six_eq_phaseSdagger_bound]

private theorem reindexSquare_smul_bound {N M : ℕ} (e : Fin N ≃ Fin M)
    (z : ℂ) (U : Square N) :
    reindexSquare e (z • U) = z • reindexSquare e U := by
  simp [reindexSquare]

private theorem castSquare_smul_bound {N M : ℕ} (h : N = M)
    (z : ℂ) (U : Square N) :
    castSquare h (z • U) = z • castSquare h U := by
  simpa [castSquare] using reindexSquare_smul_bound (Equiv.cast (congrArg Fin h)) z U

private theorem TwoQubitPlacement.tensor_smul_bound {n : ℕ} (p : TwoQubitPlacement n)
    (z : ℂ) (U : Square 4) :
    p.tensor (z • U) = z • p.tensor U := by
  unfold TwoQubitPlacement.tensor
  rw [kron_smul_left, KronHelpers.kron_smul_right]

private theorem TwoQubitPlacement.embed_smul_bound {n : ℕ} (p : TwoQubitPlacement n)
    (z : ℂ) (U : Square 4) :
    p.embed (z • U) = z • p.embed U := by
  unfold TwoQubitPlacement.embed
  rw [TwoQubitPlacement.tensor_smul_bound, castSquare_smul_bound, reindexSquare_smul_bound]

private theorem TwoQubitPlacement.globalPhaseEquivalent_bound {n : ℕ}
    (p : TwoQubitPlacement n) {A B : Square 4}
    (hAB : GlobalPhaseEquivalent A B) :
    GlobalPhaseEquivalent (p.embed A) (p.embed B) := by
  rcases hAB with ⟨z, hz, hA⟩
  refine ⟨z, hz, ?_⟩
  rw [hA, p.embed_smul_bound]

private noncomputable def standardRyGates_bound (θ : ℝ) :
    List OneQubitPrimitive :=
  [.t, .t, .t, .t, .t, .t, .h, .rz (-θ), .h, .t, .t]

private lemma standardRyGates_bound_matrix (θ : ℝ) :
    oneQubitCircuitMatrix (standardRyGates_bound θ) = CosineSine.ry θ := by
  calc
    oneQubitCircuitMatrix (standardRyGates_bound θ)
        = (phaseT * phaseT * phaseT * phaseT * phaseT * phaseT) *
            hadamard2 * rz (-θ) * hadamard2 * (phaseT * phaseT) := by
              simp [standardRyGates_bound, oneQubitCircuitMatrix,
                OneQubitPrimitive.eval, mul_assoc]
    _ = phaseSdagger * hadamard2 * rz (-θ) * hadamard2 * phaseS := by
          rw [phaseT_six_eq_phaseSdagger_bound, phaseT_sq_eq_phaseS_bound]
    _ = CosineSine.ry θ := by
          symm
          exact lemma3_ry_via_rz θ

private theorem one_qubit_exact_h_t_rz_bounded (U : Square 2)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ gates : List OneQubitPrimitive,
      GlobalPhaseEquivalent U (oneQubitCircuitMatrix gates) ∧
      gates.length ≤ 13 := by
  rcases one_qubit_euler_rz_ry_rz_up_to_global_phase U hU with
    ⟨α, β, γ, z, hz, hEuler⟩
  let gates : List OneQubitPrimitive :=
    [OneQubitPrimitive.rz α] ++ standardRyGates_bound β ++ [OneQubitPrimitive.rz γ]
  refine ⟨gates, ?_, ?_⟩
  · refine ⟨z, hz, ?_⟩
    have hGates :
        oneQubitCircuitMatrix gates = rz α * CosineSine.ry β * rz γ := by
      dsimp [gates]
      simp [standardRyGates_bound_matrix, oneQubitCircuitMatrix_append,
        OneQubitPrimitive.eval, mul_assoc]
    rw [hGates]
    exact hEuler
  · simp [gates, standardRyGates_bound]

private lemma localOnFirst_rz_eq_bound (θ : ℝ) :
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

private lemma diag4_mul_diag4_bound (a b c d e f g h : ℂ) :
    diag4 a b c d * diag4 e f g h = diag4 (a * e) (b * f) (c * g) (d * h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag4, Matrix.mul_apply, Fin.sum_univ_four]

private lemma proj0_eq_diag2_bound : proj0 = diag2 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, ketbra, ket0, diag2]

private lemma proj1_eq_diag2_bound : proj1 = diag2 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, ketbra, ket1, diag2]

private lemma controlledRzPair_eq_diag4_bound (α₀ α₁ : ℝ) :
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
  rw [controlledRzPair, proj0_eq_diag2_bound, proj1_eq_diag2_bound, rz, rz,
    hneg₀, hneg₁]
  rw [diag2_kron_diag2, diag2_kron_diag2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag4, mul_comm]

private theorem controlled_rz_pair_uses_standard_gates_bounded (α₀ α₁ : ℝ) :
    ∃ gates : List TwoQubitPrimitive,
      twoQubitCircuitMatrix gates = controlledRzPair α₀ α₁ ∧
      gates.length ≤ 4 := by
  let beta : ℝ := (α₀ - α₁) / 2
  let gamma : ℝ := (α₀ + α₁) / 2
  refine ⟨[TwoQubitPrimitive.cnot,
      TwoQubitPrimitive.onFirst (OneQubitPrimitive.rz beta),
      TwoQubitPrimitive.cnot,
      TwoQubitPrimitive.onFirst (OneQubitPrimitive.rz gamma)], ?_, ?_⟩
  · have hconj :
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
                rw [localOnFirst_rz_eq_bound]
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
              simp [twoQubitCircuitMatrix, TwoQubitPrimitive.eval,
                OneQubitPrimitive.eval, mul_assoc]
      _ = diag4 (Complex.exp (((-beta) / 2) * Complex.I))
            (Complex.exp ((beta / 2) * Complex.I))
            (Complex.exp ((beta / 2) * Complex.I))
            (Complex.exp (((-beta) / 2) * Complex.I)) *
            diag4 (Complex.exp (((-gamma) / 2) * Complex.I))
              (Complex.exp (((-gamma) / 2) * Complex.I))
              (Complex.exp ((gamma / 2) * Complex.I))
              (Complex.exp ((gamma / 2) * Complex.I)) := by
            rw [hconj, localOnFirst_rz_eq_bound]
      _ = diag4
            (Complex.exp (((-beta) / 2) * Complex.I) *
              Complex.exp (((-gamma) / 2) * Complex.I))
            (Complex.exp ((beta / 2) * Complex.I) *
              Complex.exp (((-gamma) / 2) * Complex.I))
            (Complex.exp ((beta / 2) * Complex.I) *
              Complex.exp ((gamma / 2) * Complex.I))
            (Complex.exp (((-beta) / 2) * Complex.I) *
              Complex.exp ((gamma / 2) * Complex.I)) := by
            rw [diag4_mul_diag4_bound]
      _ = controlledRzPair α₀ α₁ := by
            rw [controlledRzPair_eq_diag4_bound]
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
  · simp

private lemma localOnFirst_mul_controlledRzPair_mul_localOnFirst_bound
    (A B : Square 2) (α₀ α₁ : ℝ) :
    localOnFirst A * controlledRzPair α₀ α₁ * localOnFirst B =
      (A * rz α₀ * B) ⊗ₖ proj0 + (A * rz α₁ * B) ⊗ₖ proj1 := by
  unfold localOnFirst controlledRzPair
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [← kron_mul_two, ← kron_mul_two, ← kron_mul_two, ← kron_mul_two]
  simp [mul_assoc]

private theorem conditionalRy_uses_standard_gates_bounded (θ₀ θ₁ : ℝ) :
    ∃ gates : List TwoQubitPrimitive,
      twoQubitCircuitMatrix gates = CosineSine.conditionalRy θ₀ θ₁ ∧
      gates.length ≤ 14 := by
  rcases controlled_rz_pair_uses_standard_gates_bounded (-θ₀) (-θ₁) with
    ⟨gCtrl, hgCtrl, hCtrlLen⟩
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
            rw [phaseT_six_eq_phaseSdagger_bound]
  have hpost : oneQubitCircuitMatrix post = hadamard2 * phaseS := by
    dsimp [post]
    calc
      oneQubitCircuitMatrix [OneQubitPrimitive.h, OneQubitPrimitive.t,
          OneQubitPrimitive.t]
          = hadamard2 * (phaseT * phaseT) := by
              simp [oneQubitCircuitMatrix, OneQubitPrimitive.eval]
      _ = hadamard2 * phaseS := by
            rw [phaseT_sq_eq_phaseS_bound]
  refine ⟨gates, ?_, ?_⟩
  · calc
      twoQubitCircuitMatrix gates =
          localOnFirst (phaseSdagger * hadamard2) *
            controlledRzPair (-θ₀) (-θ₁) *
            localOnFirst (hadamard2 * phaseS) := by
            dsimp [gates]
            rw [twoQubitCircuitMatrix_append, twoQubitCircuitMatrix_append]
            rw [twoQubitCircuitMatrix_liftFirst, twoQubitCircuitMatrix_liftFirst]
            rw [hgCtrl, hpre, hpost]
      _ = CosineSine.conditionalRy θ₀ θ₁ := by
            rw [localOnFirst_mul_controlledRzPair_mul_localOnFirst_bound]
            have hθ₀ :
                phaseSdagger * hadamard2 * rz (-θ₀) * (hadamard2 * phaseS) =
                  CosineSine.ry θ₀ := by
              rw [lemma3_ry_via_rz θ₀]
              simp [mul_assoc]
            have hθ₁ :
                phaseSdagger * hadamard2 * rz (-θ₁) * (hadamard2 * phaseS) =
                  CosineSine.ry θ₁ := by
              rw [lemma3_ry_via_rz θ₁]
              simp [mul_assoc]
            rw [hθ₀, hθ₁]
            rfl
  · dsimp [gates, pre, post]
    simp [liftFirst]
    omega

private theorem blockDiag2_uses_standard_gates_up_to_global_phase_bounded
    (V₀ V₁ : Square 2)
    (hV₀ : V₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hV₁ : V₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ gates : List TwoQubitPrimitive,
      GlobalPhaseEquivalent
        (CosineSine.blockDiag2 V₀ V₁)
        (twoQubitCircuitMatrix gates) ∧
      gates.length ≤ 30 := by
  rcases lemma4_demultiplex_two_qubit V₀ V₁ hV₀ hV₁ with
    ⟨P, Q, α₀, α₁, hP, hQ, hBlock⟩
  rcases one_qubit_exact_h_t_rz_bounded P hP with ⟨gP, hgP, hLenP⟩
  rcases one_qubit_exact_h_t_rz_bounded Q hQ with ⟨gQ, hgQ, hLenQ⟩
  rcases controlled_rz_pair_uses_standard_gates_bounded α₀ α₁ with
    ⟨gCtrl, hgCtrl, hLenCtrl⟩
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
  refine ⟨gates, ?_, ?_⟩
  · exact
      GlobalPhaseEquivalent.trans
        (GlobalPhaseEquivalent.of_eq hBlock)
        (GlobalPhaseEquivalent.trans hProduct
          (GlobalPhaseEquivalent.of_eq hMatrix.symm))
  · dsimp [gates]
    simp [liftSecond]
    omega

/-- Bounded version of the existing two-qubit Lemma 11 synthesis theorem. -/
theorem lemma11_two_qubit_synthesis_bounded (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ gates : List TwoQubitPrimitive,
      GlobalPhaseEquivalent U (twoQubitCircuitMatrix gates) ∧
      gates.length ≤ lemma11Bound := by
  rcases CosineSine.cosinesine_exists U hU with
    ⟨P₀, P₁, Q₀, Q₁, θ₀, θ₁, hP₀, hP₁, hQ₀, hQ₁, hUeq⟩
  rcases blockDiag2_uses_standard_gates_up_to_global_phase_bounded
      P₀ P₁ hP₀ hP₁ with
    ⟨gP, hgP, hLenP⟩
  rcases conditionalRy_uses_standard_gates_bounded θ₀ θ₁ with
    ⟨gR, hgR, hLenR⟩
  rcases blockDiag2_uses_standard_gates_up_to_global_phase_bounded
      Q₀ Q₁ hQ₀ hQ₁ with
    ⟨gQ, hgQ, hLenQ⟩
  let gates : List TwoQubitPrimitive := (gP ++ gR) ++ gQ
  have hMatrix :
      twoQubitCircuitMatrix gates =
        twoQubitCircuitMatrix gP * twoQubitCircuitMatrix gR *
          twoQubitCircuitMatrix gQ := by
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
  refine ⟨gates, ?_, ?_⟩
  · exact
      GlobalPhaseEquivalent.trans
        (GlobalPhaseEquivalent.of_eq hUeq)
        (GlobalPhaseEquivalent.trans hProduct
          (GlobalPhaseEquivalent.of_eq hMatrix.symm))
  · dsimp [gates, lemma11Bound]
    simp
    omega

/-- Universal-layer wrapper around bounded Lemma 11. -/
theorem two_qubit_gate_has_clifford_rz_circuit_bounded (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ gates : List TwoQubitPrimitive,
      GlobalPhaseEquivalent U (twoQubitCircuitMatrix gates) ∧
      gates.length ≤ lemma11Bound :=
  lemma11_two_qubit_synthesis_bounded U hU

/-- Lift a bounded two-qubit Clifford+`R_z` circuit into an arbitrary embedded
two-qubit placement. -/
theorem embedded_two_qubit_clifford_rz_lift_bounded {n : ℕ} {V : Square 4}
    {U : Square (2 ^ n)}
    (hEmbed : IsEmbeddedTwoQubitGate n V U)
    (hSynth : ∃ gates : List TwoQubitPrimitive,
      GlobalPhaseEquivalent V (twoQubitCircuitMatrix gates) ∧
      gates.length ≤ lemma11Bound) :
    SynthesizesUpToGlobalPhaseWithLength
      (CliffordTRzGate n) U lemma11Bound := by
  rcases hEmbed with ⟨p, rfl⟩
  rcases hSynth with ⟨gates, hPhase, hLen⟩
  refine ⟨embedTwoQubitCircuit p gates,
    CircuitOver_embedTwoQubitCircuit_cliffordTRz p gates, ?_, ?_⟩
  · exact GlobalPhaseEquivalent.trans
      (TwoQubitPlacement.globalPhaseEquivalent_bound p hPhase)
      (GlobalPhaseEquivalent.of_eq (circuitMatrix_embedTwoQubitCircuit p gates).symm)
  · simpa [embedTwoQubitCircuit] using hLen

/-- Embedded `S` is a bounded Clifford+`R_z` circuit because `S = T*T`. -/
theorem embedded_phaseS_is_clifford_rz_bounded {n : ℕ}
    {U : Square (2 ^ n)}
    (hU : IsEmbeddedOneQubitGate n phaseS U) :
    SynthesizesUpToGlobalPhaseWithLength
      (CliffordTRzGate n) U 2 := by
  rcases hU with ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
  · refine ⟨embedOneQubitCircuit p [.t, .t],
      CircuitOver_embedOneQubitCircuit_cliffordTRz p [.t, .t], ?_, ?_⟩
    · apply GlobalPhaseEquivalent.of_eq
      rw [circuitMatrix_embedOneQubitCircuit, oneQubitCircuitMatrix_phaseS_bound]
    · simp [embedOneQubitCircuit]
  · refine ⟨embedTwoQubitCircuit p [.onFirst .t, .onFirst .t],
      CircuitOver_embedTwoQubitCircuit_cliffordTRz p [.onFirst .t, .onFirst .t], ?_, ?_⟩
    · apply GlobalPhaseEquivalent.of_eq
      rw [circuitMatrix_embedTwoQubitCircuit, twoQubitCircuitMatrix_onFirst_phaseS_bound]
    · simp [embedTwoQubitCircuit]
  · refine ⟨embedTwoQubitCircuit p [.onSecond .t, .onSecond .t],
      CircuitOver_embedTwoQubitCircuit_cliffordTRz p [.onSecond .t, .onSecond .t], ?_, ?_⟩
    · apply GlobalPhaseEquivalent.of_eq
      rw [circuitMatrix_embedTwoQubitCircuit, twoQubitCircuitMatrix_onSecond_phaseS_bound]
    · simp [embedTwoQubitCircuit]

/-- Embedded `S†` is a bounded Clifford+`R_z` circuit because `S† = T^6`. -/
theorem embedded_phaseSdagger_is_clifford_rz_bounded {n : ℕ}
    {U : Square (2 ^ n)}
    (hU : IsEmbeddedOneQubitGate n phaseSdagger U) :
    SynthesizesUpToGlobalPhaseWithLength
      (CliffordTRzGate n) U 6 := by
  rcases hU with ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
  · refine ⟨embedOneQubitCircuit p [.t, .t, .t, .t, .t, .t],
      CircuitOver_embedOneQubitCircuit_cliffordTRz p [.t, .t, .t, .t, .t, .t],
      ?_, ?_⟩
    · apply GlobalPhaseEquivalent.of_eq
      rw [circuitMatrix_embedOneQubitCircuit, oneQubitCircuitMatrix_phaseSdagger_bound]
    · simp [embedOneQubitCircuit]
  · refine ⟨embedTwoQubitCircuit p
        [.onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t],
      CircuitOver_embedTwoQubitCircuit_cliffordTRz p
        [.onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t],
      ?_, ?_⟩
    · apply GlobalPhaseEquivalent.of_eq
      rw [circuitMatrix_embedTwoQubitCircuit,
        twoQubitCircuitMatrix_onFirst_phaseSdagger_bound]
    · simp [embedTwoQubitCircuit]
  · refine ⟨embedTwoQubitCircuit p
        [.onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t,
          .onSecond .t],
      CircuitOver_embedTwoQubitCircuit_cliffordTRz p
        [.onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t,
          .onSecond .t],
      ?_, ?_⟩
    · apply GlobalPhaseEquivalent.of_eq
      rw [circuitMatrix_embedTwoQubitCircuit,
        twoQubitCircuitMatrix_onSecond_phaseSdagger_bound]
    · simp [embedTwoQubitCircuit]

/-- Bounded replacement of one easy-gate factor by a Clifford+`R_z` circuit. -/
theorem easy_gate_factor_to_clifford_rz_bounded {n : ℕ}
    {U : Square (2 ^ n)}
    (hU : EasyGate n U) :
    SynthesizesUpToGlobalPhaseWithLength
      (CliffordTRzGate n) U easyFactorToCliffordRzBound := by
  rcases hU with hTwo | hH | hS | hSdag | hRz
  · rcases hTwo with ⟨V, hV, hEmbed⟩
    exact SynthesizesUpToGlobalPhaseWithLength.mono_bound
      (by simp [easyFactorToCliffordRzBound, lemma11Bound])
      (embedded_two_qubit_clifford_rz_lift_bounded hEmbed
        (two_qubit_gate_has_clifford_rz_circuit_bounded V hV))
  · exact SynthesizesUpToGlobalPhaseWithLength.mono_bound
      (by simp [easyFactorToCliffordRzBound, lemma11Bound])
      (synthesizesUpToGlobalPhaseWithLength_singleton
        (CliffordTRzGate.hadamard hH))
  · exact SynthesizesUpToGlobalPhaseWithLength.mono_bound
      (by simp [easyFactorToCliffordRzBound, lemma11Bound])
      (embedded_phaseS_is_clifford_rz_bounded hS)
  · exact SynthesizesUpToGlobalPhaseWithLength.mono_bound
      (by simp [easyFactorToCliffordRzBound, lemma11Bound])
      (embedded_phaseSdagger_is_clifford_rz_bounded hSdag)
  · rcases hRz with ⟨θ, hRz⟩
    exact SynthesizesUpToGlobalPhaseWithLength.mono_bound
      (by simp [easyFactorToCliffordRzBound, lemma11Bound])
      (synthesizesUpToGlobalPhaseWithLength_singleton
        (CliffordTRzGate.rz θ hRz))

/-- Bounded replacement of an easy-gate list by a Clifford+`R_z` circuit
synthesizing the same matrix up to global phase. -/
theorem easy_circuit_matrix_to_clifford_rz_bounded {n : ℕ}
    (gates : List (Square (2 ^ n)))
    (hGates : CircuitOver (EasyGate n) gates) :
    SynthesizesUpToGlobalPhaseWithLength
      (CliffordTRzGate n)
      (circuitMatrix gates)
      (easyFactorToCliffordRzBound * gates.length) := by
  induction gates with
  | nil =>
      refine ⟨[], ?_, ?_, ?_⟩
      · intro gate hgate
        simp at hgate
      · exact GlobalPhaseEquivalent.refl (circuitMatrix ([] : List (Square (2 ^ n))))
      · simp
  | cons gate tail ih =>
      have hGate : EasyGate n gate := hGates gate (by simp)
      have hTail : CircuitOver (EasyGate n) tail := by
        intro candidate hcandidate
        exact hGates candidate (by simp [hcandidate])
      have hGateSynth :
          SynthesizesUpToGlobalPhaseWithLength
            (CliffordTRzGate n) gate easyFactorToCliffordRzBound :=
        easy_gate_factor_to_clifford_rz_bounded hGate
      have hTailSynth :
          SynthesizesUpToGlobalPhaseWithLength
            (CliffordTRzGate n) (circuitMatrix tail)
            (easyFactorToCliffordRzBound * tail.length) :=
        ih hTail
      have hProduct := synthesizesUpToGlobalPhaseWithLength_mul hGateSynth hTailSynth
      have hBound :
          easyFactorToCliffordRzBound +
              easyFactorToCliffordRzBound * tail.length =
            easyFactorToCliffordRzBound * (gate :: tail).length := by
        rw [List.length_cons, Nat.mul_succ, Nat.add_comm]
      simpa [hBound] using hProduct

/-- Bounded replacement of an exact easy-gate synthesis by a Clifford+`R_z`
synthesis. -/
theorem easy_circuit_to_clifford_rz_bounded {n : ℕ}
    {U : Square (2 ^ n)} {bound : ℕ}
    (hU : SynthesizesWithLength (EasyGate n) U bound) :
    SynthesizesUpToGlobalPhaseWithLength
      (CliffordTRzGate n) U
      (easyFactorToCliffordRzBound * bound) := by
  rcases hU with ⟨gates, hGates, hEq, hLen⟩
  rw [hEq]
  exact SynthesizesUpToGlobalPhaseWithLength.mono_bound
    (Nat.mul_le_mul_left easyFactorToCliffordRzBound hLen)
    (easy_circuit_matrix_to_clifford_rz_bounded gates hGates)

/-- Bounded version of `clifford_rz_synthesis_from_lemma1`. -/
theorem clifford_rz_synthesis_from_lemma1_bounded {n : ℕ} (hn : 2 ≤ n)
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    SynthesizesUpToGlobalPhaseWithLength
      (CliffordTRzGate n) U
      (cliffordRzBound n) := by
  simpa [cliffordRzBound] using
    easy_circuit_to_clifford_rz_bounded
      (lemma1_decomposition_to_easy_gate_set_bounded hn U hU)

/-- Unpacked stage-one theorem: every `n ≥ 2` unitary has an exact
Clifford+`R_z` circuit whose length is bounded by `cliffordRzBound n`. -/
theorem clifford_rz_synthesis_bounded_of_two_le {n : ℕ} (hn : 2 ≤ n)
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTRzGate n) gates ∧
      GlobalPhaseEquivalent U (circuitMatrix gates) ∧
      gates.length ≤ cliffordRzBound n := by
  simpa [SynthesizesUpToGlobalPhaseWithLength] using
    clifford_rz_synthesis_from_lemma1_bounded hn U hU

/-- Coarse `4^n` upper bound for the exact Clifford+`R_z` stage. -/
theorem cliffordRzBound_le_const_mul_four_pow (n : ℕ) :
    cliffordRzBound n ≤
      (5 * easyFactorToCliffordRzBound) * 4 ^ n := by
  calc
    cliffordRzBound n
        = easyFactorToCliffordRzBound * easyBound n := by
            rfl
    _ ≤ easyFactorToCliffordRzBound * (5 * 4 ^ n) := by
            exact Nat.mul_le_mul_left easyFactorToCliffordRzBound
              (easyBound_le_five_mul_four_pow n)
    _ = (5 * easyFactorToCliffordRzBound) * 4 ^ n := by
            ring

end Universal
end Clifford
end TwoControl

import TwoControl.Clifford.Universal.RecursiveDecomposition

namespace TwoControl
namespace Clifford
namespace Universal

/-!
This file records the bridge from the recursive easy-gate decomposition to
Clifford+`R_z`.  The two-qubit part uses the already-proved Lemma 11.  The
arbitrary `n`-qubit replacement theorem uses the concrete placement API from
`GateSets.lean` to lift one- and two-qubit circuits into the ambient space.
-/

/-- Concrete two-qubit replacement supplied by the existing Lemma 11 proof. -/
theorem two_qubit_gate_has_clifford_rz_circuit (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ gates : List TwoQubitPrimitive,
      GlobalPhaseEquivalent U (twoQubitCircuitMatrix gates) :=
  lemma11_two_qubit_synthesis U hU

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
    simp [phaseS, phaseSdagger, diag2, Matrix.mul_apply, Fin.sum_univ_two]

private lemma phaseT_six_eq_phaseSdagger :
    phaseT * phaseT * phaseT * phaseT * phaseT * phaseT = phaseSdagger := by
  calc
    phaseT * phaseT * phaseT * phaseT * phaseT * phaseT
        = (phaseT * phaseT) * ((phaseT * phaseT) * (phaseT * phaseT)) := by
            simp [mul_assoc]
    _ = phaseS * (phaseS * phaseS) := by rw [phaseT_sq_eq_phaseS]
    _ = phaseSdagger := by simpa [mul_assoc] using phaseS_cubed_eq_phaseSdagger

private lemma localOnFirst_mul (A B : Square 2) :
    localOnFirst (A * B) = localOnFirst A * localOnFirst B := by
  unfold localOnFirst
  simpa using
    (KronHelpers.kron_mul_reindex (A := A) (B := B)
      (C := (1 : Square 2)) (D := (1 : Square 2)))

private lemma localOnSecond_mul (A B : Square 2) :
    localOnSecond (A * B) = localOnSecond A * localOnSecond B := by
  unfold localOnSecond
  simpa using
    (KronHelpers.kron_mul_reindex (A := (1 : Square 2)) (B := (1 : Square 2))
      (C := A) (D := B))

private lemma oneQubitHT_phaseS :
    oneQubitHTCircuitMatrix [.t, .t] = phaseS := by
  simpa [oneQubitHTCircuitMatrix, OneQubitHTPrimitive.eval] using phaseT_sq_eq_phaseS

private lemma oneQubitHT_phaseSdagger :
    oneQubitHTCircuitMatrix [.t, .t, .t, .t, .t, .t] = phaseSdagger := by
  calc
    oneQubitHTCircuitMatrix [.t, .t, .t, .t, .t, .t]
        = phaseT * phaseT * phaseT * phaseT * phaseT * phaseT := by
            simp [oneQubitHTCircuitMatrix, OneQubitHTPrimitive.eval, mul_assoc]
    _ = phaseSdagger := phaseT_six_eq_phaseSdagger

private lemma twoQubitCliffordT_onFirst_phaseS :
    twoQubitCliffordTCircuitMatrix [.onFirst .t, .onFirst .t] =
      localOnFirst phaseS := by
  calc
    twoQubitCliffordTCircuitMatrix [.onFirst .t, .onFirst .t]
        = localOnFirst phaseT * localOnFirst phaseT := by
            simp [twoQubitCliffordTCircuitMatrix, TwoQubitCliffordTPrimitive.eval,
              OneQubitHTPrimitive.eval]
    _ = localOnFirst (phaseT * phaseT) := by rw [← localOnFirst_mul]
    _ = localOnFirst phaseS := by rw [phaseT_sq_eq_phaseS]

private lemma twoQubitCliffordT_onSecond_phaseS :
    twoQubitCliffordTCircuitMatrix [.onSecond .t, .onSecond .t] =
      localOnSecond phaseS := by
  calc
    twoQubitCliffordTCircuitMatrix [.onSecond .t, .onSecond .t]
        = localOnSecond phaseT * localOnSecond phaseT := by
            simp [twoQubitCliffordTCircuitMatrix, TwoQubitCliffordTPrimitive.eval,
              OneQubitHTPrimitive.eval]
    _ = localOnSecond (phaseT * phaseT) := by rw [← localOnSecond_mul]
    _ = localOnSecond phaseS := by rw [phaseT_sq_eq_phaseS]

private lemma twoQubitCliffordT_onFirst_phaseSdagger :
    twoQubitCliffordTCircuitMatrix
        [.onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t] =
      localOnFirst phaseSdagger := by
  calc
    twoQubitCliffordTCircuitMatrix
        [.onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t]
        = localOnFirst phaseT *
            (localOnFirst phaseT *
              (localOnFirst phaseT *
                (localOnFirst phaseT * (localOnFirst phaseT * localOnFirst phaseT)))) := by
            simp [twoQubitCliffordTCircuitMatrix, TwoQubitCliffordTPrimitive.eval,
              OneQubitHTPrimitive.eval]
    _ = localOnFirst
            (phaseT * (phaseT * (phaseT * (phaseT * (phaseT * phaseT))))) := by
            repeat rw [← localOnFirst_mul]
    _ = localOnFirst (phaseT * phaseT * phaseT * phaseT * phaseT * phaseT) := by
            congr 1
            simp [mul_assoc]
    _ = localOnFirst phaseSdagger := by rw [phaseT_six_eq_phaseSdagger]

private lemma twoQubitCliffordT_onSecond_phaseSdagger :
    twoQubitCliffordTCircuitMatrix
        [.onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t,
          .onSecond .t] =
      localOnSecond phaseSdagger := by
  calc
    twoQubitCliffordTCircuitMatrix
        [.onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t,
          .onSecond .t]
        = localOnSecond phaseT *
            (localOnSecond phaseT *
              (localOnSecond phaseT *
                (localOnSecond phaseT * (localOnSecond phaseT * localOnSecond phaseT)))) := by
            simp [twoQubitCliffordTCircuitMatrix, TwoQubitCliffordTPrimitive.eval,
              OneQubitHTPrimitive.eval]
    _ = localOnSecond
            (phaseT * (phaseT * (phaseT * (phaseT * (phaseT * phaseT))))) := by
            repeat rw [← localOnSecond_mul]
    _ = localOnSecond (phaseT * phaseT * phaseT * phaseT * phaseT * phaseT) := by
            congr 1
            simp [mul_assoc]
    _ = localOnSecond phaseSdagger := by rw [phaseT_six_eq_phaseSdagger]

private theorem reindexSquare_smul {N M : ℕ} (e : Fin N ≃ Fin M)
    (z : ℂ) (U : Square N) :
    reindexSquare e (z • U) = z • reindexSquare e U := by
  simp [reindexSquare]

private theorem castSquare_smul {N M : ℕ} (h : N = M)
    (z : ℂ) (U : Square N) :
    castSquare h (z • U) = z • castSquare h U := by
  simpa [castSquare] using reindexSquare_smul (Equiv.cast (congrArg Fin h)) z U

private theorem TwoQubitPlacement.tensor_smul {n : ℕ} (p : TwoQubitPlacement n)
    (z : ℂ) (U : Square 4) :
    p.tensor (z • U) = z • p.tensor U := by
  unfold TwoQubitPlacement.tensor
  rw [kron_smul_left, KronHelpers.kron_smul_right]

private theorem TwoQubitPlacement.embed_smul {n : ℕ} (p : TwoQubitPlacement n)
    (z : ℂ) (U : Square 4) :
    p.embed (z • U) = z • p.embed U := by
  unfold TwoQubitPlacement.embed
  rw [TwoQubitPlacement.tensor_smul, castSquare_smul, reindexSquare_smul]

private theorem TwoQubitPlacement.globalPhaseEquivalent {n : ℕ}
    (p : TwoQubitPlacement n) {A B : Square 4}
    (hAB : GlobalPhaseEquivalent A B) :
    GlobalPhaseEquivalent (p.embed A) (p.embed B) := by
  rcases hAB with ⟨z, hz, hA⟩
  refine ⟨z, hz, ?_⟩
  rw [hA, p.embed_smul]

/-- Lift a concrete two-qubit Clifford+`R_z` circuit into the same embedded
two-qubit placement. -/
theorem embedded_two_qubit_clifford_rz_lift {n : ℕ} {V : Square 4}
    {U : Square (2 ^ n)}
    (hEmbed : IsEmbeddedTwoQubitGate n V U)
    (hSynth : ∃ gates : List TwoQubitPrimitive,
      GlobalPhaseEquivalent V (twoQubitCircuitMatrix gates)) :
    SynthesizesUpToGlobalPhase (CliffordTRzGate n) U := by
  rcases hEmbed with ⟨p, rfl⟩
  rcases hSynth with ⟨gates, hPhase⟩
  refine ⟨embedTwoQubitCircuit p gates,
    CircuitOver_embedTwoQubitCircuit_cliffordTRz p gates, ?_⟩
  exact GlobalPhaseEquivalent.trans
    (TwoQubitPlacement.globalPhaseEquivalent p hPhase)
    (GlobalPhaseEquivalent.of_eq (circuitMatrix_embedTwoQubitCircuit p gates).symm)

private theorem synthesizes_to_global_phase {N : ℕ} {allowed : Square N → Prop}
    {U : Square N} (hU : Synthesizes allowed U) :
    SynthesizesUpToGlobalPhase allowed U := by
  rcases hU with ⟨gates, hGates, hEq⟩
  exact ⟨gates, hGates, GlobalPhaseEquivalent.of_eq hEq⟩

private theorem clifford_t_gate_is_clifford_t_rz {n : ℕ} {U : Square (2 ^ n)}
    (hU : CliffordTGate n U) :
    CliffordTRzGate n U := by
  rcases hU with hCnot | hH | hT
  · exact Or.inl hCnot
  · exact Or.inr (Or.inl hH)
  · exact Or.inr (Or.inr (Or.inl hT))

private theorem clifford_t_synthesis_is_clifford_t_rz {n : ℕ}
    {U : Square (2 ^ n)}
    (hU : SynthesizesUpToGlobalPhase (CliffordTGate n) U) :
    SynthesizesUpToGlobalPhase (CliffordTRzGate n) U := by
  rcases hU with ⟨gates, hGates, hPhase⟩
  refine ⟨gates, ?_, hPhase⟩
  intro gate hmem
  exact clifford_t_gate_is_clifford_t_rz (hGates gate hmem)

/-- `S` can be treated as a Clifford+T gate because `S = T*T`.

The concrete two-qubit Clifford track already proves this identity internally;
the arbitrary `n`-qubit version will become a small embedding lemma once
one-qubit placements are formalized. -/
theorem embedded_phaseS_is_clifford_t {n : ℕ} {U : Square (2 ^ n)}
    (hU : IsEmbeddedOneQubitGate n phaseS U) :
    SynthesizesUpToGlobalPhase (CliffordTGate n) U := by
  apply synthesizes_to_global_phase
  rcases hU with ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
  · refine ⟨embedOneQubitHTCircuit p [.t, .t],
      CircuitOver_embedOneQubitHTCircuit_cliffordT p [.t, .t], ?_⟩
    rw [circuitMatrix_embedOneQubitHTCircuit, oneQubitHT_phaseS]
  · refine ⟨embedTwoQubitCliffordTCircuit p [.onFirst .t, .onFirst .t],
      CircuitOver_embedTwoQubitCliffordTCircuit_cliffordT p [.onFirst .t, .onFirst .t], ?_⟩
    rw [circuitMatrix_embedTwoQubitCliffordTCircuit, twoQubitCliffordT_onFirst_phaseS]
  · refine ⟨embedTwoQubitCliffordTCircuit p [.onSecond .t, .onSecond .t],
      CircuitOver_embedTwoQubitCliffordTCircuit_cliffordT p [.onSecond .t, .onSecond .t], ?_⟩
    rw [circuitMatrix_embedTwoQubitCliffordTCircuit, twoQubitCliffordT_onSecond_phaseS]

/-- `S†` can be treated as a Clifford+T gate because `S† = T^6`.

This is the embedded version of the identity already used in the concrete
two-qubit Lemma 11 proof. -/
theorem embedded_phaseSdagger_is_clifford_t {n : ℕ} {U : Square (2 ^ n)}
    (hU : IsEmbeddedOneQubitGate n phaseSdagger U) :
    SynthesizesUpToGlobalPhase (CliffordTGate n) U := by
  apply synthesizes_to_global_phase
  rcases hU with ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
  · refine ⟨embedOneQubitHTCircuit p [.t, .t, .t, .t, .t, .t],
      CircuitOver_embedOneQubitHTCircuit_cliffordT p [.t, .t, .t, .t, .t, .t], ?_⟩
    rw [circuitMatrix_embedOneQubitHTCircuit, oneQubitHT_phaseSdagger]
  · refine ⟨embedTwoQubitCliffordTCircuit p
        [.onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t],
      CircuitOver_embedTwoQubitCliffordTCircuit_cliffordT p
        [.onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t, .onFirst .t],
      ?_⟩
    rw [circuitMatrix_embedTwoQubitCliffordTCircuit,
      twoQubitCliffordT_onFirst_phaseSdagger]
  · refine ⟨embedTwoQubitCliffordTCircuit p
        [.onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t,
          .onSecond .t],
      CircuitOver_embedTwoQubitCliffordTCircuit_cliffordT p
        [.onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t, .onSecond .t,
          .onSecond .t],
      ?_⟩
    rw [circuitMatrix_embedTwoQubitCliffordTCircuit,
      twoQubitCliffordT_onSecond_phaseSdagger]

/-- Replacement of one easy-gate factor by a Clifford+`R_z` circuit. -/
theorem easy_gate_factor_to_clifford_rz {n : ℕ} {U : Square (2 ^ n)}
    (hU : EasyGate n U) :
    SynthesizesUpToGlobalPhase (CliffordTRzGate n) U := by
  rcases hU with hTwo | hH | hS | hSdag | hRz
  · rcases hTwo with ⟨V, hVunitary, hEmbed⟩
    exact embedded_two_qubit_clifford_rz_lift hEmbed
      (two_qubit_gate_has_clifford_rz_circuit V hVunitary)
  · exact ⟨[U], by
      intro gate hmem
      have hgate : gate = U := by simpa using hmem
      subst gate
      exact Or.inr (Or.inl hH),
      by simp [circuitMatrix, GlobalPhaseEquivalent.refl]⟩
  · exact clifford_t_synthesis_is_clifford_t_rz
      (embedded_phaseS_is_clifford_t hS)
  · exact clifford_t_synthesis_is_clifford_t_rz
      (embedded_phaseSdagger_is_clifford_t hSdag)
  · rcases hRz with ⟨θ, hθ⟩
    exact ⟨[U], by
      intro gate hmem
      have hgate : gate = U := by simpa using hmem
      subst gate
      exact Or.inr (Or.inr (Or.inr ⟨θ, hθ⟩)),
      by simp [circuitMatrix, GlobalPhaseEquivalent.refl]⟩

private theorem circuitOver_append {N : ℕ} {allowed : Square N → Prop}
    {left right : List (Square N)}
    (hleft : CircuitOver allowed left) (hright : CircuitOver allowed right) :
    CircuitOver allowed (left ++ right) := by
  intro gate hmem
  rw [List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact hleft gate hmem
  · exact hright gate hmem

private theorem easy_circuit_matrix_to_clifford_rz {n : ℕ}
    (gates : List (Square (2 ^ n)))
    (hGates : CircuitOver (EasyGate n) gates) :
    SynthesizesUpToGlobalPhase (CliffordTRzGate n) (circuitMatrix gates) := by
  induction gates with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · intro gate hmem
        cases hmem
      · simp [GlobalPhaseEquivalent.refl]
  | cons gate rest ih =>
      have hGateAllowed : EasyGate n gate := hGates gate (by simp)
      have hRestAllowed : CircuitOver (EasyGate n) rest := by
        intro factor hmem
        exact hGates factor (by simp [hmem])
      rcases easy_gate_factor_to_clifford_rz hGateAllowed with
        ⟨gateCircuit, hGateCircuit, hGatePhase⟩
      rcases ih hRestAllowed with ⟨restCircuit, hRestCircuit, hRestPhase⟩
      refine ⟨gateCircuit ++ restCircuit, ?_, ?_⟩
      · exact circuitOver_append hGateCircuit hRestCircuit
      · have hProduct :
            GlobalPhaseEquivalent
              (gate * circuitMatrix rest)
              (circuitMatrix gateCircuit * circuitMatrix restCircuit) :=
          GlobalPhaseEquivalent.mul hGatePhase hRestPhase
        exact GlobalPhaseEquivalent.trans hProduct
          (GlobalPhaseEquivalent.of_eq (circuitMatrix_append gateCircuit restCircuit).symm)

/-- Replace every factor in an easy circuit by a Clifford+`R_z` circuit.

This is the formal bridge where Lemma 11 combines with Lemma 1. -/
theorem easy_circuit_to_clifford_rz {n : ℕ} {U : Square (2 ^ n)}
    (hU : Synthesizes (EasyGate n) U) :
    SynthesizesUpToGlobalPhase (CliffordTRzGate n) U := by
  rcases hU with ⟨gates, hGates, hEq⟩
  rcases easy_circuit_matrix_to_clifford_rz gates hGates with
    ⟨rzGates, hRzGates, hPhase⟩
  exact ⟨rzGates, hRzGates,
    GlobalPhaseEquivalent.trans (GlobalPhaseEquivalent.of_eq hEq) hPhase⟩

/-- Clifford+`R_z` synthesis for arbitrary `n`-qubit unitaries, assuming the
recursive Lemma 1 decomposition. -/
theorem clifford_rz_synthesis_from_lemma1 {n : ℕ} (hn : 2 ≤ n)
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    SynthesizesUpToGlobalPhase (CliffordTRzGate n) U :=
  easy_circuit_to_clifford_rz (lemma1_decomposition_to_easy_gate_set hn U hU)

end Universal
end Clifford
end TwoControl

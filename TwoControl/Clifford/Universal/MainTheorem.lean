import TwoControl.Clifford.Universal.CliffordRz
import TwoControl.Clifford.Universal.RzApproximation

namespace TwoControl
namespace Clifford
namespace Universal

/-!
Final theorem interface for the `universal_new_gates.tex` universality track.

The proof route is:

1. `clifford_rz_universal`: exact synthesis into `{CX, H, S, S†, R_z}` up to
   global phase (paper Lemma `clifford-plus-rx-is-universal`, induction with
   a one-qubit base case);
2. `clifford_rz_to_clifford_t_rz`: rewrite `S = T²`, `S† = T⁶`;
3. Lemma 12 (`lemma12_rz_approximation_by_ht`, the `G₁/G₂` track): replace
   each `R_z` by an `{H,T}` circuit;
4. the distance layer bounds the accumulated error.
-/

private theorem hsDistance_eq_of_globalPhaseEquivalent_left {N : ℕ}
    {U V W : Square N} (h : GlobalPhaseEquivalent U V) :
    hsDistance U W = hsDistance V W := by
  rcases h with ⟨z, hz, hUV⟩
  rw [hUV]
  unfold hsDistance
  have htrace :
      Matrix.trace ((z • V)† * W) = star z * Matrix.trace (V† * W) := by
    calc
      Matrix.trace ((z • V)† * W)
          = Matrix.trace ((star z • V†) * W) := by simp
      _ = Matrix.trace (star z • (V† * W)) := by rw [Matrix.smul_mul]
      _ = star z * Matrix.trace (V† * W) := by simp
  have hnorm : ‖star z * Matrix.trace (V† * W)‖ = ‖Matrix.trace (V† * W)‖ := by
    rw [norm_mul]
    simp [hz]
  rw [htrace, hnorm]

private theorem circuitMatrix_mem_unitaryGroup {N : ℕ}
    {allowed : Square N → Prop} {gates : List (Square N)}
    (hAllowedUnitary :
      ∀ {gate : Square N}, allowed gate → gate ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hGates : CircuitOver allowed gates) :
    circuitMatrix gates ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  induction gates with
  | nil =>
      simp
  | cons gate gates ih =>
      have hgate : gate ∈ Matrix.unitaryGroup (Fin N) ℂ :=
        hAllowedUnitary (hGates gate (by simp))
      have htail : circuitMatrix gates ∈ Matrix.unitaryGroup (Fin N) ℂ := by
        apply ih
        intro tailGate htailGate
        exact hGates tailGate (by simp [htailGate])
      simpa [circuitMatrix] using
        (Submonoid.mul_mem (Matrix.unitaryGroup (Fin N) ℂ) hgate htail)

private theorem clifford_trz_gate_as_clifford_t_or_rz {n : ℕ}
    {gate : Square (2 ^ n)} (hgate : CliffordTRzGate n gate) :
    CliffordTGate n gate ∨ ∃ θ : ℝ, IsEmbeddedOneQubitGate n (rz θ) gate := by
  rcases hgate with hCnot | hH | hT | hRz
  · exact Or.inl (Or.inl hCnot)
  · exact Or.inl (Or.inr (Or.inl hH))
  · exact Or.inl (Or.inr (Or.inr hT))
  · exact Or.inr hRz

private theorem one_gate_replacement {n : ℕ} (hn : 0 < 2 ^ n)
    {gate : Square (2 ^ n)} (hgate : CliffordTRzGate n gate)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ replacement : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) replacement ∧
      hsDistance gate (circuitMatrix replacement) < δ ∧
      circuitMatrix replacement ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rcases clifford_trz_gate_as_clifford_t_or_rz hgate with hCliffordT | hRz
  · refine ⟨[gate], ?_, ?_, ?_⟩
    · intro candidate hcandidate
      have hcandidate_eq : candidate = gate := by
        simpa using hcandidate
      simpa [hcandidate_eq] using hCliffordT
    · have hunit : gate ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
        CliffordTGate.mem_unitaryGroup hCliffordT
      have hzero : hsDistance gate (circuitMatrix [gate]) = 0 := by
        simpa using hsDistance_self hn gate hunit
      rw [hzero]
      exact hδ
    · simpa using CliffordTGate.mem_unitaryGroup hCliffordT
  · rcases hRz with ⟨θ, hEmbedded⟩
    rcases embedded_rz_approximation_by_clifford_t (n := n)
        (R := gate) (θ := θ) hδ hEmbedded with
      ⟨replacement, hReplacement, hDistance⟩
    refine ⟨replacement, hReplacement, hDistance, ?_⟩
    exact circuitMatrix_mem_unitaryGroup
      (allowed := CliffordTGate n)
      (fun hAllowed => CliffordTGate.mem_unitaryGroup hAllowed)
      hReplacement

private theorem clifford_rz_circuit_replacement {n : ℕ} (hn : 0 < 2 ^ n)
    {gates : List (Square (2 ^ n))}
    (hGates : CircuitOver (CliffordTRzGate n) gates)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ replacement : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) replacement ∧
      hsDistance (circuitMatrix gates) (circuitMatrix replacement) ≤
        (gates.length : ℝ) * δ ∧
      circuitMatrix replacement ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  induction gates with
  | nil =>
      refine ⟨[], ?_, ?_, ?_⟩
      · intro gate hgate
        simp at hgate
      · have hone : (1 : Square (2 ^ n)) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
          Submonoid.one_mem (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
        have hzero : hsDistance (circuitMatrix ([] : List (Square (2 ^ n))))
            (circuitMatrix ([] : List (Square (2 ^ n)))) = 0 := by
          simpa using hsDistance_self hn (1 : Square (2 ^ n)) hone
        rw [hzero]
        simp
      · simp
  | cons gate tail ih =>
      have hgate : CliffordTRzGate n gate := hGates gate (by simp)
      have htail : CircuitOver (CliffordTRzGate n) tail := by
        intro tailGate htailGate
        exact hGates tailGate (by simp [htailGate])
      rcases one_gate_replacement hn hgate hδ with
        ⟨gateReplacement, hGateReplacement, hGateDistance, hGateUnitary⟩
      rcases ih htail with
        ⟨tailReplacement, hTailReplacement, hTailDistance, hTailUnitary⟩
      refine ⟨gateReplacement ++ tailReplacement, ?_, ?_, ?_⟩
      · intro candidate hcandidate
        rcases List.mem_append.mp hcandidate with hcandidate | hcandidate
        · exact hGateReplacement candidate hcandidate
        · exact hTailReplacement candidate hcandidate
      · have hOriginalGateUnitary :
            gate ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
          CliffordTRzGate.mem_unitaryGroup hgate
        have hOriginalTailUnitary :
            circuitMatrix tail ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
          circuitMatrix_mem_unitaryGroup
            (allowed := CliffordTRzGate n)
            (fun hAllowed => CliffordTRzGate.mem_unitaryGroup hAllowed)
            htail
        have hProduct := hsDistance_mul_le hn gate (circuitMatrix tail)
          (circuitMatrix gateReplacement) (circuitMatrix tailReplacement)
          hOriginalGateUnitary hOriginalTailUnitary hGateUnitary hTailUnitary
        have hAppend :
            circuitMatrix (gateReplacement ++ tailReplacement) =
              circuitMatrix gateReplacement * circuitMatrix tailReplacement :=
          circuitMatrix_append gateReplacement tailReplacement
        have hDistance :
            hsDistance (circuitMatrix (gate :: tail))
                (circuitMatrix (gateReplacement ++ tailReplacement)) ≤
              hsDistance gate (circuitMatrix gateReplacement) +
                hsDistance (circuitMatrix tail) (circuitMatrix tailReplacement) := by
          rw [hAppend]
          simpa [circuitMatrix] using hProduct
        have hBound :
            hsDistance gate (circuitMatrix gateReplacement) +
                hsDistance (circuitMatrix tail) (circuitMatrix tailReplacement) ≤
              δ + (tail.length : ℝ) * δ :=
          add_le_add (le_of_lt hGateDistance) hTailDistance
        have hTotal :
            hsDistance (circuitMatrix (gate :: tail))
                (circuitMatrix (gateReplacement ++ tailReplacement)) ≤
              δ + (tail.length : ℝ) * δ :=
          le_trans hDistance hBound
        have hArith : δ + (tail.length : ℝ) * δ =
            ((gate :: tail).length : ℝ) * δ := by
          simp
          ring
        simpa [hArith] using hTotal
      · rw [circuitMatrix_append]
        exact Submonoid.mul_mem (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
          hGateUnitary hTailUnitary

/-- Replace all `R_z` factors in a Clifford+`R_z` synthesis using Lemma 12 and
the product-distance bound. -/
theorem clifford_rz_synthesis_approximates_by_clifford_t {n : ℕ}
    (hn : 0 < 2 ^ n)
    (U : Square (2 ^ n))
    (hSynth : SynthesizesUpToGlobalPhase (CliffordTRzGate n) U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      hsDistance U (circuitMatrix gates) < ε := by
  rcases hSynth with ⟨rzGates, hRzGates, hPhase⟩
  let denom : ℝ := (rzGates.length : ℝ) + 1
  let δ : ℝ := ε / denom
  have hDenPos : 0 < denom := by
    dsimp [denom]
    positivity
  have hδ : 0 < δ := div_pos hε hDenPos
  rcases clifford_rz_circuit_replacement hn hRzGates hδ with
    ⟨replacement, hReplacement, hDistance, hReplacementUnitary⟩
  refine ⟨replacement, hReplacement, ?_⟩
  have hOriginalUnitary :
      circuitMatrix rzGates ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
    circuitMatrix_mem_unitaryGroup
      (allowed := CliffordTRzGate n)
      (fun hAllowed => CliffordTRzGate.mem_unitaryGroup hAllowed)
      hRzGates
  have hGlobal :
      hsDistance U (circuitMatrix replacement) =
        hsDistance (circuitMatrix rzGates) (circuitMatrix replacement) :=
    hsDistance_eq_of_globalPhaseEquivalent_left hPhase
  rw [hGlobal]
  refine lt_of_le_of_lt hDistance ?_
  have hLenLt : (rzGates.length : ℝ) * δ < ε := by
    have hlt : (rzGates.length : ℝ) < denom := by
      dsimp [denom]
      linarith
    have hmul : (rzGates.length : ℝ) * ε < denom * ε :=
      mul_lt_mul_of_pos_right hlt hε
    calc
      (rzGates.length : ℝ) * δ
          = (rzGates.length : ℝ) * ε / denom := by
              dsimp [δ]
              ring
      _ < denom * ε / denom := by
              exact div_lt_div_of_pos_right hmul hDenPos
      _ = ε := by
              field_simp [ne_of_gt hDenPos]
  exact hLenLt

/-- Recover a unit-modulus phase from a scalar equation `star z * z = 1`. -/
private theorem norm_eq_one_of_conj_mul_eq_one {z : ℂ} (hz : star z * z = 1) :
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

private theorem one_by_one_globalPhaseEquivalent_one
    (U : Square 1) (hU : U ∈ Matrix.unitaryGroup (Fin 1) ℂ) :
    GlobalPhaseEquivalent U (1 : Square 1) := by
  refine ⟨U 0 0, ?_, ?_⟩
  · apply norm_eq_one_of_conj_mul_eq_one
    have hUnitary : U * star U = (1 : Square 1) := Matrix.mem_unitaryGroup_iff.mp hU
    have hEntry := congrFun (congrFun hUnitary 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_one, mul_comm] using hEntry
  · ext i j
    fin_cases i
    fin_cases j
    simp

private theorem zero_qubit_clifford_t_is_universal
    (U : Square 1)
    (hU : U ∈ Matrix.unitaryGroup (Fin 1) ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square 1),
      CircuitOver (CliffordTGate 0) gates ∧
      hsDistance U (circuitMatrix gates) < ε := by
  refine ⟨[], ?_, ?_⟩
  · intro gate hgate
    simp at hgate
  · have hPhase : GlobalPhaseEquivalent U (1 : Square 1) :=
      one_by_one_globalPhaseEquivalent_one U hU
    have hSelf : hsDistance (1 : Square 1) (1 : Square 1) = 0 := by
      simpa using hsDistance_self (show 0 < 1 by norm_num)
        (1 : Square 1) (Submonoid.one_mem (Matrix.unitaryGroup (Fin 1) ℂ))
    have hZero : hsDistance U (circuitMatrix ([] : List (Square 1))) = 0 := by
      calc
        hsDistance U (circuitMatrix ([] : List (Square 1)))
            = hsDistance U (1 : Square 1) := by simp [circuitMatrix]
        _ = hsDistance (1 : Square 1) (1 : Square 1) :=
            hsDistance_eq_of_globalPhaseEquivalent_left hPhase
        _ = 0 := hSelf
    rw [hZero]
    exact hε

/-- **Clifford+T is universal** (`universal_new_gates.tex`, main theorem).

For `n ≥ 1` the proof is the paper's single path:
`clifford_rz_universal` (exact synthesis into `{CX, H, S, S†, R_z}`, up to
global phase, induction with a one-qubit base case), then
`clifford_rz_to_clifford_t_rz` (`S = T²`, `S† = T⁶`), then the Lemma-12
`R_z`-approximation pipeline.  The zero-qubit case is a trivial phase. -/
theorem clifford_t_is_universal {n : ℕ}
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      hsDistance U (circuitMatrix gates) < ε := by
  cases n with
  | zero =>
      simpa using zero_qubit_clifford_t_is_universal U hU hε
  | succ m =>
      have hdim : 0 < 2 ^ (m + 1) := Nat.pow_pos (by decide : 0 < 2)
      exact clifford_rz_synthesis_approximates_by_clifford_t hdim U
        (clifford_rz_to_clifford_t_rz
          (clifford_rz_universal (Nat.succ_le_succ (Nat.zero_le m)) U hU)) hε

end Universal
end Clifford
end TwoControl

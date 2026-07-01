import TwoControl.Clifford.Universal.GateSets

namespace TwoControl
namespace Clifford
namespace Universal

/-!
Bounded synthesis predicates for the Clifford+T universality track.

These are length-refined versions of `Synthesizes` and
`SynthesizesUpToGlobalPhase`.  They are intentionally generic over the gate-set
predicate so the recursive easy-gate bound and the Clifford+`R_z` bridge can
share the same list algebra.
-/

/-- Exact synthesis by a gate set with an upper bound on circuit length. -/
def SynthesizesWithLength {N : ℕ}
    (allowed : Square N → Prop) (U : Square N) (bound : ℕ) : Prop :=
  ∃ gates : List (Square N),
    CircuitOver allowed gates ∧
    U = circuitMatrix gates ∧
    gates.length ≤ bound

/-- Synthesis up to global phase by a gate set with an upper bound on circuit
length. -/
def SynthesizesUpToGlobalPhaseWithLength {N : ℕ}
    (allowed : Square N → Prop) (U : Square N) (bound : ℕ) : Prop :=
  ∃ gates : List (Square N),
    CircuitOver allowed gates ∧
    GlobalPhaseEquivalent U (circuitMatrix gates) ∧
    gates.length ≤ bound

theorem SynthesizesWithLength.toSynthesizes {N : ℕ}
    {allowed : Square N → Prop} {U : Square N} {bound : ℕ}
    (h : SynthesizesWithLength allowed U bound) :
    Synthesizes allowed U := by
  rcases h with ⟨gates, hGates, hEq, _hLen⟩
  exact ⟨gates, hGates, hEq⟩

theorem SynthesizesUpToGlobalPhaseWithLength.toSynthesizesUpToGlobalPhase {N : ℕ}
    {allowed : Square N → Prop} {U : Square N} {bound : ℕ}
    (h : SynthesizesUpToGlobalPhaseWithLength allowed U bound) :
    SynthesizesUpToGlobalPhase allowed U := by
  rcases h with ⟨gates, hGates, hPhase, _hLen⟩
  exact ⟨gates, hGates, hPhase⟩

theorem SynthesizesWithLength.toUpToGlobalPhaseWithLength {N : ℕ}
    {allowed : Square N → Prop} {U : Square N} {bound : ℕ}
    (h : SynthesizesWithLength allowed U bound) :
    SynthesizesUpToGlobalPhaseWithLength allowed U bound := by
  rcases h with ⟨gates, hGates, hEq, hLen⟩
  exact ⟨gates, hGates, GlobalPhaseEquivalent.of_eq hEq, hLen⟩

theorem SynthesizesWithLength.mono_bound {N : ℕ}
    {allowed : Square N → Prop} {U : Square N} {bound₁ bound₂ : ℕ}
    (hBound : bound₁ ≤ bound₂)
    (h : SynthesizesWithLength allowed U bound₁) :
    SynthesizesWithLength allowed U bound₂ := by
  rcases h with ⟨gates, hGates, hEq, hLen⟩
  exact ⟨gates, hGates, hEq, le_trans hLen hBound⟩

theorem SynthesizesUpToGlobalPhaseWithLength.mono_bound {N : ℕ}
    {allowed : Square N → Prop} {U : Square N} {bound₁ bound₂ : ℕ}
    (hBound : bound₁ ≤ bound₂)
    (h : SynthesizesUpToGlobalPhaseWithLength allowed U bound₁) :
    SynthesizesUpToGlobalPhaseWithLength allowed U bound₂ := by
  rcases h with ⟨gates, hGates, hPhase, hLen⟩
  exact ⟨gates, hGates, hPhase, le_trans hLen hBound⟩

theorem synthesizesWithLength_singleton {N : ℕ}
    {allowed : Square N → Prop} {U : Square N}
    (hU : allowed U) :
    SynthesizesWithLength allowed U 1 := by
  refine ⟨[U], ?_, ?_, ?_⟩
  · intro gate hgate
    rw [List.mem_singleton] at hgate
    subst gate
    exact hU
  · simp [circuitMatrix]
  · simp

theorem synthesizesUpToGlobalPhaseWithLength_singleton {N : ℕ}
    {allowed : Square N → Prop} {U : Square N}
    (hU : allowed U) :
    SynthesizesUpToGlobalPhaseWithLength allowed U 1 :=
  (synthesizesWithLength_singleton hU).toUpToGlobalPhaseWithLength

theorem synthesizesWithLength_mul {N : ℕ}
    {allowed : Square N → Prop} {U V : Square N} {boundU boundV : ℕ}
    (hU : SynthesizesWithLength allowed U boundU)
    (hV : SynthesizesWithLength allowed V boundV) :
    SynthesizesWithLength allowed (U * V) (boundU + boundV) := by
  rcases hU with ⟨gatesU, hGatesU, hEqU, hLenU⟩
  rcases hV with ⟨gatesV, hGatesV, hEqV, hLenV⟩
  refine ⟨gatesU ++ gatesV, CircuitOver_append hGatesU hGatesV, ?_, ?_⟩
  · rw [hEqU, hEqV, circuitMatrix_append]
  · rw [List.length_append]
    exact Nat.add_le_add hLenU hLenV

theorem synthesizesUpToGlobalPhaseWithLength_mul {N : ℕ}
    {allowed : Square N → Prop} {U V : Square N} {boundU boundV : ℕ}
    (hU : SynthesizesUpToGlobalPhaseWithLength allowed U boundU)
    (hV : SynthesizesUpToGlobalPhaseWithLength allowed V boundV) :
    SynthesizesUpToGlobalPhaseWithLength allowed (U * V) (boundU + boundV) := by
  rcases hU with ⟨gatesU, hGatesU, hPhaseU, hLenU⟩
  rcases hV with ⟨gatesV, hGatesV, hPhaseV, hLenV⟩
  refine ⟨gatesU ++ gatesV, CircuitOver_append hGatesU hGatesV, ?_, ?_⟩
  · exact GlobalPhaseEquivalent.trans
      (GlobalPhaseEquivalent.mul hPhaseU hPhaseV)
      (GlobalPhaseEquivalent.of_eq (circuitMatrix_append gatesU gatesV).symm)
  · rw [List.length_append]
    exact Nat.add_le_add hLenU hLenV

end Universal
end Clifford
end TwoControl


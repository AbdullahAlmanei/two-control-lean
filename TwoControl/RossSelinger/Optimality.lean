import TwoControl.RossSelinger.Correctness

namespace TwoControl.RossSelinger

open DyadicCyclotomic

/-!
Conditional `T`-count optimality for the Ross-Selinger Rz-approximation
algorithm with a factoring oracle:

> *If the oracle algorithm returns a circuit, that circuit minimizes `TCount`
> among all Clifford+T circuits ε-approximating `Rz θ`.*

`RSOracleSolver.complete` is the Diophantine-oracle promise.  The current
search trace proves the enumeration part of the paper's argument: once a
candidate returns at level `k`, the oracle cannot have skipped a completable
candidate from any lower level.

The competitor side is factored along the paper's proof:

* Lemma 7.8/7.9 put any relevant competitor into completion-matrix form,
  yielding a scaled-grid candidate with a norm-equation solution;
* the fixed-level grid enumerator exposes that candidate at its least
  denominator exponent; and
* the KMM/Ma denominator-exponent theorem gives the `T`-count lower bound
  for that competitor.
-/

/-- The circuit `C` ε-approximates `Rz θ` and no circuit with the same
property has a smaller `T`-count. -/
def IsOptimalRzApproxByTCount (θ ε : ℝ) (C : CliffordTCircuit) : Prop :=
  IsRzApproxCircuit θ ε C ∧
    ∀ C', IsRzApproxCircuit θ ε C' → TCount C ≤ TCount C'

/-- A scaled-grid candidate admits a Ross-Selinger norm-equation completion. -/
def CandidateCompletable {θ ε : ℝ} (candidate : RSCandidate θ ε) : Prop :=
  ∃ t : ℂ, SolvesNormEquation (completionXi candidate.u) t

/-- Paper-side normal form extracted from a competing Clifford+T circuit.

This is the Lean boundary for Ross-Selinger's Lemma 7.8/7.9 plus the
Diophantine reduction: the competitor supplies an entry `u`, a completion `t`,
least-denominator metadata for `u`, and a norm-equation certificate. -/
structure RSCompetitorForm (input : RSInput) (C : CliffordTCircuit) where
  level : ℕ
  u : ℂ
  t : ℂ
  hFixed : FixedDenominatorScaledGridCandidate input.θ input.ε level u
  hLeast : IsLeastDenominatorExponent u level
  hSolve : SolvesNormEquation (completionXi u) t

namespace RSCompetitorForm

/-- The scaled-grid candidate induced by a competitor normal form. -/
def candidate {input : RSInput} {C : CliffordTCircuit}
    (form : RSCompetitorForm input C) : RSCandidate input.θ input.ε :=
  { level := form.level
    u := form.u
    hFixed := form.hFixed
    hLeast := form.hLeast }

@[simp] theorem candidate_level {input : RSInput} {C : CliffordTCircuit}
    (form : RSCompetitorForm input C) :
    form.candidate.level = form.level := rfl

@[simp] theorem candidate_u {input : RSInput} {C : CliffordTCircuit}
    (form : RSCompetitorForm input C) :
    form.candidate.u = form.u := rfl

/-- The competitor-induced candidate is completable by its extracted `t`. -/
theorem candidate_completable {input : RSInput} {C : CliffordTCircuit}
    (form : RSCompetitorForm input C) :
    CandidateCompletable form.candidate := by
  exact ⟨form.t, by simpa using form.hSolve⟩

end RSCompetitorForm

/-- The paper facts that remain after the oracle search-order proof.

The returned branch of Lemma 7.10 is part of the completion solver's successful
result certificate and is exposed as `returned_branch_tcount_le_level` below.
The three fields here are the competitor/lower-bound side of Proposition 7.11:
competitor normal form, fixed-level enumeration completeness, and the KMM/Ma
denominator-exponent lower bound. -/
structure RSOracleOptimalityBridge (oracle : RSOracleSolver) where
  competitor_form :
    ∀ (input : RSInput) {C : CliffordTCircuit},
      IsRzApproxCircuit input.θ input.ε C →
        RSCompetitorForm input C
  enumerates_competitor :
    ∀ (input : RSInput) {C : CliffordTCircuit}
      (hApprox : IsRzApproxCircuit input.θ input.ε C),
        let form := competitor_form input hApprox
        form.candidate ∈
          oracle.completionSolver.candidatesAtLevel input form.candidate.level
  competitor_tcount_lower_bound :
    ∀ (input : RSInput) {C : CliffordTCircuit}
      (hApprox : IsRzApproxCircuit input.θ input.ε C),
        let form := competitor_form input hApprox
        rossLevelTCount form.candidate.level ≤ TCount C

/-- The returned branch has the Ross-Selinger/KMM `0` or `2k - 2` T-count
bound promised by the successful synthesis certificate. -/
theorem returned_branch_tcount_le_level {θ ε : ℝ}
    (completed : CompletedCandidate θ ε) :
    TCount completed.synthesize ≤ rossLevelTCount completed.candidate.level :=
  completed.tcount_synthesize

/-- A competing approximating circuit induces the completable scaled-grid
candidate that the oracle search must have considered, together with the KMM
denominator/T-count lower bound for that competitor. -/
theorem competing_candidate_of_lower_bound_bridge
    (oracle : RSOracleSolver)
    (bridge : RSOracleOptimalityBridge oracle)
    (input : RSInput) {C : CliffordTCircuit}
    (hApprox : IsRzApproxCircuit input.θ input.ε C) :
    ∃ candidate : RSCandidate input.θ input.ε,
      candidate ∈
          oracle.completionSolver.candidatesAtLevel input candidate.level ∧
        CandidateCompletable candidate ∧
          rossLevelTCount candidate.level ≤ TCount C := by
  let form := bridge.competitor_form input hApprox
  refine ⟨form.candidate, ?_, ?_, ?_⟩
  · simpa [form] using bridge.enumerates_competitor input hApprox
  · exact form.candidate_completable
  · simpa [form] using bridge.competitor_tcount_lower_bound input hApprox

/-- An oracle return has minimum denominator level among completable candidates
that the fixed-level grid enumerator exposes. -/
theorem returned_level_le_of_oracle_completable_candidate
    (oracle : RSOracleSolver) (fuel : ℕ) (input : RSInput)
    {completed : CompletedCandidate input.θ input.ε}
    (hrun :
      rossSelingerCompletedSearch oracle.completionSolver fuel input =
        some completed)
    {candidate : RSCandidate input.θ input.ε}
    (hmem :
      candidate ∈
        oracle.completionSolver.candidatesAtLevel input candidate.level)
    (hcomplete : CandidateCompletable candidate) :
    completed.candidate.level ≤ candidate.level := by
  by_contra hnot
  have hlt : candidate.level < completed.candidate.level := by omega
  have hnone :=
    solve_eq_none_of_level_lt_returned_level oracle.completionSolver fuel input
      hrun hlt hmem
  rcases oracle.complete candidate hcomplete with ⟨completion, hcompletion⟩
  rw [hnone] at hcompletion
  simp at hcompletion

/-- **Conditional `T`-count optimality** for the oracle variant of the
Ross-Selinger search. -/
theorem rossSelingerOracle_optimal_if_returns
    (oracle : RSOracleSolver)
    (bridge : RSOracleOptimalityBridge oracle)
    (fuel : ℕ)
    (input : RSInput) {C : CliffordTCircuit}
    (hrun : rossSelingerOracleSearch oracle fuel input = some C) :
    IsOptimalRzApproxByTCount input.θ input.ε C := by
  rcases exists_completed_of_rossSelingerSearch_eq_some oracle.completionSolver
      fuel input hrun with ⟨completed, hcompleted, hC⟩
  refine ⟨rossSelingerOracleSearch_sound_if_returns oracle fuel input hrun, ?_⟩
  intro C' hC'
  rcases competing_candidate_of_lower_bound_bridge oracle bridge input hC' with
    ⟨candidate, hmem, hcomplete, hcompetitor⟩
  have hlevel :=
    returned_level_le_of_oracle_completable_candidate oracle fuel input
      hcompleted hmem hcomplete
  have hreturned :
      TCount C ≤ rossLevelTCount completed.candidate.level := by
    simpa [← hC] using returned_branch_tcount_le_level completed
  exact hreturned.trans ((rossLevelTCount_mono hlevel).trans hcompetitor)

end RossSelinger
end TwoControl

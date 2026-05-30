import TwoControl.RossSelinger.Diophantine
import TwoControl.RossSelinger.MANormalForm
import TwoControl.KMM.ExactSynthesis

namespace TwoControl.RossSelinger

open DyadicCyclotomic
open MatrixCompletion
open TwoControl.Clifford
open TwoControl.KMM
open TwoControl.RossSelinger.Selinger75

/-!
Fuelled, proof-carrying Ross-Selinger search.

The grid and Diophantine engines are intentionally injected as contracts:
`RSCompletionSolver` supplies finite fixed-level candidate batches and attempts
norm-equation completions for those candidates.  A returned candidate already
carries the scaled-grid facts needed by Ross-Selinger correctness, and a
returned completion is accepted only through the solver's soundness law.

This keeps the compiler-facing theorem conditional in exactly the sense of
Algorithm 7.6: no factorization, prime-distribution, or termination theorem is
assumed to prove soundness of a circuit that was actually returned.
-/

/-- Input to the Ross-Selinger Rz-approximation algorithm. -/
structure RSInput where
  θ : ℝ
  ε : ℝ
  hε : 0 < ε

/-- The circuit `C` epsilon-approximates `Rz theta` in operator norm. -/
def IsRzApproxCircuit (θ ε : ℝ) (C : CliffordTCircuit) : Prop :=
  opDist (rz θ) (CliffordTCircuit.eval C) ≤ ε

/-- Raw output of a Diophantine completion attempt.  Soundness lives in the
solver law so partial solvers are not forced to manufacture proof terms in
their runtime payload. -/
structure RSCompletionData where
  t : ℂ

/-! ### Selinger Lemma 7.5 returned branch

Lemma 7.5 says that for a completion matrix with top-left entry `u` at least
denominator exponent `k`, the returned operator may be either `U` or `T U T†`,
and the smaller branch has `T`-count `0` at `k = 0` or `2k - 2` for `k > 0`.

The finite Ma/KMM residue classification is represented below by
`SelingerLemma75Classification`; later definitions discharge all of the branch
plumbing: the `T U T†` branch is converted into the adjusted completion `ω * t`,
its norm equation is proved, and the result is packaged as a `CompletedCandidate`
suitable for the search/correctness layer.
-/

/-- The two possible operator branches in Selinger Lemma 7.5.  This is `Type`,
rather than `Prop`, so that the search layer can extract the returned circuit
and package it as a `CompletedCandidate`. -/
inductive SelingerLemma75Branch {θ ε : ℝ}
    (candidate : RSCandidate θ ε) (completion : RSCompletionData)
    (C : CliffordTCircuit) : Type where
  | direct :
      CliffordTCircuit.eval C = completionMatrix candidate.u completion.t →
        SelingerLemma75Branch candidate completion C
  | phaseT :
      CliffordTCircuit.eval C =
          phaseT * completionMatrix candidate.u completion.t * phaseT† →
        SelingerLemma75Branch candidate completion C

/-- The Ma/KMM finite residue classification content of Selinger Lemma 7.5:
there is a circuit of sharp Ross-Selinger `T`-count implementing either the
completion matrix itself or its `T U T†` branch. -/
structure SelingerLemma75Classification {θ ε : ℝ}
    (candidate : RSCandidate θ ε) (completion : RSCompletionData) where
  circuit : CliffordTCircuit
  branch : SelingerLemma75Branch candidate completion circuit
  tcount : TCount circuit ≤ rossLevelTCount candidate.level

/-! ### Paper-shaped Selinger 7.5 targets

The following statements are the exact high-level seams from the papers. They
currently carry `sorry` where the remaining proof work belongs.

Ross-Selinger Lemma `lem-2k-2` says that for a completion matrix
`[[u, -t†], [t, u†]]`, where `k` is the least denominator exponent of `u`,
one of the direct branch `U` or phase branch `T U T†` has the sharp returned
branch `T`-count: `0` at `k = 0`, otherwise `2k - 2`.

Giles-Selinger's U(2) Figure 2 theorem is the underlying normal-form
classification: a unitary over `D[ω]`, together with its least denominator
exponent and residue, determines the relevant Figure 2 vertex and therefore
the `T`-count offset.
-/

/-- Giles-Selinger U(2)/Figure 2 synthesis theorem, in the exact form needed
by Ross-Selinger: if `U` lies at a Figure 2 vertex at its least denominator
level, then `U` has a Clifford+T implementation with the vertex's printed
`2k - offset` T-count bound.

This is not a selected finite path word evaluating to `U`; it is the
Matsumoto-Amano normal-form theorem behind Figure 2. -/
theorem giles_selinger_u2_figure2_synthesis_bound
    {U : Square 2} {k : ℕ} {R : ResidueMatrix} {node : Figure2Node}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hEntries : MatrixEntriesInDyadicCyclotomic U)
    (hLeast : MatrixLeastOmegaDenominatorExponent U k)
    (hResidue : MatrixHasResidueAtLevel U k R)
    (hNode : node ∈ Figure2.nodes)
    (hR : node.residue = R)
    (hValid : node.ValidAtLevel k) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C = U ∧
        TCount C ≤ 2 * k - node.tOffset := by
  exact ma_normal_form_figure2_synthesis_bound hU hEntries hLeast hResidue
    hNode hR hValid

/-- Ross-Selinger Lemma 7.5 first denominator fact, in the paper's
`D[ω]` denominator convention: in a unitary completion matrix, the two
completion entries `u` and `t` have the same least omega-denominator exponent.

This deliberately uses `omegaSDE`, not the legacy scaled-grid coordinate
predicate `IsLeastDenominatorExponent`; the latter is a coordinate-enumerator
artifact and is not the denominator exponent used in Giles-Selinger Figure 2.
-/
theorem completion_same_least_omega_denominator_exponent {θ ε : ℝ}
    (candidate : RSCandidate θ ε) {completion : RSCompletionData}
    (hSolve : SolvesNormEquation (completionXi candidate.u) completion.t) :
    omegaSDE completion.t = omegaSDE candidate.u := by
  exact omegaSDE_eq_of_normEquation candidate.inDyadicCyclotomic hSolve.1
    (normEquation_of_solves_completionXi hSolve)

/-- The paper denominator level of a Ross candidate is bounded by the grid
level carried by the current enumerator.  The enumerator level is the older
coordinate denominator convention; `omegaSDE` is the Giles-Selinger/Ross
denominator convention. -/
theorem omegaSDE_candidate_le_level {θ ε : ℝ}
    (candidate : RSCandidate θ ε) :
    omegaSDE candidate.u ≤ candidate.level := by
  have huOmega : HasOmegaDenominatorExponent candidate.u candidate.level :=
    hasOmegaDenominatorExponent_of_hasDenominatorExponent
      candidate.hasDenominatorExponent
  exact omegaSDE_le_of_hasOmegaDenominatorExponent huOmega

/-- Matrix-level least-denominator fact for the actual completion matrix
returned by a solved Ross candidate, stated in the paper's omega-denominator
convention. -/
theorem completionMatrix_candidate_leastOmegaDenominatorExponent {θ ε : ℝ}
    (candidate : RSCandidate θ ε) {completion : RSCompletionData}
    (hSolve : SolvesNormEquation (completionXi candidate.u) completion.t) :
    MatrixLeastOmegaDenominatorExponent
      (completionMatrix candidate.u completion.t)
      (omegaSDE candidate.u) := by
  exact completionMatrix_leastOmegaDenominatorExponent_of_normEquation
    candidate.inDyadicCyclotomic hSolve.1
    (normEquation_of_solves_completionXi hSolve)

/-- A solved Ross completion matrix is unitary. -/
theorem completionMatrix_candidate_mem_unitaryGroup {θ ε : ℝ}
    (candidate : RSCandidate θ ε) {completion : RSCompletionData}
    (hSolve : SolvesNormEquation (completionXi candidate.u) completion.t) :
    completionMatrix candidate.u completion.t ∈
      Matrix.unitaryGroup (Fin 2) ℂ :=
  completionMatrix_mem_unitaryGroup
    (normEquation_of_solves_completionXi hSolve)

/-- A solved Ross completion matrix has entries in `D[ω]`. -/
theorem completionMatrix_candidate_entries_in_dyadic {θ ε : ℝ}
    (candidate : RSCandidate θ ε) {completion : RSCompletionData}
    (hSolve : SolvesNormEquation (completionXi candidate.u) completion.t) :
    MatrixEntriesInDyadicCyclotomic
      (completionMatrix candidate.u completion.t) :=
  completionMatrix_entries_in_dyadic candidate.inDyadicCyclotomic hSolve.1

/-- A solved Ross completion has a completion-shaped residue matrix at the
paper omega-denominator level. -/
theorem completionMatrix_candidate_exists_residueAtOmegaSDE {θ ε : ℝ}
    (candidate : RSCandidate θ ε) {completion : RSCompletionData}
    (hSolve : SolvesNormEquation (completionXi candidate.u) completion.t) :
    ∃ ru rt : Residue,
      MatrixHasResidueAtLevel
        (completionMatrix candidate.u completion.t)
        (omegaSDE candidate.u)
        (Figure2Branch.completionResidue ru rt) := by
  have huOmega : InOmegaDyadicCyclotomic candidate.u :=
    inOmegaDyadicCyclotomic_of_inDyadicCyclotomic
      candidate.inDyadicCyclotomic
  have hu : HasOmegaDenominatorExponent candidate.u
      (omegaSDE candidate.u) :=
    hasOmegaDenominatorExponent_omegaSDE huOmega
  have hNorm : NormEquation candidate.u completion.t :=
    normEquation_of_solves_completionXi hSolve
  have ht : HasOmegaDenominatorExponent completion.t
      (omegaSDE candidate.u) :=
    hasOmegaDenominatorExponent_of_normEquation hu hSolve.1 hNorm
  rcases completionMatrix_exists_residueAtLevel (u := candidate.u)
      (t := completion.t) hu ht with ⟨ru, rt, hres⟩
  refine ⟨ru, rt, ?_⟩
  simpa [Figure2Branch.completionResidue] using hres

/-- A Giles-Selinger bound proved at the paper denominator level can be used
at the current candidate grid level.  This is the explicit bridge between the
omega-denominator theorem and the legacy coordinate-box candidate record. -/
theorem rossLevelTCount_omegaSDE_candidate_le_level {θ ε : ℝ}
    (candidate : RSCandidate θ ε) :
    rossLevelTCount (omegaSDE candidate.u) ≤
      rossLevelTCount candidate.level :=
  rossLevelTCount_mono (omegaSDE_candidate_le_level candidate)

/-- Multiplying a Diophantine completion by `ω` preserves the same norm-equation
right-hand side. This is the algebra behind Selinger's `T U T†` returned
branch. -/
theorem solvesNormEquation_omega_mul {ξ t : ℂ}
    (hSolve : SolvesNormEquation ξ t) :
    SolvesNormEquation ξ (rsOmegaAlg * t) := by
  refine ⟨InDyadicCyclotomic.mul rsOmegaAlg_in_dyadic hSolve.1, ?_⟩
  calc
    star (rsOmegaAlg * t) * (rsOmegaAlg * t)
        = (star rsOmegaAlg * rsOmegaAlg) * (star t * t) := by
            simp [star_mul]
            ring
    _ = ξ := by rw [rsOmegaAlg_star_mul_self, one_mul, hSolve.2]

/-- Ross-Selinger Lemma 7.5 (`lem-2k-2`) packaged exactly for the search
layer: a solved completion returns either `U` or `T U T†`, with the sharp
returned-branch bound `rossLevelTCount k`.

This is the theorem that should eventually be proved from:
1. `completion_same_least_omega_denominator_exponent`;
2. `completionMatrix_candidate_leastOmegaDenominatorExponent`;
3. the completion-shaped residue facts;
4. `figure2_completion_branch_with_selected_path`; and
5. `giles_selinger_u2_figure2_synthesis_bound`, followed by
   `rossLevelTCount_omegaSDE_candidate_le_level`.
-/
noncomputable def selinger_lemma_7_5 {θ ε : ℝ}
    (candidate : RSCandidate θ ε) {completion : RSCompletionData}
    (hSolve : SolvesNormEquation (completionXi candidate.u) completion.t) :
    SelingerLemma75Classification candidate completion := by
  sorry

/-- Contract for the non-oracle completion stage.

`candidatesAtLevel` is the finite/fuelled seam for future executable scaled
grid enumeration.  Search scans its level batches in the order
`0, 1, ..., fuel`; batch order inside a level is owned by the enumerator. -/
structure RSCompletionSolver where
  candidatesAtLevel :
    (input : RSInput) → (level : ℕ) →
      List (RSCandidate input.θ input.ε)
  candidates_level :
    ∀ (input : RSInput) (level : ℕ) {candidate : RSCandidate input.θ input.ε},
      candidate ∈ candidatesAtLevel input level → candidate.level = level
  solve :
    {θ ε : ℝ} → RSCandidate θ ε → Option RSCompletionData
  sound :
    ∀ {θ ε : ℝ} (candidate : RSCandidate θ ε) {completion : RSCompletionData},
      solve candidate = some completion →
        SolvesNormEquation (completionXi candidate.u) completion.t

namespace RSCompletionSolver

/-- Build a completion solver whose candidate generation stage is the concrete
bounded coordinate-box grid enumerator from `Grid.lean`.

The remaining arguments are exactly the non-grid parts of Algorithm 7.6: the
Diophantine completion attempt and the returned Ross/KMM branch synthesis
certificate.  Increasing `gridBound input k` expands the finite box scanned at
level `k`. -/
noncomputable def ofBoundedGrid
    (gridBound : RSInput → ℕ → ℕ)
    (solve :
      {θ ε : ℝ} → RSCandidate θ ε → Option RSCompletionData)
    (sound :
      ∀ {θ ε : ℝ} (candidate : RSCandidate θ ε) {completion : RSCompletionData},
        solve candidate = some completion →
          SolvesNormEquation (completionXi candidate.u) completion.t) :
    RSCompletionSolver :=
  { candidatesAtLevel := fun input level =>
      boundedGridCandidatesAtLevel input.θ input.ε level
        (gridBound input level)
    candidates_level := by
      intro input level candidate hmem
      exact boundedGridCandidatesAtLevel_level input.θ input.ε level
        (gridBound input level) hmem
    solve := solve
    sound := sound }

/-- Build a completion solver from the canonical full fixed-level grid
enumerator.  This is the default Ross-Selinger candidate source: at level `k`
it scans the complete coordinate box `[-2^k, 2^k]^4`. -/
noncomputable def ofGrid
    (solve :
      {θ ε : ℝ} → RSCandidate θ ε → Option RSCompletionData)
    (sound :
      ∀ {θ ε : ℝ} (candidate : RSCandidate θ ε) {completion : RSCompletionData},
        solve candidate = some completion →
          SolvesNormEquation (completionXi candidate.u) completion.t) :
    RSCompletionSolver :=
  { candidatesAtLevel := fun input level =>
      gridCandidatesAtLevel input.θ input.ε level
    candidates_level := by
      intro input level candidate hmem
      exact gridCandidatesAtLevel_level input.θ input.ε level hmem
    solve := solve
    sound := sound }

end RSCompletionSolver

/-- KMM-backed returned-branch synthesis from an explicit denominator/T-count
comparison.

The sharp Ross-Selinger branch theorem should eventually provide the final
bound `DenNormSDE u + 71 ≤ rossLevelTCount k` (or replace this coarse KMM bound
by the paper's exact `0 / 2k - 2` construction).  This lemma already removes
the synthesis black box: once the bound is available, the circuit and its
evaluation proof come from KMM exact synthesis. -/
theorem kmm_branch_synthesis_tcount_of_denNorm_bound
    {θ ε : ℝ} (candidate : RSCandidate θ ε) {completion : RSCompletionData}
    (hSolve : SolvesNormEquation (completionXi candidate.u) completion.t)
    (hBound : DenNormSDE candidate.u + 71 ≤ rossLevelTCount candidate.level) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C =
          completionMatrix candidate.u completion.t ∧
        TCount C ≤ rossLevelTCount candidate.level := by
  have hNorm : NormEquation candidate.u completion.t :=
    normEquation_of_solves_completionXi hSolve
  rcases exact_synthesis_completion_tcount candidate.inDyadicCyclotomic
      hSolve.1 hNorm with ⟨C, hC, hT⟩
  exact ⟨C, hC, hT.trans hBound⟩

/-! ### Completion matrices at the candidate denominator level -/

/-- A successful Diophantine completion gives a completion matrix whose entries
all have omega-denominator presentations at the candidate's enumerated level.

This is the first matrix-level bridge needed by Selinger 7.5: it turns the
grid/candidate denominator certificate for `u` plus the norm equation for `t`
into a denominator statement about the actual unitary completion matrix. -/
theorem completionMatrix_candidate_hasOmegaDenominatorExponent {θ ε : ℝ}
    (candidate : RSCandidate θ ε) {completion : RSCompletionData}
    (hSolve : SolvesNormEquation (completionXi candidate.u) completion.t) :
    MatrixHasOmegaDenominatorExponent
      (completionMatrix candidate.u completion.t) candidate.level := by
  exact completionMatrix_hasOmegaDenominatorExponent_legacy
    candidate.hasDenominatorExponent hSolve.1
    (normEquation_of_solves_completionXi hSolve)

/-- A successful Diophantine completion has a completion-shaped residue matrix
at the candidate's enumerated level. -/
theorem completionMatrix_candidate_exists_residueAtLevel {θ ε : ℝ}
    (candidate : RSCandidate θ ε) {completion : RSCompletionData}
    (hSolve : SolvesNormEquation (completionXi candidate.u) completion.t) :
    ∃ ru rt : Residue,
      MatrixHasResidueAtLevel
        (completionMatrix candidate.u completion.t) candidate.level
        (Figure2Branch.completionResidue ru rt) := by
  have hu : HasOmegaDenominatorExponent candidate.u candidate.level :=
    hasOmegaDenominatorExponent_of_hasDenominatorExponent
      candidate.hasDenominatorExponent
  have hNorm : NormEquation candidate.u completion.t :=
    normEquation_of_solves_completionXi hSolve
  have ht : HasOmegaDenominatorExponent completion.t candidate.level :=
    hasOmegaDenominatorExponent_of_normEquation hu hSolve.1 hNorm
  rcases completionMatrix_exists_residueAtLevel (u := candidate.u)
      (t := completion.t) hu ht with ⟨ru, rt, hres⟩
  refine ⟨ru, rt, ?_⟩
  simpa [Figure2Branch.completionResidue] using hres

/-- A candidate together with the completion certificate obtained from a
sound solver result. -/
structure CompletedCandidate (θ ε : ℝ) where
  candidate : RSCandidate θ ε
  completion : RSCompletionData
  hSolve : SolvesNormEquation (completionXi candidate.u) completion.t
  synthesize : CliffordTCircuit
  eval_synthesize :
    CliffordTCircuit.eval synthesize =
      completionMatrix candidate.u completion.t
  tcount_synthesize :
    TCount synthesize ≤ rossLevelTCount candidate.level

namespace CompletedCandidate

theorem normEquation {θ ε : ℝ} (completed : CompletedCandidate θ ε) :
    NormEquation completed.candidate.u completed.completion.t :=
  normEquation_of_solves_completionXi completed.hSolve

theorem synthesize_approximates (input : RSInput)
    (completed : CompletedCandidate input.θ input.ε) :
    IsRzApproxCircuit input.θ input.ε completed.synthesize := by
  unfold IsRzApproxCircuit
  rw [completed.eval_synthesize]
  exact opDist_rz_completion_le_of_region input.θ input.hε
    completed.candidate.inEpsilonRegion completed.normEquation

end CompletedCandidate

noncomputable def completedCandidate_of_selinger_direct_branch {θ ε : ℝ}
    (candidate : RSCandidate θ ε) (completion : RSCompletionData)
    (hSolve : SolvesNormEquation (completionXi candidate.u) completion.t)
    {C : CliffordTCircuit}
    (hC : CliffordTCircuit.eval C =
      completionMatrix candidate.u completion.t)
    (hT : TCount C ≤ rossLevelTCount candidate.level) :
    CompletedCandidate θ ε :=
  { candidate := candidate
    completion := completion
    hSolve := hSolve
    synthesize := C
    eval_synthesize := hC
    tcount_synthesize := hT }

noncomputable def completedCandidate_of_selinger_phaseT_branch {θ ε : ℝ}
    (candidate : RSCandidate θ ε) (completion : RSCompletionData)
    (hSolve : SolvesNormEquation (completionXi candidate.u) completion.t)
    {C : CliffordTCircuit}
    (hC : CliffordTCircuit.eval C =
      phaseT * completionMatrix candidate.u completion.t * phaseT†)
    (hT : TCount C ≤ rossLevelTCount candidate.level) :
    CompletedCandidate θ ε :=
  { candidate := candidate
    completion := { t := rsOmegaAlg * completion.t }
    hSolve := solvesNormEquation_omega_mul hSolve
    synthesize := C
    eval_synthesize := by
      rw [hC, phaseT_completionMatrix_phaseT_conjTranspose]
    tcount_synthesize := hT }

/-- Selinger Lemma 7.5 packaged for the Ross search layer, modulo the Ma/KMM
finite residue classification. -/
noncomputable def completedCandidate_of_selinger_lemma_7_5 {θ ε : ℝ}
    (candidate : RSCandidate θ ε) (completion : RSCompletionData)
    (hSolve : SolvesNormEquation (completionXi candidate.u) completion.t)
    (h75 : SelingerLemma75Classification candidate completion) :
    CompletedCandidate θ ε := by
  rcases h75.branch with hC | hC
  · exact completedCandidate_of_selinger_direct_branch
      candidate completion hSolve hC h75.tcount
  · exact completedCandidate_of_selinger_phaseT_branch
      candidate completion hSolve hC h75.tcount

/-- Attempt to complete one scaled-grid candidate with a sound solver. -/
noncomputable def completeCandidate (solver : RSCompletionSolver)
    {θ ε : ℝ} (candidate : RSCandidate θ ε) :
    Option (CompletedCandidate θ ε) :=
  match hsolve : solver.solve candidate with
  | none => none
  | some completion =>
      some
        (completedCandidate_of_selinger_lemma_7_5 candidate completion
          (solver.sound candidate hsolve)
          (selinger_lemma_7_5 candidate (solver.sound candidate hsolve)))

theorem candidate_eq_of_completeCandidate_eq_some
    (solver : RSCompletionSolver) {θ ε : ℝ}
    {candidate : RSCandidate θ ε}
    {completed : CompletedCandidate θ ε}
    (hrun : completeCandidate solver candidate = some completed) :
    completed.candidate = candidate := by
  unfold completeCandidate at hrun
  split at hrun
  · simp at hrun
  · rename_i completion hsolve
    cases hbranch :
        (selinger_lemma_7_5 candidate
          (solver.sound candidate hsolve)).branch
    · simp [completedCandidate_of_selinger_lemma_7_5,
        completedCandidate_of_selinger_direct_branch,
        completedCandidate_of_selinger_phaseT_branch, hbranch] at hrun
      subst completed
      rfl
    · simp [completedCandidate_of_selinger_lemma_7_5,
        completedCandidate_of_selinger_direct_branch,
        completedCandidate_of_selinger_phaseT_branch, hbranch] at hrun
      subst completed
      rfl

/-- Search a single finite candidate batch for the first completable candidate. -/
noncomputable def searchCompletedCandidates (solver : RSCompletionSolver)
    {θ ε : ℝ} : List (RSCandidate θ ε) → Option (CompletedCandidate θ ε)
  | [] => none
  | candidate :: rest =>
      match completeCandidate solver candidate with
      | none => searchCompletedCandidates solver rest
      | some completed => some completed

theorem candidate_mem_of_searchCompletedCandidates_eq_some
    (solver : RSCompletionSolver) {θ ε : ℝ}
    {candidates : List (RSCandidate θ ε)}
    {completed : CompletedCandidate θ ε}
    (hrun : searchCompletedCandidates solver candidates = some completed) :
    completed.candidate ∈ candidates := by
  induction candidates with
  | nil =>
      simp [searchCompletedCandidates] at hrun
  | cons candidate rest ih =>
      cases hcomplete : completeCandidate solver candidate with
      | none =>
          simp [searchCompletedCandidates, hcomplete] at hrun
          exact List.mem_cons_of_mem _ (ih hrun)
      | some head =>
          simp [searchCompletedCandidates, hcomplete] at hrun
          subst completed
          exact List.mem_cons.2
            (Or.inl (candidate_eq_of_completeCandidate_eq_some solver hcomplete))

theorem solve_eq_none_of_completeCandidate_eq_none
    (solver : RSCompletionSolver) {θ ε : ℝ}
    (candidate : RSCandidate θ ε)
    (hnone : completeCandidate solver candidate = none) :
    solver.solve candidate = none := by
  unfold completeCandidate at hnone
  split at hnone
  · assumption
  · simp at hnone

theorem solve_eq_none_of_searchCompletedCandidates_eq_none
    (solver : RSCompletionSolver) {θ ε : ℝ}
    {candidates : List (RSCandidate θ ε)}
    (hnone : searchCompletedCandidates solver candidates = none)
    {candidate : RSCandidate θ ε}
    (hmem : candidate ∈ candidates) :
    solver.solve candidate = none := by
  induction candidates with
  | nil => simp at hmem
  | cons head rest ih =>
      cases hcomplete : completeCandidate solver head with
      | some completed =>
          simp [searchCompletedCandidates, hcomplete] at hnone
      | none =>
          simp [searchCompletedCandidates, hcomplete] at hnone
          rcases List.mem_cons.1 hmem with rfl | hmem
          · exact solve_eq_none_of_completeCandidate_eq_none solver _ hcomplete
          · exact ih hnone hmem

/-- Search one finite batch, then synthesize the first returned completion. -/
noncomputable def searchCandidates (solver : RSCompletionSolver)
    {θ ε : ℝ} (candidates : List (RSCandidate θ ε)) :
    Option CliffordTCircuit :=
  Option.map CompletedCandidate.synthesize
    (searchCompletedCandidates solver candidates)

/-- Candidate batches inspected by a finite-fuel search. -/
def candidatesThrough (solver : RSCompletionSolver) (fuel : ℕ)
    (input : RSInput) : List (RSCandidate input.θ input.ε) :=
  (List.range (fuel + 1)).flatMap (solver.candidatesAtLevel input)

/-- A candidate reached by fuel `fuel` belongs to one of the scanned
denominator levels `0, ..., fuel`. -/
theorem candidate_level_le_of_mem_candidatesThrough
    (solver : RSCompletionSolver) (fuel : ℕ) (input : RSInput)
    {candidate : RSCandidate input.θ input.ε}
    (hmem : candidate ∈ candidatesThrough solver fuel input) :
    candidate.level ≤ fuel := by
  rcases List.mem_flatMap.1 hmem with ⟨level, hlevel, hcand⟩
  have hlevel' : level < fuel + 1 := List.mem_range.mp hlevel
  rw [solver.candidates_level input level hcand]
  omega

/-- The plain Ross-Selinger search up to denominator level `fuel`. -/
noncomputable def searchCompletedThrough (solver : RSCompletionSolver)
    (input : RSInput) : ℕ → Option (CompletedCandidate input.θ input.ε)
  | 0 => searchCompletedCandidates solver (solver.candidatesAtLevel input 0)
  | fuel + 1 =>
      match searchCompletedThrough solver input fuel with
      | some completed => some completed
      | none =>
          searchCompletedCandidates solver
            (solver.candidatesAtLevel input (fuel + 1))

/-- The completed candidate found by a finite-fuel Ross-Selinger search. -/
noncomputable def rossSelingerCompletedSearch
    (solver : RSCompletionSolver) (fuel : ℕ) (input : RSInput) :
    Option (CompletedCandidate input.θ input.ε) :=
  searchCompletedThrough solver input fuel

/-- The plain Ross-Selinger search up to denominator level `fuel`. -/
noncomputable def rossSelingerSearch
    (solver : RSCompletionSolver) (fuel : ℕ) (input : RSInput) :
    Option CliffordTCircuit :=
  Option.map CompletedCandidate.synthesize
    (rossSelingerCompletedSearch solver fuel input)

theorem searchCandidates_sound_if_returns (solver : RSCompletionSolver)
    (input : RSInput) {candidates : List (RSCandidate input.θ input.ε)}
    {C : CliffordTCircuit}
    (hrun : searchCandidates solver candidates = some C) :
    IsRzApproxCircuit input.θ input.ε C := by
  unfold searchCandidates at hrun
  cases hsearch : searchCompletedCandidates solver candidates with
  | none =>
      simp [hsearch] at hrun
  | some completed =>
      have hC : completed.synthesize = C := by
        simpa [hsearch] using hrun
      simpa [hC] using
        (CompletedCandidate.synthesize_approximates input completed)

theorem exists_completed_of_rossSelingerSearch_eq_some
    (solver : RSCompletionSolver) (fuel : ℕ) (input : RSInput)
    {C : CliffordTCircuit}
    (hrun : rossSelingerSearch solver fuel input = some C) :
    ∃ completed : CompletedCandidate input.θ input.ε,
      rossSelingerCompletedSearch solver fuel input = some completed ∧
        completed.synthesize = C := by
  unfold rossSelingerSearch at hrun
  cases hsearch : rossSelingerCompletedSearch solver fuel input with
  | none =>
      simp [hsearch] at hrun
  | some completed =>
      refine ⟨completed, ?_, ?_⟩
      · rfl
      simpa [hsearch] using hrun

theorem rossSelingerSearch_sound_if_returns'
    (solver : RSCompletionSolver) (fuel : ℕ) (input : RSInput)
    {C : CliffordTCircuit}
    (hrun : rossSelingerSearch solver fuel input = some C) :
    IsRzApproxCircuit input.θ input.ε C := by
  rcases exists_completed_of_rossSelingerSearch_eq_some solver fuel input hrun with
    ⟨completed, _hcompleted, rfl⟩
  exact CompletedCandidate.synthesize_approximates input completed

theorem completed_level_eq_of_searchCompletedCandidates_batch
    (solver : RSCompletionSolver) (input : RSInput) (level : ℕ)
    {completed : CompletedCandidate input.θ input.ε}
    (hrun :
      searchCompletedCandidates solver (solver.candidatesAtLevel input level) =
        some completed) :
    completed.candidate.level = level :=
  solver.candidates_level input level
    (candidate_mem_of_searchCompletedCandidates_eq_some solver hrun)

theorem completed_level_le_of_rossSelingerCompletedSearch_eq_some
    (solver : RSCompletionSolver) (fuel : ℕ) (input : RSInput)
    {completed : CompletedCandidate input.θ input.ε}
    (hrun : rossSelingerCompletedSearch solver fuel input = some completed) :
    completed.candidate.level ≤ fuel := by
  induction fuel generalizing completed with
  | zero =>
      have hlevel :=
        completed_level_eq_of_searchCompletedCandidates_batch solver input 0 hrun
      omega
  | succ fuel ih =>
      cases hprev : rossSelingerCompletedSearch solver fuel input with
      | some previous =>
          have hprev' :
              searchCompletedThrough solver input fuel = some previous := by
            simpa [rossSelingerCompletedSearch] using hprev
          have hrun' : some previous = some completed := by
            simpa [rossSelingerCompletedSearch, searchCompletedThrough, hprev'] using hrun
          injection hrun' with hcompleted
          subst completed
          exact (ih hprev).trans (Nat.le_succ fuel)
      | none =>
          have hprev' :
              searchCompletedThrough solver input fuel = none := by
            simpa [rossSelingerCompletedSearch] using hprev
          have hbatch :
              searchCompletedCandidates solver
                  (solver.candidatesAtLevel input (fuel + 1)) =
                some completed := by
            simpa [rossSelingerCompletedSearch, searchCompletedThrough, hprev'] using hrun
          have hlevel :=
            completed_level_eq_of_searchCompletedCandidates_batch solver input
              (fuel + 1) hbatch
          omega

theorem solve_eq_none_of_rossSelingerCompletedSearch_eq_none
    (solver : RSCompletionSolver) (fuel : ℕ) (input : RSInput)
    (hnone : rossSelingerCompletedSearch solver fuel input = none)
    {level : ℕ} {candidate : RSCandidate input.θ input.ε}
    (hlevel : level ≤ fuel)
    (hmem : candidate ∈ solver.candidatesAtLevel input level) :
    solver.solve candidate = none := by
  induction fuel generalizing level candidate with
  | zero =>
      have hlevel0 : level = 0 := by omega
      subst level
      exact solve_eq_none_of_searchCompletedCandidates_eq_none solver
        (by simpa [rossSelingerCompletedSearch, searchCompletedThrough] using hnone)
        hmem
  | succ fuel ih =>
      cases hprev : rossSelingerCompletedSearch solver fuel input with
      | some previous =>
          have hprev' :
              searchCompletedThrough solver input fuel = some previous := by
            simpa [rossSelingerCompletedSearch] using hprev
          have hcontr : False := by
            simp [rossSelingerCompletedSearch, searchCompletedThrough, hprev'] at hnone
          exact False.elim hcontr
      | none =>
          have hprev' :
              searchCompletedThrough solver input fuel = none := by
            simpa [rossSelingerCompletedSearch] using hprev
          by_cases hbefore : level ≤ fuel
          · exact ih hprev hbefore hmem
          · have hlevelEq : level = fuel + 1 := by omega
            subst level
            have hbatch :
                searchCompletedCandidates solver
                    (solver.candidatesAtLevel input (fuel + 1)) =
                  none := by
              simpa [rossSelingerCompletedSearch, searchCompletedThrough, hprev'] using hnone
            exact solve_eq_none_of_searchCompletedCandidates_eq_none solver hbatch hmem

/-- When search returns at level `k`, every candidate from an earlier scanned
denominator level failed the completion solver. -/
theorem solve_eq_none_of_level_lt_returned_level
    (solver : RSCompletionSolver) (fuel : ℕ) (input : RSInput)
    {completed : CompletedCandidate input.θ input.ε}
    (hrun : rossSelingerCompletedSearch solver fuel input = some completed)
    {level : ℕ} {candidate : RSCandidate input.θ input.ε}
    (hlevel : level < completed.candidate.level)
    (hmem : candidate ∈ solver.candidatesAtLevel input level) :
    solver.solve candidate = none := by
  induction fuel generalizing completed level candidate with
  | zero =>
      have hreturned :=
        completed_level_le_of_rossSelingerCompletedSearch_eq_some solver 0 input hrun
      omega
  | succ fuel ih =>
      cases hprev : rossSelingerCompletedSearch solver fuel input with
      | some previous =>
          have hprev' :
              searchCompletedThrough solver input fuel = some previous := by
            simpa [rossSelingerCompletedSearch] using hprev
          have hrun' : some previous = some completed := by
            simpa [rossSelingerCompletedSearch, searchCompletedThrough, hprev'] using hrun
          injection hrun' with hcompleted
          subst completed
          exact ih hprev hlevel hmem
      | none =>
          have hprev' :
              searchCompletedThrough solver input fuel = none := by
            simpa [rossSelingerCompletedSearch] using hprev
          have hbatch :
              searchCompletedCandidates solver
                  (solver.candidatesAtLevel input (fuel + 1)) =
                some completed := by
            simpa [rossSelingerCompletedSearch, searchCompletedThrough, hprev'] using hrun
          have hreturned :=
            completed_level_eq_of_searchCompletedCandidates_batch solver input
              (fuel + 1) hbatch
          have hlevelLe : level ≤ fuel := by omega
          exact solve_eq_none_of_rossSelingerCompletedSearch_eq_none solver fuel
            input hprev hlevelLe hmem

/-- Contract for the factoring-oracle search.

`complete` is the Diophantine oracle promise: every candidate that admits a
completion is accepted by the oracle completion solver. -/
structure RSOracleSolver where
  completionSolver : RSCompletionSolver
  complete :
    ∀ {θ ε : ℝ} (candidate : RSCandidate θ ε),
      (∃ t : ℂ, SolvesNormEquation (completionXi candidate.u) t) →
        ∃ completion : RSCompletionData,
          completionSolver.solve candidate = some completion

/-- Fuelled Ross-Selinger search with the factoring-oracle completion contract. -/
noncomputable def rossSelingerOracleSearch
    (oracle : RSOracleSolver) (fuel : ℕ) (input : RSInput) :
    Option CliffordTCircuit :=
  rossSelingerSearch oracle.completionSolver fuel input

end RossSelinger
end TwoControl

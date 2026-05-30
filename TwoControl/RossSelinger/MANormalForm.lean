import TwoControl.RossSelinger.Selinger75

namespace TwoControl.RossSelinger

open TwoControl.Clifford
open TwoControl.RossSelinger.Selinger75
open TwoControl.KMM
open MatrixCompletion
open DyadicCyclotomic

/-!
Matsumoto-Amano recursion semantics for the Ross-Selinger/Selinger 7.5
close-out.

This file deliberately does **not** claim that a finite Figure 2 path word
evaluates to an arbitrary matrix.  A Figure 2 edge word is a reduction prefix:
if `U' = N† U`, then a circuit for `U'` is turned into a circuit for `U` by
prefixing the syllable `N`.
-/

/-- The elementary MA syllables used as reduction prefixes.  With the local
left-to-right circuit convention, `[h, t]` evaluates to `H * T`, etc. -/
inductive MASyllable where
  | t
  | ht
  | sht
deriving DecidableEq, Repr

namespace MASyllable

/-- Circuit word for an MA reduction prefix. -/
def toCircuit : MASyllable → CliffordTCircuit
  | .t => [.t]
  | .ht => [.h, .t]
  | .sht => [.s, .h, .t]

/-- Matrix semantics of an MA syllable. -/
noncomputable def eval (N : MASyllable) : Square 2 :=
  CliffordTCircuit.eval N.toCircuit

/-- The inverse/reduction action associated to a left prefix.  For unitary
syllables this is the genuine inverse matrix. -/
noncomputable def invEval (N : MASyllable) : Square 2 :=
  (eval N)†

@[simp] theorem eval_toCircuit (N : MASyllable) :
    CliffordTCircuit.eval N.toCircuit = eval N := rfl

/-- Local orientation theorem: prefixing a circuit word is left multiplication
by the syllable matrix. -/
theorem eval_prefix_cons (N : MASyllable) (C : CliffordTCircuit) :
    CliffordTCircuit.eval (N.toCircuit ++ C) =
      eval N * CliffordTCircuit.eval C := by
  rw [CliffordTCircuit.eval_append]
  rfl

@[simp] theorem TCount_toCircuit (N : MASyllable) :
    TCount N.toCircuit = 1 := by
  cases N <;> simp [toCircuit]

theorem tcount_prefix (N : MASyllable) (C : CliffordTCircuit) :
    TCount (N.toCircuit ++ C) = 1 + TCount C := by
  rw [TCount_append, TCount_toCircuit]

theorem eval_mem_unitaryGroup (N : MASyllable) :
    eval N ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  cases N
  · simpa [eval, toCircuit, RossSelingerPrimitive.eval] using
      TwoControl.Clifford.Universal.phaseT_mem_unitaryGroup
  · simpa [eval, toCircuit, RossSelingerPrimitive.eval] using
      (Submonoid.mul_mem _
        TwoControl.Clifford.Universal.hadamard2_mem_unitaryGroup
        TwoControl.Clifford.Universal.phaseT_mem_unitaryGroup)
  · simpa [eval, toCircuit, RossSelingerPrimitive.eval, mul_assoc] using
      (Submonoid.mul_mem _
        TwoControl.Clifford.Universal.phaseS_mem_unitaryGroup
        (Submonoid.mul_mem _
          TwoControl.Clifford.Universal.hadamard2_mem_unitaryGroup
          TwoControl.Clifford.Universal.phaseT_mem_unitaryGroup))

theorem eval_mul_invEval (N : MASyllable) :
    eval N * invEval N = 1 := by
  have hN := eval_mem_unitaryGroup N
  simpa [invEval, Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff.mp hN)

theorem invEval_mul_eval (N : MASyllable) :
    invEval N * eval N = 1 := by
  have hN := eval_mem_unitaryGroup N
  simpa [invEval, Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff'.mp hN)

/-- Matrix orientation for reduction prefixes.  If the reduced matrix is
`U' = N† U`, then prefixing the recursive circuit by `N` reconstructs `U`. -/
theorem reduction_equation_orientation
    (N : MASyllable) (U U' : Square 2)
    (hred : U' = invEval N * U) :
    eval N * U' = U := by
  rw [hred, ← Matrix.mul_assoc, eval_mul_invEval, Matrix.one_mul]

/-- Circuit-level reconstruction from a reduced matrix. -/
theorem eval_prefix_of_reduction
    (N : MASyllable) (C : CliffordTCircuit) (U U' : Square 2)
    (hred : U' = invEval N * U)
    (hC : CliffordTCircuit.eval C = U') :
    CliffordTCircuit.eval (N.toCircuit ++ C) = U := by
  rw [eval_prefix_cons, hC]
  exact reduction_equation_orientation N U U' hred

end MASyllable

/-! ### Closed KMM/MA recursive reduction

The first version of this file exposed two contract structures,
`MABaseSynthesizer` and `MAReducer`.  Those contracts were intentionally too
abstract, and the naive matrix-level version is not a true theorem: arbitrary
matrices of omega-denominator level zero are not necessarily Clifford circuits,
and arbitrary positive-level matrices do not admit a universal `T/HT/SHT`
descent step.

The proved KMM recursion is state/unitary-shaped.  It tracks the denominator of
the first state coordinate via `DenNormSDE`; for low denominator it dispatches
to the finite base table, and otherwise it finds a concrete `H T^k` transform
that strictly lowers `DenNormSDE`.  The theorems below package that closed
math directly, with no solver/reducer contracts.
-/

/-- A concrete KMM/MA state-reduction step: apply one of the four transforms
`H T^k` and strictly lower the tracked norm-denominator exponent.  This is a
`Prop`, not a data structure, so it can be used as the right branch of recursive
case splits without introducing a new computational contract. -/
def KMMStateReductionStep (z w : ℂ) : Prop :=
  ∃ k : Fin 4, ∃ z' w' : ℂ,
    z' = (applyHTPowToState k z w).1 ∧
      w' = (applyHTPowToState k z w).2 ∧
        StateEntriesInDyadicCyclotomic z' w' ∧
          IsUnitState z' w' ∧
            DenNormSDE z' < DenNormSDE z

/-- The actual denominator-lowering reducer from KMM.

For a normalized state over `D[ω]`, once the tracked denominator norm is at
least `5`, one of the four `H T^k` moves preserves the state invariants and
strictly lowers `DenNormSDE`. -/
theorem kmm_state_reduce_step
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w)
    (hLarge : 5 ≤ DenNormSDE z) :
    KMMStateReductionStep z w := by
  rcases kmm_exists_reducing_k hEntries hState hLarge with ⟨k, hred⟩
  refine ⟨k, (applyHTPowToState k z w).1, (applyHTPowToState k z w).2,
    rfl, rfl, ?_, ?_, ?_⟩
  · simpa using hred.1
  · simpa using hred.2.1
  · simpa using hred.2.2

/-- The closed low-denominator/base side of the KMM recursion.

KMM's internal finite table covers the low range used by the recursive proof.
This theorem exposes the public consequence needed by the normal-form layer:
in the base range, the state is synthesizable with the coarse KMM T-count
bound. -/
theorem kmm_state_base_case
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w)
    (hLow : DenNormSDE z ≤ 4) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w ∧
        TCount C ≤ 68 := by
  rcases kmm_state_preparation_tcount hEntries hState with ⟨C, hC, hT⟩
  refine ⟨C, hC, ?_⟩
  omega

/-- The KMM recursion split: a normalized dyadic state is either in the
low-denominator base range and can be synthesized immediately, or it has a
concrete denominator-lowering `H T^k` reduction step. -/
theorem kmm_state_base_or_reduce
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w) :
    (DenNormSDE z ≤ 4 ∧
      ∃ C : CliffordTCircuit,
        CliffordTCircuit.eval C * ket0Column = stateColumn z w ∧
          TCount C ≤ 68)
      ∨ KMMStateReductionStep z w := by
  by_cases hLow : DenNormSDE z ≤ 4
  · left
    exact ⟨hLow, kmm_state_base_case hEntries hState hLow⟩
  · right
    exact kmm_state_reduce_step hEntries hState (by omega)

/-- Fully closed recursive KMM state synthesis, with the public coarse
T-count bound threaded through the recursion. -/
theorem kmm_state_recursive_synthesis
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w ∧
        TCount C ≤ DenNormSDE z + 64 :=
  kmm_state_preparation_tcount hEntries hState

/-- Fully closed recursive KMM unitary synthesis for `2 × 2` dyadic unitaries.

This is the contract-free replacement for the old matrix-level normal-form
synthesis hook. -/
theorem kmm_unitary_recursive_synthesis
    {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hEntries : MatrixEntriesInDyadicCyclotomic U) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C = U ∧
        TCount C ≤ DenNormSDE (U 0 0) + 71 :=
  kmm_exact_synthesis_tcount hU hEntries

/-! ### Ross completion matrices as KMM states -/

/-- The first column of a Ross-Selinger completion matrix is exactly the KMM
state `(u,t)`.  This is the concrete matrix/state bridge needed before the
Selinger 7.5 recursion can use the closed KMM state machinery. -/
theorem completionMatrix_mul_ket0Column (u t : ℂ) :
    completionMatrix u t * ket0Column = stateColumn u t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [completionMatrix, ket0Column, stateColumn, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- The norm equation for a Ross completion is exactly the unit-state
condition on the first column. -/
theorem isUnitState_of_normEquation {u t : ℂ}
    (hNorm : NormEquation u t) :
    IsUnitState u t := by
  simpa [IsUnitState, NormEquation, add_comm] using hNorm

/-- Conversely, a KMM unit-state proof is the Ross completion norm equation. -/
theorem normEquation_of_isUnitState {u t : ℂ}
    (hState : IsUnitState u t) :
    NormEquation u t := by
  simpa [IsUnitState, NormEquation, add_comm] using hState

/-- A Ross completion matrix is the unique completion unitary whose first
column is the state `(u,t)`.  This pins the recursive state-synthesis bridge to
the exact matrix used by Ross-Selinger. -/
theorem completionMatrix_first_column
    (u t : ℂ) :
    (completionMatrix u t) 0 0 = u ∧
      (completionMatrix u t) 1 0 = t := by
  simp [completionMatrix]

/-! ### MA normal-form / Figure 2 bridge

The finite Figure 2 residue work selects the correct vertex and proves the
printed arithmetic at that vertex.  What remains, mathematically, is the
Giles-Selinger/Matsumoto-Amano normal-form bridge: a dyadic unitary whose
least omega-denominator residue lies at a Figure 2 vertex has an actual
Clifford+T normal-form circuit with the vertex's T-count bound.

The witness below is deliberately semantic.  It is the point where the
recursive MA normal-form theorem connects to the Ross-Selinger completion
pipeline: after this witness is supplied, the algorithm layer only needs to
extract the circuit and bound.
-/

/-- Semantic payload of the Giles-Selinger U(2) Figure 2 normal-form theorem. -/
structure MANormalFormFigure2Witness
    (U : Square 2) (k : ℕ) (R : ResidueMatrix) (node : Figure2Node) where
  circuit : CliffordTCircuit
  eval_circuit : CliffordTCircuit.eval circuit = U
  tcount_bound : TCount circuit ≤ 2 * k - node.tOffset

namespace MANormalFormFigure2Witness

/-- Extract the actual synthesis statement from an MA/Figure 2 witness. -/
theorem synthesizes
    {U : Square 2} {k : ℕ} {R : ResidueMatrix} {node : Figure2Node}
    (w : MANormalFormFigure2Witness U k R node) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C = U ∧
        TCount C ≤ 2 * k - node.tOffset :=
  ⟨w.circuit, w.eval_circuit, w.tcount_bound⟩

end MANormalFormFigure2Witness

/-- Giles-Selinger/Matsumoto-Amano normal-form existence at a Figure 2 vertex.

This is the remaining paper theorem behind the bridge.  It packages the exact
content of the U(2) Figure 2 theorem: from a dyadic unitary, its least
omega-denominator exponent, and its residue vertex, the MA normal form supplies
a circuit whose T-count is bounded by the printed vertex expression.
-/
noncomputable def dyadic_unitary_has_ma_figure2_witness
    {U : Square 2} {k : ℕ} {R : ResidueMatrix} {node : Figure2Node}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hEntries : MatrixEntriesInDyadicCyclotomic U)
    (hLeast : MatrixLeastOmegaDenominatorExponent U k)
    (hResidue : MatrixHasResidueAtLevel U k R)
    (hNode : node ∈ Figure2.nodes)
    (hR : node.residue = R)
    (hValid : node.ValidAtLevel k) :
    MANormalFormFigure2Witness U k R node := by
  sorry

/-- The MA normal-form bridge in the synthesis-bound form consumed by
Ross-Selinger. -/
theorem ma_normal_form_figure2_synthesis_bound
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
        TCount C ≤ 2 * k - node.tOffset :=
  (dyadic_unitary_has_ma_figure2_witness hU hEntries hLeast hResidue
    hNode hR hValid).synthesizes

end TwoControl.RossSelinger

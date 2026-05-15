# Strict Branch Prompts For Clifford+T Universality

Use these prompts to assign agents to the independent Clifford+T universality
branches.  These replace the earlier permissive branch prompt.

Global rule for every branch:

```text
No `sorry`, no `admit`, and no new `axiom`.
```

The only accepted axiom in the entire universality track is the local statement
of Lemma 12:

```lean
TwoControl.Clifford.Universal.lemma12_rz_approximation_by_ht
```

Every other current axiom must be removed by the responsible branch.  In
particular, the following are not acceptable final dependencies:

```lean
TwoControl.Clifford.Universal.trace_inequality
TwoControl.Clifford.Universal.general_cosine_sine_step_exists
TwoControl.Clifford.Universal.general_demultiplexing_step_exists
TwoControl.Clifford.Universal.controlled_rz_reduction_step_exists
TwoControl.Clifford.Universal.lemma1_decomposition_to_easy_gate_set_exists
TwoControl.Clifford.Universal.embedded_rz_approximation_by_clifford_t
TwoControl.Clifford.Universal.clifford_trz_gate_mem_unitaryGroup
TwoControl.Clifford.Universal.clifford_t_gate_mem_unitaryGroup
```

Relevant imports agents should consider, depending on branch:

```lean
import TwoControl.CosineSine.Statements
import TwoControl.StateHelpers
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
```

Other likely relevant local files:

```text
TwoControl/Prelude.lean
TwoControl/Definitions.lean
TwoControl/GateHelpers.lean
TwoControl/KronHelpers.lean
TwoControl/BlockHelpers.lean
TwoControl/DiagonalizationHelpers.lean
TwoControl/CosineSine/Statements.lean
TwoControl/Clifford/Definitions.lean
TwoControl/Clifford/Statements.lean
TwoControl/Clifford/Universal/GateSets.lean
reference/cliff/doc.tex
docs/migration/clifford/universal_parallel_work_packet.md
```

Every branch prompt below tells the agent to read `reference/cliff/doc.tex`.
That is intentional: the original paper proof is allowed as mathematical
context.

## Branch 1 Prompt: Distance And Wang-Zhang Trace Inequality

```text
You are assigned to Branch 1: Hilbert-Schmidt distance and error accumulation.

Repository:

  /home/abdullah/projects/two-ctrl-root/two-control-lean

Read first:

  docs/migration/clifford/universal_parallel_work_packet.md
  docs/migration/clifford/universal_strict_branch_prompts.md
  reference/cliff/doc.tex
  TwoControl/Clifford/Universal/Distance.lean
  TwoControl/Clifford/Universal/GateSets.lean
  TwoControl/Clifford/Statements.lean

Useful imports to consider:

  import Mathlib.Analysis.SpecialFunctions.Complex.Arg
  import Mathlib.Analysis.SpecialFunctions.Complex.Circle
  import TwoControl.StateHelpers

Your owned file is:

  TwoControl/Clifford/Universal/Distance.lean

Your job is to remove every non-foundational assumption from this file.  In
particular, `trace_inequality` must not remain an axiom.  Prove it or replace
it with proved lemmas whose combination gives the current statement.

Endpoints that must be fully proved:

  hsDistance_self
  hsDistance_eq_zero_of_globalPhaseEquivalent
  trace_inequality
  hsDistance_mul_le
  hsDistance_circuitMatrix_le_sum

Guidance:

  - Start by running:

      #print axioms TwoControl.Clifford.Universal.hsDistance_circuitMatrix_le_sum

    and confirm that the only offending dependency is the trace inequality.

  - The paper cites Wang-Zhang for the trace inequality.  You may prove that
    theorem directly, or prove a stronger standard result that implies it.

  - Search mathlib for relevant facts about unitary matrices, trace, complex
    inner products, Cauchy-Schwarz, Frobenius/Hilbert-Schmidt norms, angles,
    and circle-valued complex numbers.  Do not assume the theorem.

  - Keep the public theorem name `trace_inequality`.

  - If the current statement is too hard in its exact syntax, introduce proved
    private helper lemmas and then prove the existing public statement from
    them.  Do not weaken the public endpoint unless you also update every
    downstream proof and preserve the intended theorem.

  - You may add imports in `Distance.lean` if they are needed.

  - Do not edit recursive decomposition, Rz approximation, or final theorem
    files except for import adjustments that are strictly required.

Completion criteria:

  - `rg -n "\\b(sorry|admit|axiom)\\b" TwoControl/Clifford/Universal/Distance.lean`
    shows no branch-owned `sorry`, `admit`, or `axiom`.

  - `#print axioms TwoControl.Clifford.Universal.hsDistance_circuitMatrix_le_sum`
    does not list `TwoControl.Clifford.Universal.trace_inequality` or any
    branch-created axiom.

  - `lake build TwoControl.Clifford.Main` succeeds.

Do not stop with a plan.  Keep proving until the branch is complete.  If a
proof path fails, try another path.  Only report a blocker if it is a precise
Lean/mathlib gap with the exact theorem shape that remains.
```

## Branch 2 Prompt: Embedded Gate Placement And Unitarity Infrastructure

```text
You are assigned to Branch 2: embedded gate placement and circuit
infrastructure.

Repository:

  /home/abdullah/projects/two-ctrl-root/two-control-lean

Read first:

  docs/migration/clifford/universal_parallel_work_packet.md
  docs/migration/clifford/universal_strict_branch_prompts.md
  reference/cliff/doc.tex
  TwoControl/Clifford/Universal/GateSets.lean
  TwoControl/Clifford/Definitions.lean
  TwoControl/Clifford/Statements.lean
  TwoControl/KronHelpers.lean
  TwoControl/GateHelpers.lean

Useful imports to consider:

  import TwoControl.StateHelpers
  import Mathlib.Analysis.SpecialFunctions.Complex.Arg
  import Mathlib.Analysis.SpecialFunctions.Complex.Circle

Your owned primary file is:

  TwoControl/Clifford/Universal/GateSets.lean

Allowed helper file if needed:

  TwoControl/Clifford/Universal/Embeddings.lean

Your job is to make the embedding infrastructure strong enough that no later
branch needs private unitary axioms for allowed gates.  In particular,
MainTheorem.lean must not need:

  private axiom clifford_trz_gate_mem_unitaryGroup
  private axiom clifford_t_gate_mem_unitaryGroup

Endpoints/APIs to provide as proved theorems:

  - primitive one-qubit gates are unitary:
      hadamard2, phaseT, rz θ, phaseS, phaseSdagger

  - primitive two-qubit gates are unitary:
      cnot

  - local/tensor embeddings preserve unitarity:
      OneQubitPlacement.embed
      TwoQubitPlacement.embed

  - allowed gates are unitary:
      CliffordTGate n U -> U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ
      CliffordTRzGate n U -> U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ
      EasyGate n U -> U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ, if useful

Guidance:

  - Reuse existing local helpers first.  Search for unitary lemmas in:

      TwoControl/GateHelpers.lean
      TwoControl/KronHelpers.lean
      TwoControl/Clifford/Statements.lean

  - If a primitive unitary proof is missing, prove it directly by matrix
    extensionality or by diagonal/unitary helper lemmas.

  - For embeddings, prove that `reindexSquare`, `castSquare`, and tensoring
    with identity preserve membership in `Matrix.unitaryGroup`.

  - The current placement structures have `target`, `first`, and `second`
    fields.  You may strengthen or add helper lemmas around them, but preserve
    public predicates:

      IsEmbeddedOneQubitGate
      IsEmbeddedTwoQubitGate

  - Do not use axioms.  Do not push this work into MainTheorem as private
    assumptions.

  - Do not prove Lemma 1, Wang-Zhang, or Lemma 12 here.

Completion criteria:

  - `rg -n "\\b(sorry|admit|axiom)\\b" TwoControl/Clifford/Universal/GateSets.lean`
    shows no branch-owned `sorry`, `admit`, or `axiom`.

  - MainTheorem no longer needs private axioms for allowed-gate unitarity once
    Branch 6 uses your proved lemmas.

  - `lake build TwoControl.Clifford.Main` succeeds.

Do not stop with a plan.  Keep proving and strengthening the embedding API
until downstream agents can use proved unitary lemmas instead of axioms.
```

## Branch 3 Prompt: Recursive Lemma 1, No Lemma 1 Axiom

```text
You are assigned to Branch 3: recursive easy-gate decomposition, the paper's
Lemma 1.

Repository:

  /home/abdullah/projects/two-ctrl-root/two-control-lean

Read first:

  docs/migration/clifford/universal_parallel_work_packet.md
  docs/migration/clifford/universal_strict_branch_prompts.md
  reference/cliff/doc.tex
  TwoControl/Clifford/Universal/RecursiveDecomposition.lean
  TwoControl/Clifford/Universal/GateSets.lean
  TwoControl/Clifford/Statements.lean
  TwoControl/CosineSine/Statements.lean

Useful imports to consider:

  import TwoControl.CosineSine.Statements
  import TwoControl.StateHelpers
  import Mathlib.Analysis.SpecialFunctions.Complex.Arg
  import Mathlib.Analysis.SpecialFunctions.Complex.Circle

Your owned primary file is:

  TwoControl/Clifford/Universal/RecursiveDecomposition.lean

Allowed helper files if needed:

  TwoControl/Clifford/Universal/CosineSineStep.lean
  TwoControl/Clifford/Universal/DemultiplexingStep.lean
  TwoControl/Clifford/Universal/ControlledRzReduction.lean
  TwoControl/Clifford/Universal/EasyDecomposition.lean

Your job is to remove all recursive-decomposition axioms.  These are not
acceptable:

  general_cosine_sine_step_exists
  general_demultiplexing_step_exists
  controlled_rz_reduction_step_exists
  lemma1_decomposition_to_easy_gate_set_exists

Endpoints that must be fully proved:

  general_cosine_sine_step
  general_demultiplexing_step
  controlled_rz_reduction_step
  lemma1_decomposition_to_easy_gate_set

Guidance:

  - Use `reference/cliff/doc.tex` for the intended proof.

  - Use existing `TwoControl.CosineSine.Statements` wherever possible.  There
    is already a two-qubit CS theorem used by Lemma 11; determine whether it
    can be generalized, reused recursively, or needs a new stated/proved
    general theorem in this branch.

  - Do not simply wrap the paper lemmas as axioms.  If an external theorem is
    mathematically needed, prove the exact Lean interface from existing local
    results or add a proved theorem with sufficient hypotheses.

  - Lemma 1 should end at:

      Synthesizes (EasyGate n) U

    It should not use Lemma 11.  Lemma 11 belongs to the next exact bridge.

  - Use `lemma3_ry_via_rz` to convert `R_y` pieces to `R_z` pieces where the
    paper does.

  - You may change abstract marker predicates if doing so helps prove the
    recursive theorem, but preserve public theorem names or add compatibility
    wrappers under the current names.

  - Do not prove Wang-Zhang, Lemma 12, or final epsilon accounting here.

Completion criteria:

  - `rg -n "\\b(sorry|admit|axiom)\\b" TwoControl/Clifford/Universal/RecursiveDecomposition.lean`
    shows no branch-owned `sorry`, `admit`, or `axiom`.

  - `#print axioms TwoControl.Clifford.Universal.lemma1_decomposition_to_easy_gate_set`
    does not list any `TwoControl.Clifford.Universal.*_exists` axiom.

  - `lake build TwoControl.Clifford.Main` succeeds.

Do not stop with a plan.  This is the large branch; keep decomposing it into
proved helper lemmas until the public Lemma 1 endpoint is genuinely proved.
```

## Branch 4 Prompt: Exact EasyGate To Clifford+Rz Bridge

```text
You are assigned to Branch 4: exact EasyGate to Clifford+Rz bridge.

Repository:

  /home/abdullah/projects/two-ctrl-root/two-control-lean

Read first:

  docs/migration/clifford/universal_parallel_work_packet.md
  docs/migration/clifford/universal_strict_branch_prompts.md
  reference/cliff/doc.tex
  TwoControl/Clifford/Universal/CliffordRz.lean
  TwoControl/Clifford/Universal/GateSets.lean
  TwoControl/Clifford/Definitions.lean
  TwoControl/Clifford/Statements.lean

Useful imports to consider:

  import TwoControl.StateHelpers
  import Mathlib.Analysis.SpecialFunctions.Complex.Arg
  import Mathlib.Analysis.SpecialFunctions.Complex.Circle

Your owned file is:

  TwoControl/Clifford/Universal/CliffordRz.lean

Your job is to keep this bridge fully proved and axiom-free.  It should use
Lemma 11 as a proved theorem, not as an axiom, and it may depend on the public
Lemma 1 endpoint as an imported theorem.  It must not introduce any new axiom.

Endpoints that must be fully proved:

  two_qubit_gate_has_clifford_rz_circuit
  embedded_phaseS_is_clifford_t
  embedded_phaseSdagger_is_clifford_t
  easy_gate_factor_to_clifford_rz
  easy_circuit_to_clifford_rz
  clifford_rz_synthesis_from_lemma1

Guidance:

  - The current file may already have many of these proofs.  Audit them with
    `#print axioms`.

  - Ensure every theorem in this file depends only on proved infrastructure,
    except for `clifford_rz_synthesis_from_lemma1`, whose only non-foundational
    dependency should be the public Lemma 1 theorem if Branch 3 is not merged
    yet.

  - Use existing global-phase helpers:

      GlobalPhaseEquivalent.of_eq
      GlobalPhaseEquivalent.refl
      GlobalPhaseEquivalent.trans
      GlobalPhaseEquivalent.mul

  - Use existing Lemma 11:

      TwoControl.Clifford.lemma11_two_qubit_synthesis

  - Do not use private axioms for embedding, phase gates, or circuit
    concatenation.  Prove the needed local lemmas.

  - Do not prove Wang-Zhang, Lemma 12, or recursive Lemma 1 here.

Completion criteria:

  - `rg -n "\\b(sorry|admit|axiom)\\b" TwoControl/Clifford/Universal/CliffordRz.lean`
    shows no branch-owned `sorry`, `admit`, or `axiom`.

  - `#print axioms TwoControl.Clifford.Universal.easy_circuit_to_clifford_rz`
    lists only ordinary Lean/mathlib foundations such as `propext`,
    `Classical.choice`, and `Quot.sound`.

  - `lake build TwoControl.Clifford.Main` succeeds.

Do not stop with a plan.  If a proof currently closes only because another
file has an axiom, isolate whether that is your branch's dependency or another
branch's endpoint, and do not add new assumptions.
```

## Branch 5 Prompt: Lemma 12 Interface And Embedded Rz Approximation

```text
You are assigned to Branch 5: Lemma 12 interface and embedded Rz
approximation.

Repository:

  /home/abdullah/projects/two-ctrl-root/two-control-lean

Read first:

  docs/migration/clifford/universal_parallel_work_packet.md
  docs/migration/clifford/universal_strict_branch_prompts.md
  reference/cliff/doc.tex
  TwoControl/Clifford/Universal/RzApproximation.lean
  TwoControl/Clifford/Universal/GateSets.lean
  TwoControl/Clifford/Universal/Distance.lean

Useful imports to consider:

  import TwoControl.StateHelpers
  import Mathlib.Analysis.SpecialFunctions.Complex.Arg
  import Mathlib.Analysis.SpecialFunctions.Complex.Circle

Your owned file is:

  TwoControl/Clifford/Universal/RzApproximation.lean

Strict axiom policy for this branch:

  - The local Lemma 12 statement may remain an axiom:

      lemma12_rz_approximation_by_ht

  - No other axiom is allowed.

Therefore `embedded_rz_approximation_by_clifford_t` must be proved from:

  lemma12_rz_approximation_by_ht

and the concrete embedding/circuit APIs from `GateSets.lean`.

Endpoints:

  - preserve `lemma12_rz_approximation_by_ht` as the single accepted external
    axiom unless explicitly instructed to prove Lemma 12 itself;
  - prove `embedded_rz_approximation_by_clifford_t`.

Guidance:

  - Destructure `hR : IsEmbeddedOneQubitGate n (rz θ) R`.

  - For a direct one-qubit placement, apply local Lemma 12 to get a
    `List OneQubitHTPrimitive`, lift it with `embedOneQubitHTCircuit`, and use
    `circuitMatrix_embedOneQubitHTCircuit`.

  - For a two-qubit local-on-first or local-on-second placement, lift the
    one-qubit `{H,T}` circuit through `TwoQubitCliffordTPrimitive.onFirst` or
    `.onSecond`, then embed the two-qubit circuit.

  - You will likely need distance-preservation lemmas for embeddings:

      hsDistance (p.embed A) (p.embed B) = hsDistance A B

    or enough specialized inequalities to transfer the Lemma 12 bound through
    the embedding.  Prove these lemmas; do not assume them.

  - Coordinate only through public APIs from Branch 2.  Do not add axioms for
    embedding-distance preservation.

  - Do not prove final epsilon accounting here.

Completion criteria:

  - `rg -n "\\b(sorry|admit|axiom)\\b" TwoControl/Clifford/Universal/RzApproximation.lean`
    shows exactly one branch-owned axiom: `lemma12_rz_approximation_by_ht`.

  - `#print axioms TwoControl.Clifford.Universal.embedded_rz_approximation_by_clifford_t`
    lists `lemma12_rz_approximation_by_ht` as the only non-foundational
    Clifford universality axiom.

  - `lake build TwoControl.Clifford.Main` succeeds.

Do not stop with a plan.  Keep proving the embedded theorem from the local
Lemma 12 axiom until the embedded axiom is gone.
```

## Branch 6 Prompt: Final Clifford+Rz To Clifford+T Connector

```text
You are assigned to Branch 6: final Clifford+Rz to Clifford+T connector.

Repository:

  /home/abdullah/projects/two-ctrl-root/two-control-lean

Read first:

  docs/migration/clifford/universal_parallel_work_packet.md
  docs/migration/clifford/universal_strict_branch_prompts.md
  reference/cliff/doc.tex
  TwoControl/Clifford/Universal/MainTheorem.lean
  TwoControl/Clifford/Universal/Distance.lean
  TwoControl/Clifford/Universal/RzApproximation.lean
  TwoControl/Clifford/Universal/CliffordRz.lean
  TwoControl/Clifford/Universal/GateSets.lean

Useful imports to consider:

  import TwoControl.StateHelpers
  import Mathlib.Analysis.SpecialFunctions.Complex.Arg
  import Mathlib.Analysis.SpecialFunctions.Complex.Circle

Your owned file is:

  TwoControl/Clifford/Universal/MainTheorem.lean

Your job is to remove all private axioms and make the final connector proof
depend only on proved branch endpoints plus the single accepted local Lemma 12
axiom.

Private axioms that must be removed:

  clifford_trz_gate_mem_unitaryGroup
  clifford_t_gate_mem_unitaryGroup

Endpoints that must be fully proved:

  clifford_rz_synthesis_approximates_by_clifford_t
  clifford_t_is_universal

Guidance:

  - Replace the private unitary axioms with proved lemmas from Branch 2, such
    as:

      CliffordTGate n U -> U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ
      CliffordTRzGate n U -> U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ

  - The proof may depend on:

      hsDistance_eq_zero_of_globalPhaseEquivalent
      hsDistance_circuitMatrix_le_sum
      embedded_rz_approximation_by_clifford_t
      clifford_rz_synthesis_from_lemma1

    but those must be real theorems, not axioms, except insofar as the embedded
    Rz approximation ultimately depends on the accepted local Lemma 12 axiom.

  - Keep the public theorem statement of `clifford_t_is_universal`.

  - Be careful with the zero-Rz case and with distributing an error budget
    across circuit factors.  The existing `length + 1` budget pattern is fine
    if it proves the strict `< ε` bound cleanly.

  - Do not introduce any axiom to assert that circuits are unitary.  Prove it
    from allowed-gate unitarity and `circuitMatrix`.

  - Do not prove Lemma 1, Wang-Zhang, or Lemma 12 here.  Use their public
    endpoints once the responsible branches provide real theorems.

Completion criteria:

  - `rg -n "\\b(sorry|admit|axiom)\\b" TwoControl/Clifford/Universal/MainTheorem.lean`
    shows no branch-owned `sorry`, `admit`, or `axiom`.

  - `#print axioms TwoControl.Clifford.Universal.clifford_t_is_universal`
    lists no private unitary axioms and no universality axioms except, if
    Branch 5 is intentionally left at the accepted boundary,
    `lemma12_rz_approximation_by_ht`.

  - `lake build TwoControl.Clifford.Main` succeeds.

Do not stop with a plan.  Keep replacing private assumptions with proved
lemmas until the final theorem has the required axiom footprint.
```

## Final Audit Prompt

```text
You are assigned to the final audit after all branches merge.

Repository:

  /home/abdullah/projects/two-ctrl-root/two-control-lean

Read:

  docs/migration/clifford/universal_parallel_work_packet.md
  docs/migration/clifford/universal_strict_branch_prompts.md
  reference/cliff/doc.tex
  TwoControl/Clifford/Universal/*.lean

Your job is not to add new mathematics unless a small connector proof is
missing.  Your job is to enforce the axiom policy.

Run:

  rg -n "\\b(sorry|admit|axiom)\\b" TwoControl/Clifford/Universal

The only acceptable result is the local Lemma 12 axiom:

  TwoControl.Clifford.Universal.lemma12_rz_approximation_by_ht

Then run:

  #print axioms TwoControl.Clifford.Universal.clifford_t_is_universal

The only acceptable non-foundational Clifford universality axiom is:

  TwoControl.Clifford.Universal.lemma12_rz_approximation_by_ht

No Wang-Zhang axiom.  No Lemma 1 axiom.  No embedded Rz axiom.  No private
unitary axioms.

Finally run:

  lake build TwoControl.Clifford.Main

If any forbidden axiom remains, identify exactly which branch owns it and keep
working or hand it back to that branch.  Do not declare the project complete
while any forbidden axiom remains.
```

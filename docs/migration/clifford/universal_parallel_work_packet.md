# Clifford+T Universality Parallel Work Packet

This packet is for agents working on the `reference/cliff/doc.tex` Clifford+T
universality proof inside this Lean repository.  It is intentionally
self-contained: an agent should be able to read this file, choose one branch
below, and work on that branch without needing to understand the other branches'
implementation details.

The current target theorem is:

```lean
TwoControl.Clifford.Universal.clifford_t_is_universal
```

It lives in:

```text
TwoControl/Clifford/Universal/MainTheorem.lean
```

The final theorem says that for any `n`-qubit unitary `U`, with `2 <= n`, and
any `epsilon > 0`, there is a circuit over Clifford+T gates whose
Hilbert-Schmidt distance from `U` is less than `epsilon`.

## Current Lean Status

The old Clifford track up to Lemma 11 is already present in:

```text
TwoControl/Clifford/Definitions.lean
TwoControl/Clifford/Statements.lean
```

The new universality scaffold is split under:

```text
TwoControl/Clifford/Universal/GateSets.lean
TwoControl/Clifford/Universal/Distance.lean
TwoControl/Clifford/Universal/RecursiveDecomposition.lean
TwoControl/Clifford/Universal/CliffordRz.lean
TwoControl/Clifford/Universal/RzApproximation.lean
TwoControl/Clifford/Universal/MainTheorem.lean
TwoControl/Clifford/Universal/Main.lean
```

The blueprint-facing map is in:

```text
blueprint/src/chapters/clifford_lemma11.tex
blueprint/src/chapters/clifford_universal.tex
blueprint/lean_decls
```

The new scaffold currently builds, but many declarations are `sorry`-backed.
To inspect the exact current list:

```bash
rg -n "sorry" TwoControl/Clifford/Universal
```

The branch lists below are designed so different people can work in parallel.
Each branch has an owned proof surface and should avoid editing other branches'
owned files except for tiny import-line additions agreed at merge time.

## Existing Helpers To Know

### Concrete Clifford definitions

File:

```text
TwoControl/Clifford/Definitions.lean
```

Important declarations:

```lean
hadamard2 : Square 2
phaseS : Square 2
phaseSdagger : Square 2
phaseT : Square 2
phaseShift : ℝ -> Square 2
rz : ℝ -> Square 2
cnot : Square 4
localOnFirst : Square 2 -> Square 4
localOnSecond : Square 2 -> Square 4
reverseControlledGate : Square 2 -> Square 4
controlledRzPair : ℝ -> ℝ -> Square 4
```

Circuit primitives already available:

```lean
OneQubitPrimitive
OneQubitPrimitive.eval
oneQubitCircuitMatrix
oneQubitCircuitMatrix_append

TwoQubitPrimitive
TwoQubitPrimitive.eval
twoQubitCircuitMatrix
twoQubitCircuitMatrix_append

liftFirst
twoQubitCircuitMatrix_liftFirst
liftSecond
twoQubitCircuitMatrix_liftSecond
```

Use these existing primitives before creating new local circuit datatypes.

### Proven or already-scaffolded Clifford lemmas

File:

```text
TwoControl/Clifford/Statements.lean
```

Important declarations:

```lean
lemma3_ry_via_rz
lemma4_demultiplex_two_qubit
controlled_rz_pair_uses_standard_gates
one_qubit_exact_h_t_rz
lemma11_two_qubit_synthesis
```

Global phase infrastructure:

```lean
GlobalPhaseEquivalent
GlobalPhaseEquivalent.of_eq
GlobalPhaseEquivalent.refl
GlobalPhaseEquivalent.trans
GlobalPhaseEquivalent.mul
GlobalPhaseEquivalent.localOnFirst
GlobalPhaseEquivalent.localOnSecond
```

The key completed result for the universality proof is:

```lean
lemma11_two_qubit_synthesis :
  ∀ U : Square 4,
    U ∈ Matrix.unitaryGroup (Fin 4) ℂ ->
      ∃ gates : List TwoQubitPrimitive,
        GlobalPhaseEquivalent U (twoQubitCircuitMatrix gates)
```

### Universal scaffold vocabulary

File:

```text
TwoControl/Clifford/Universal/GateSets.lean
```

General circuit vocabulary:

```lean
circuitMatrix : List (Square N) -> Square N
circuitMatrix_append
CircuitOver
Synthesizes
SynthesizesUpToGlobalPhase
```

Current embedded-gate predicates:

```lean
IsEmbeddedOneQubitGate (n : ℕ) : Square 2 -> Square (2 ^ n) -> Prop
IsEmbeddedTwoQubitGate (n : ℕ) : Square 4 -> Square (2 ^ n) -> Prop
```

These are currently `opaque`.  That is deliberate scaffolding.  The placement
branch below owns the task of replacing or refining them with concrete
placement semantics while preserving the public theorem statements.

Gate-set predicates:

```lean
EasyGate n
CliffordTRzGate n
CliffordTGate n
```

Concrete `{H,T}` and Clifford+T primitive helpers:

```lean
OneQubitHTPrimitive
OneQubitHTPrimitive.eval
OneQubitHTPrimitive.toOneQubitPrimitive
oneQubitHTCircuitMatrix
oneQubitHTCircuitMatrix_append
oneQubitHTCircuitMatrix_eq_oneQubitCircuitMatrix_map

TwoQubitCliffordTPrimitive
TwoQubitCliffordTPrimitive.eval
TwoQubitCliffordTPrimitive.toTwoQubitPrimitive
twoQubitCliffordTCircuitMatrix
twoQubitCliffordTCircuitMatrix_append
twoQubitCliffordTCircuitMatrix_eq_twoQubitCircuitMatrix_map
```

## Branch Rules

Use these rules for every branch.

1. Keep public theorem names stable unless the branch explicitly says
   otherwise.  If a statement must change, add a wrapper under the old name.
2. Do not prove or refactor another branch's endpoint.  Treat other branches'
   declarations as public interfaces.
3. Keep edits to the owned files listed in the branch.  If a helper naturally
   belongs elsewhere, add a short note in the branch file or this packet, but
   do not take over another branch's file.
4. Each branch should finish with:

   ```bash
   lake build TwoControl.Clifford.Main
   ```

5. A branch is complete only when its owned endpoint declarations no longer
   contain `sorry`.  Existing unrelated warnings in older files are not part
   of the branch.
6. Do not update generated files under `blueprint/print` or `blueprint/web`
   unless explicitly asked.  Source blueprint files are fine when a branch
   endpoint status changes.

## Branch 1: Hilbert-Schmidt Distance And Error Accumulation

Owned file:

```text
TwoControl/Clifford/Universal/Distance.lean
```

This branch is independent of the recursive decomposition, Lemma 11, and
Lemma 12.  It is pure matrix analysis plus list/circuit algebra.

Endpoints to complete:

```lean
hsDistance_self
hsDistance_eq_zero_of_globalPhaseEquivalent
trace_inequality
hsDistance_mul_le
hsDistance_circuitMatrix_le_sum
```

Checklist:

1. Read `hsDistance` and confirm the exact normalization by `N ^ 2`.
2. Prove `hsDistance_self` from `U† * U = 1` and
   `Matrix.trace 1 = N`.
3. Prove `hsDistance_eq_zero_of_globalPhaseEquivalent` using the definition of
   `GlobalPhaseEquivalent`; the scalar phase should disappear under norm.
4. Prove or isolate the Wang-Zhang trace inequality as
   `trace_inequality`.  If mathlib has a usable theorem, import it locally.
   If the proof is long, add private helper lemmas in this same file only.
5. Prove `hsDistance_mul_le` using trace cyclicity and
   `trace_inequality`.
6. Prove `hsDistance_circuitMatrix_le_sum` by induction on the zipped circuit
   lists, using `hsDistance_mul_le`.
7. Do not edit `RecursiveDecomposition.lean`, `CliffordRz.lean`,
   `RzApproximation.lean`, or `MainTheorem.lean`.

Branch completion condition:

```bash
rg -n "sorry" TwoControl/Clifford/Universal/Distance.lean
lake build TwoControl.Clifford.Main
```

The first command should produce no branch-owned `sorry`.

## Branch 2: Embedded Gate Placement And Circuit Infrastructure

Owned primary file:

```text
TwoControl/Clifford/Universal/GateSets.lean
```

Allowed new helper file, if the file grows:

```text
TwoControl/Clifford/Universal/Embeddings.lean
```

This branch is the shared placement foundation.  It must not prove distance,
recursive decomposition, Lemma 12, or final universality.  Its job is to make
the embedded-gate predicates usable by all later connector proofs.

Current issue:

```lean
opaque IsEmbeddedOneQubitGate
opaque IsEmbeddedTwoQubitGate
```

These predicates are currently black boxes.  That is enough for statement
scaffolding but not enough to prove embedded replacement theorems.

Checklist:

1. Choose a concrete representation of an embedded one-qubit gate in an
   `n`-qubit matrix.  The representation should track at least:
   - the target wire,
   - the tensor placement,
   - any permutation needed to move the target wire into place.
2. Choose a concrete representation of an embedded two-qubit gate.  It should
   track:
   - two distinct target wires,
   - the tensor placement,
   - any permutation needed to move the two target wires into place.
3. Preserve the public predicate names:

   ```lean
   IsEmbeddedOneQubitGate
   IsEmbeddedTwoQubitGate
   ```

   If changing them from `opaque` to `def` breaks downstream proofs, add
   compatibility lemmas rather than changing downstream theorem statements.
4. Add constructor/helper lemmas showing that embedded primitive gates are
   accepted by the gate-set predicates:

   ```lean
   CliffordTGate n U
   CliffordTRzGate n U
   EasyGate n U
   ```

5. Add list/circuit lift helpers for embedded one-qubit circuits.  These are
   needed later for embedded `{H,T}` approximations.
6. Add list/circuit lift helpers for embedded two-qubit circuits.  These are
   needed later to lift `lemma11_two_qubit_synthesis` into arbitrary
   `n`-qubit circuits.
7. Add multiplication/concatenation lemmas for embedded circuits, but keep them
   generic.  Do not prove a branch-specific theorem such as
   `easy_circuit_to_clifford_rz` here.
8. Keep the public statements of `EasyGate`, `CliffordTRzGate`, and
   `CliffordTGate` stable.

Branch completion condition:

```bash
lake build TwoControl.Clifford.Main
```

This branch may not remove all `sorry`s in the universal directory.  It is
complete when embedding predicates are concrete or backed by proved placement
APIs strong enough for the connector branches, and no new `sorry`s are added
in its owned files.

## Branch 3: Recursive Easy-Gate Decomposition, The Paper's Lemma 1

Owned primary file:

```text
TwoControl/Clifford/Universal/RecursiveDecomposition.lean
```

Allowed new helper files, if useful:

```text
TwoControl/Clifford/Universal/CosineSineStep.lean
TwoControl/Clifford/Universal/DemultiplexingStep.lean
TwoControl/Clifford/Universal/ControlledRzReduction.lean
TwoControl/Clifford/Universal/EasyDecomposition.lean
```

This branch proves the large recursive exact decomposition from the paper:
arbitrary `n`-qubit unitaries decompose into arbitrary two-qubit gates and
one-qubit gates `H`, `S`, `Sdagger`, and `R_z(theta)`.

Endpoints to complete:

```lean
general_cosine_sine_step
general_demultiplexing_step
controlled_rz_reduction_step
lemma1_decomposition_to_easy_gate_set
```

Relevant existing theorem:

```lean
TwoControl.Clifford.lemma3_ry_via_rz
```

Use it to convert multiplexed `R_y` gates into multiplexed `R_z` gates.

Checklist:

1. Formalize the general `n`-qubit cosine-sine step corresponding to the
   Paige-Wei lemma in `doc.tex`.
2. Formalize the general demultiplexing step for controlled choices of two
   `(n-1)`-qubit gates.
3. Formalize the Mottönen-style controlled-`R_z` reduction step.
4. Prove the recursive decomposition theorem:

   ```lean
   lemma1_decomposition_to_easy_gate_set
   ```

5. Keep the output in terms of:

   ```lean
   Synthesizes (EasyGate n) U
   ```

6. Do not use `lemma11_two_qubit_synthesis`; this branch stops before
   arbitrary two-qubit gates are replaced by Clifford+`R_z`.
7. Do not prove approximation or distance lemmas in this branch.

Branch completion condition:

```bash
rg -n "sorry" TwoControl/Clifford/Universal/RecursiveDecomposition.lean
lake build TwoControl.Clifford.Main
```

The first command should produce no branch-owned `sorry`.

## Branch 4: Exact EasyGate To Clifford+Rz Bridge

Owned file:

```text
TwoControl/Clifford/Universal/CliffordRz.lean
```

This branch is where Lemma 11 combines with Lemma 1, but it should not prove
Lemma 1 itself.  It should prove a conditional bridge:

```lean
Synthesizes (EasyGate n) U
  -> SynthesizesUpToGlobalPhase (CliffordTRzGate n) U
```

Endpoints to complete:

```lean
embedded_phaseS_is_clifford_t
embedded_phaseSdagger_is_clifford_t
easy_gate_factor_to_clifford_rz
easy_circuit_to_clifford_rz
```

Already complete and available:

```lean
two_qubit_gate_has_clifford_rz_circuit
clifford_rz_synthesis_from_lemma1
```

The first is a direct wrapper around:

```lean
TwoControl.Clifford.lemma11_two_qubit_synthesis
```

Checklist:

1. Prove embedded `S` synthesis using the exact identity `S = T*T`.
2. Prove embedded `Sdagger` synthesis using the exact identity
   `Sdagger = T^6`.
3. Prove the one-factor replacement theorem:

   ```lean
   easy_gate_factor_to_clifford_rz
   ```

   Cases:
   - arbitrary embedded two-qubit gate: use `two_qubit_gate_has_clifford_rz_circuit`;
   - embedded `H`: already allowed by `CliffordTRzGate`;
   - embedded `S`: use `embedded_phaseS_is_clifford_t`;
   - embedded `Sdagger`: use `embedded_phaseSdagger_is_clifford_t`;
   - embedded `R_z(theta)`: already allowed by `CliffordTRzGate`.
4. Prove the circuit-level replacement theorem:

   ```lean
   easy_circuit_to_clifford_rz
   ```

   This should be a list induction over the easy circuit, concatenating the
   replacement circuits and composing global phases.
5. Use existing global phase helpers:

   ```lean
   GlobalPhaseEquivalent.refl
   GlobalPhaseEquivalent.trans
   GlobalPhaseEquivalent.mul
   ```

6. Do not edit `RecursiveDecomposition.lean`; assume
   `lemma1_decomposition_to_easy_gate_set` as an imported theorem.
7. Do not edit `Distance.lean` or approximation files.

Branch completion condition:

```bash
rg -n "sorry" TwoControl/Clifford/Universal/CliffordRz.lean
lake build TwoControl.Clifford.Main
```

The first command should produce no branch-owned `sorry`.

## Branch 5: Local Lemma 12, Approximation Of Rz By H And T

Owned file:

```text
TwoControl/Clifford/Universal/RzApproximation.lean
```

If this file becomes too mixed, split the local theorem into:

```text
TwoControl/Clifford/Universal/RzApproximationLocal.lean
```

This branch is mathematically independent of the recursive decomposition and
Lemma 11.  It is the state-of-the-art approximation input mentioned in the
notes.  Short term, we are allowed to treat Lemma 12 as an axiom; long term,
this branch is where the axiom is replaced by proof.

Primary endpoint:

```lean
lemma12_rz_approximation_by_ht
```

Secondary endpoint currently in the same file:

```lean
embedded_rz_approximation_by_clifford_t
```

Recommended ownership split:

1. This branch should focus first on the local one-qubit theorem
   `lemma12_rz_approximation_by_ht`.
2. If another person is working on embedded placement, do not edit their
   embedding helpers.  Treat embedded lifting as an integration concern.
3. Once placement APIs are stable, either this branch or the final connector
   branch can finish `embedded_rz_approximation_by_clifford_t`.

Checklist:

1. Decide whether the branch goal is:
   - a real Lean proof of Lemma 12, or
   - a carefully isolated external axiom/theorem imported from a separate
     approximation development.
2. Keep the public statement:

   ```lean
   ∃ gates : List OneQubitHTPrimitive,
     hsDistance (rz θ) (oneQubitHTCircuitMatrix gates) < ε
   ```

3. Reuse `OneQubitHTPrimitive` and `oneQubitHTCircuitMatrix`; do not introduce
   another `{H,T}` circuit datatype.
4. If proving constructively, document any number-theoretic or Solovay-Kitaev
   style lemmas as private helpers or as a dedicated local file.
5. Do not prove the final theorem in this branch.

Branch completion condition:

```bash
lake build TwoControl.Clifford.Main
```

If the branch is only preserving Lemma 12 as an explicit assumption for now,
leave a clear comment saying that this is the remaining external axiom.  If
the branch aims to remove the assumption, then:

```bash
rg -n "sorry" TwoControl/Clifford/Universal/RzApproximation.lean
```

should show no branch-owned `sorry`.

## Branch 6: Clifford+Rz To Clifford+T Error Replacement

Owned file:

```text
TwoControl/Clifford/Universal/MainTheorem.lean
```

This is a connector branch.  It should not start until the following public
endpoints are considered stable enough to use:

```lean
hsDistance_eq_zero_of_globalPhaseEquivalent
hsDistance_circuitMatrix_le_sum
embedded_rz_approximation_by_clifford_t
```

Endpoint to complete:

```lean
clifford_rz_synthesis_approximates_by_clifford_t
```

Checklist:

1. Destructure:

   ```lean
   hSynth : SynthesizesUpToGlobalPhase (CliffordTRzGate n) U
   ```

   into a Clifford+`R_z` circuit and a global phase relation.
2. Count or filter the `R_z` gates in the circuit.  The proof needs to assign
   each such gate an error budget, usually `epsilon / k`.
3. Replace exact Clifford+T gates by themselves.
4. Replace every `R_z(theta)` gate using:

   ```lean
   embedded_rz_approximation_by_clifford_t
   ```

5. Use:

   ```lean
   hsDistance_eq_zero_of_globalPhaseEquivalent
   hsDistance_circuitMatrix_le_sum
   ```

   to control the accumulated error.
6. Be careful about the case `k = 0`: then the Clifford+`R_z` circuit is
   already a Clifford+T circuit up to global phase.
7. Do not edit Lemma 1, Lemma 11, or Lemma 12 proofs.

Branch completion condition:

```bash
rg -n "sorry" TwoControl/Clifford/Universal/MainTheorem.lean
lake build TwoControl.Clifford.Main
```

The only theorem in this file that currently contains a `sorry` is
`clifford_rz_synthesis_approximates_by_clifford_t`.  Once it is complete, the
wrapper theorem `clifford_t_is_universal` should already close.

## Final Stop Point: Connect The Branches

When the parallel branches are ready, one integrator should do the final pass.
This is not a parallel proof branch.  It is the point where the results are
connected.

Required public endpoints:

Branch 1:

```lean
hsDistance_eq_zero_of_globalPhaseEquivalent
hsDistance_circuitMatrix_le_sum
```

Branch 2:

```text
Concrete and usable IsEmbeddedOneQubitGate / IsEmbeddedTwoQubitGate APIs
```

Branch 3:

```lean
lemma1_decomposition_to_easy_gate_set
```

Branch 4:

```lean
easy_circuit_to_clifford_rz
clifford_rz_synthesis_from_lemma1
```

Branch 5:

```lean
lemma12_rz_approximation_by_ht
embedded_rz_approximation_by_clifford_t
```

Branch 6:

```lean
clifford_rz_synthesis_approximates_by_clifford_t
```

Final connection proof:

```lean
clifford_t_is_universal
```

Expected proof shape:

1. Apply `clifford_rz_synthesis_from_lemma1` to get a Clifford+`R_z`
   synthesis up to global phase.
2. Apply `clifford_rz_synthesis_approximates_by_clifford_t` to replace all
   `R_z` gates with Clifford+T approximations.
3. Return the resulting circuit and error bound.

Final verification commands:

```bash
rg -n "sorry" TwoControl/Clifford/Universal
lake build TwoControl.Clifford.Main
```

If the goal is a fully assumption-free development, the `rg` command should
return no `sorry`s in `TwoControl/Clifford/Universal`.

If the short-term goal is "main theorem modulo Lemma 12", then the only
acceptable remaining `sorry` should be the explicit Lemma 12 approximation
assumption:

```lean
lemma12_rz_approximation_by_ht
```

## Blueprint Updates After Branch Completion

When a branch endpoint is completed, update:

```text
blueprint/src/chapters/clifford_universal.tex
```

Change the relevant node from:

```tex
\notready
```

to:

```tex
\leanok
```

Do this only for endpoints that are genuinely proved or intentionally accepted
as external assumptions.

Then run, if available:

```bash
leanblueprint checkdecls
leanblueprint web
```

If `leanblueprint` is not installed, at minimum run:

```bash
lake build TwoControl.Clifford.Main
```

and check that every `\lean{...}` declaration in the blueprint chapter appears
in `blueprint/lean_decls`.

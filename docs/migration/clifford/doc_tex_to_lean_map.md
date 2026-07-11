# `doc.tex` To Lean Universality Map

This map aligns `reference/cliff/doc.tex` with the current Lean implementation
of the Clifford+T universality theorem.  It is meant to be read as a status
packet: every mathematical item in the paper is connected to the declarations
that implement it, or marked as not formalized / not used.

Line numbers are current for the repository state inspected on 2026-05-27.

## Current End-To-End Route

The paper route is:

```text
Lemma 1: exact easy-gate decomposition
  + Lemma 11: exact two-qubit synthesis using C(X), H, T, Rz
  + S = T*T and S† = T^6
  + Lemma 12: approximate every Rz by H,T
  + distance product bounds
  = Clifford+T universality
```

The Lean route is the same at the top level, with two important refinements:

1. Exact synthesis is usually tracked **up to global phase**, via
   `GlobalPhaseEquivalent`.  This is physically natural and is invisible to
   `hsDistance`, but it is not stated explicitly in the paper.
2. Lemma 12 is no longer an axiom on the imported `Universal.MainTheorem` path.
   It is proved in the independent Boykin branch under
   `TwoControl/Clifford/Lemma12`.

Primary import spine:

| Lean entry | Role |
|---|---|
| [`TwoControl.Clifford.Universal.Main`](../../../TwoControl/Clifford/Universal/Main.lean#L1) | Aggregates the universality files. |
| [`TwoControl.Clifford.Universal.MainTheorem`](../../../TwoControl/Clifford/Universal/MainTheorem.lean#L1) | Final theorem and error accounting. |
| [`TwoControl.Clifford.Universal.CliffordRz`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L1) | Bridges easy-gate circuits to Clifford+`R_z`. |
| [`TwoControl.Clifford.Universal.RzApproximation`](../../../TwoControl/Clifford/Universal/RzApproximation.lean#L1) | Lifts Lemma 12 into embedded `n`-qubit positions. |
| [`TwoControl.Clifford.Lemma12.Main`](../../../TwoControl/Clifford/Lemma12/Main.lean#L1) | Lemma 12 entry point. |
| [`TwoControl.Clifford.Lemma12.MainTheorem`](../../../TwoControl/Clifford/Lemma12/MainTheorem.lean#L1) | Paper Lemma 12 statement. |
| [`TwoControl.Clifford.Lemma12.Boykin.BoykinDensity`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1) | Actual proof of Lemma 12. |

Ross-Selinger is a separate, currently paused approximation/compiler leg; it
lives in the top-level [`RossSelinger/`](../../../RossSelinger.lean) and
[`KMM/`](../../../KMM.lean) libraries (not under `TwoControl/`), is not built
by default, and is not imported by `Universal.MainTheorem` or any proof of
paper Lemma 12.

## Core Infrastructure Not Present In The Paper

These declarations are the Lean vocabulary used to make the paper precise.

| Lean declaration | File | Paper role | Alignment |
|---|---|---|---|
| `circuitMatrix` | [`GateSets.lean`](../../../TwoControl/Clifford/Universal/GateSets.lean#L19) | "Circuit means a product of unitaries." | Exact formalization as list product. |
| `CircuitOver` | [`GateSets.lean`](../../../TwoControl/Clifford/Universal/GateSets.lean#L43) | "Built from a gate set." | Exact formal predicate. |
| `Synthesizes` | [`GateSets.lean`](../../../TwoControl/Clifford/Universal/GateSets.lean#L88) | Exact circuit equality. | Used for exact easy-gate synthesis. |
| `SynthesizesUpToGlobalPhase` | [`GateSets.lean`](../../../TwoControl/Clifford/Universal/GateSets.lean#L92) | Not explicit in paper. | Lean refinement for physical equivalence. |
| `GlobalPhaseEquivalent` | [`Statements.lean`](../../../TwoControl/Clifford/Statements.lean#L846) | Not explicit in paper. | Needed because Lemma 11 and one-qubit synthesis are up to phase. |
| `EasyGate` | [`GateSets.lean`](../../../TwoControl/Clifford/Universal/GateSets.lean#L408) | "2-qubit gates and `{H,S,S†,Rz}`." | Exact gate predicate for Lemma 1. |
| `CliffordTRzGate` | [`GateSets.lean`](../../../TwoControl/Clifford/Universal/GateSets.lean#L417) | `{C(X),H,T,Rz}` intermediate gate set. | Exact bridge gate predicate. |
| `CliffordTGate` | [`GateSets.lean`](../../../TwoControl/Clifford/Universal/GateSets.lean#L424) | `{C(X),H,T}` final gate set. | Exact final gate predicate. |
| `OneQubitPlacement` | [`GateSets.lean`](../../../TwoControl/Clifford/Universal/GateSets.lean#L229) | Paper draws gates on wires informally. | Lean embedding machinery. |
| `TwoQubitPlacement` | [`GateSets.lean`](../../../TwoControl/Clifford/Universal/GateSets.lean#L293) | Paper draws 2-qubit gates on wires informally. | Lean embedding machinery. |
| `IsEmbeddedOneQubitGate` | [`GateSets.lean`](../../../TwoControl/Clifford/Universal/GateSets.lean#L359) | "A one-qubit gate appears in an `n`-qubit circuit." | Lean-only explicit placement predicate. |
| `IsEmbeddedTwoQubitGate` | [`GateSets.lean`](../../../TwoControl/Clifford/Universal/GateSets.lean#L365) | "A two-qubit gate appears in an `n`-qubit circuit." | Lean-only explicit placement predicate. |

Unitary side conditions are explicit in Lean.  The relevant gate unitarity
lemmas are:

| Gate | Lean declaration |
|---|---|
| `H` | [`hadamard2_mem_unitaryGroup`](../../../TwoControl/Clifford/Universal/GateSets.lean#L176) |
| `S` | [`phaseS_mem_unitaryGroup`](../../../TwoControl/Clifford/Universal/GateSets.lean#L186) |
| `S†` | [`phaseSdagger_mem_unitaryGroup`](../../../TwoControl/Clifford/Universal/GateSets.lean#L190) |
| `T` | [`phaseT_mem_unitaryGroup`](../../../TwoControl/Clifford/Universal/GateSets.lean#L194) |
| `R_z` | [`rz_mem_unitaryGroup`](../../../TwoControl/Clifford/Universal/GateSets.lean#L201) |
| `C(X)` | [`cnot_mem_unitaryGroup`](../../../TwoControl/Clifford/Universal/GateSets.lean#L209) |
| `EasyGate` | [`EasyGate.mem_unitaryGroup`](../../../TwoControl/Clifford/Universal/GateSets.lean#L490) |
| `CliffordTRzGate` | [`CliffordTRzGate.mem_unitaryGroup`](../../../TwoControl/Clifford/Universal/GateSets.lean#L502) |
| `CliffordTGate` | [`CliffordTGate.mem_unitaryGroup`](../../../TwoControl/Clifford/Universal/GateSets.lean#L512) |

## Paper Definitions

| Paper item | Lean declaration(s) | Status and notes |
|---|---|---|
| `H`, `S`, `S†`, `T`, `C(X)` | [`hadamard2`](../../../TwoControl/Clifford/Definitions.lean#L13), [`phaseS`](../../../TwoControl/Clifford/Definitions.lean#L17), [`phaseSdagger`](../../../TwoControl/Clifford/Definitions.lean#L21), [`phaseT`](../../../TwoControl/Clifford/Definitions.lean#L25), [`cnot`](../../../TwoControl/Clifford/Definitions.lean#L37) | Direct definitions. |
| `R_z(θ)` | [`rz`](../../../TwoControl/Clifford/Definitions.lean#L33) | Direct definition. |
| `R_y(θ)` | [`CosineSine.ry`](../../../TwoControl/CosineSine/Definitions.lean#L27), [`ry_unitary`](../../../TwoControl/CosineSine/Statements.lean#L390) | Direct definition outside `Clifford/Universal`. |
| `R_x(θ)` | No current direct counterpart on the universality path. | The paper defines it for context, but the proof does not use it. |
| Hilbert-Schmidt distance `d` | [`hsDistance`](../../../TwoControl/Clifford/Universal/Distance.lean#L385) | Direct formalization for `Square N`. |
| Universal gate-set theorem | [`clifford_t_is_universal`](../../../TwoControl/Clifford/Universal/MainTheorem.lean#L356) | Direct theorem, formulated for every `n : ℕ` and dimension `2^n`. |

## Paper Lemma And Theorem Map

### Main Theorem: Clifford+T Is Universal

Paper statement:
for every unitary `U` and `ε > 0`, there is a circuit over `{C(X),H,T}` with
`d(U,C) < ε`.

Lean endpoint:

| Lean declaration | File | Alignment |
|---|---|---|
| `clifford_t_is_universal` | [`MainTheorem.lean`](../../../TwoControl/Clifford/Universal/MainTheorem.lean#L356) | Direct final theorem. Covers `n = 0`, `n = 1`, and `n ≥ 2`. |
| `clifford_t_is_universal_of_two_le` | [`MainTheorem.lean`](../../../TwoControl/Clifford/Universal/MainTheorem.lean#L302) | The paper-like `n ≥ 2` branch. |
| `one_qubit_clifford_t_is_universal` | [`MainTheorem.lean`](../../../TwoControl/Clifford/Universal/MainTheorem.lean#L288) | Lean-only one-qubit base case. |
| `zero_qubit_clifford_t_is_universal` | [`MainTheorem.lean`](../../../TwoControl/Clifford/Universal/MainTheorem.lean#L326) | Lean-only zero-qubit base case. |

Implementation differences:

- The paper treats all dimensions uniformly.  Lean splits `n = 0`, `n = 1`,
  and `n ≥ 2`.
- The `n ≥ 2` branch uses `clifford_rz_synthesis_from_lemma1`, then replaces
  `R_z` factors by Lemma 12 approximations.
- The paper uses `ε/k` for `k` `R_z` gates.  Lean uses
  `δ = ε / (length + 1)` in
  [`clifford_rz_synthesis_approximates_by_clifford_t`](../../../TwoControl/Clifford/Universal/MainTheorem.lean#L175),
  avoiding division by zero and proving `(length * δ) < ε`.

### Lemma 1: Exact Easy-Gate Decomposition

Paper label: `lem:decomposition-to-an-easy-gate-set`.

Paper statement:
every unitary can be exactly decomposed into 2-qubit gates and
`{H,S,S†,R_z(θ)}`.

Lean declarations:

| Lean declaration | File | Alignment |
|---|---|---|
| `lemma1_decomposition_to_easy_gate_set` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L2318) | Direct theorem for `n ≥ 2`: `Synthesizes (EasyGate n) U`. |
| `two_qubit_unitary_is_easy_gate` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L1244) | Base case: any 2-qubit unitary is one easy embedded two-qubit gate. |
| `general_cosine_sine_step` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L995) | Supplies the recursive CS step used by Lemma 1. |
| `controlled_ry_family_via_controlled_rz` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L1013) | Paper's `R_y` to `R_z` conjugation lifted to a controlled family. |
| `general_demultiplexing_step` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L1145) | General demultiplexing step for block-diagonal gates. |
| `synthesizes_controlled_rz_family` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L2208) | Implements uniformly controlled `R_z` families by easy gates. |
| `synthesizes_controlled_ry_family` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L2268) | Implements uniformly controlled `R_y` families using the previous item. |
| `synthesizes_first_qubit_block_diag` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L2294) | Recursive synthesis of the `P` and `Q` block-diagonal factors. |

Implementation differences:

- The paper says "for any unitary" without edge cases.  Lean's recursive
  Lemma 1 is for `2 ≤ n`; final theorem handles `0` and `1` separately.
- The paper writes circuit diagrams.  Lean expands them into explicit matrix
  equalities, embeddings, and `Synthesizes` witnesses.

### Paige-Wei Cosine-Sine Decomposition

Paper label: `cosinesine`.

Lean declarations:

| Lean declaration | File | Alignment |
|---|---|---|
| `CosineSine.cosinesine_exists` | [`CosineSine/Statements.lean`](../../../TwoControl/CosineSine/Statements.lean#L1106) | Fully proved 2-qubit CS decomposition used by Lemma 11. |
| `HasGeneralCosineSineStep` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L213) | Lean predicate matching the general paper shape. |
| `general_cosine_sine_step_exists` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L268) | General CS existence interface used by Lemma 1. |
| `general_cosine_sine_step_two_qubit` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L983) | 2-qubit specialization bridged into the general predicate. |
| `general_cosine_sine_step` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L995) | Dispatches to the 2-qubit proof for `n = 2` and general theorem otherwise. |

Status:
used in both the two-qubit Lemma 11 route and the recursive Lemma 1 route.

### Lemma 3: `R_y` Via `R_z`

Paper label: `ryrz`.

Lean declarations:

| Lean declaration | File | Alignment |
|---|---|---|
| `lemma3_ry_via_rz` | [`Statements.lean`](../../../TwoControl/Clifford/Statements.lean#L553) | Direct 1-qubit matrix identity. |
| `controlled_ry_family_via_controlled_rz` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L1013) | Lifted controlled-family form used by recursive Lemma 1. |
| `conditionalRy_uses_standard_gates` | [`Statements.lean`](../../../TwoControl/Clifford/Statements.lean#L1127) | 2-qubit controlled form used in Lemma 11. |

Status:
used.  The paper proves the 1-qubit identity; Lean also proves the controlled
forms needed by the compiler route.

### Lemma 4: Demultiplexing

Paper label: `demultiplexing`.

Lean declarations:

| Lean declaration | File | Alignment |
|---|---|---|
| `lemma4_demultiplex_two_qubit` | [`Statements.lean`](../../../TwoControl/Clifford/Statements.lean#L636) | 2-qubit specialization used by Lemma 11. |
| `general_demultiplexing_step` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L1145) | General first-qubit block-diagonal demultiplexing used by Lemma 1. |

Status:
used.  Lean exposes unitarity side conditions and constructs `P`, `Q`, and
the angle family explicitly via diagonalization and `Complex.arg`.

### Möttönen Controlled-`R_z` Reduction

Paper label: `rzrz`.

Lean declarations:

| Lean declaration | File | Alignment |
|---|---|---|
| `controlled_rz_reduction_step` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L1900) | Direct controlled-family reduction by one control wire. |
| `synthesizes_controlled_rz_family` | [`RecursiveDecomposition.lean`](../../../TwoControl/Clifford/Universal/RecursiveDecomposition.lean#L2208) | Recursive synthesis using the reduction. |

Status:
used by Lemma 1.  Lean phrases the CNOT as an embedded two-qubit gate
`IsEmbeddedTwoQubitGate`, while the paper uses a circuit diagram.

### Gate Count Lemma For Controlled `R_z`

Paper label: `rzcount`.

Paper statement:
controlled `R_z` families can be implemented with `3 * 2^(n-2) - 2` two-qubit
gates.

Lean status:

| Lean counterpart | Status |
|---|---|
| None in the final theorem path. | Not formalized and not used. |

The Lean development proves existence of circuits, not the exact gate-count
formula.  The final theorem does not depend on this complexity bound.

### Exponential Gate Count For General `n`-Qubit Unitaries

Paper section:
the recurrence for `U(n)` and the final count
`1/2 * 4^n - 9 * 2^(n-2) + 2`.

Lean status:

| Lean counterpart | Status |
|---|---|
| None in the final theorem path. | Not formalized and not used. |

This is a complexity-analysis section of the paper.  It is not needed to prove
universality, and no current Lean theorem tracks the recurrence or closed form.

### Hilbert-Schmidt Distance Definition

Paper definition:
`d(U,V) = sqrt(1 - ||Tr(U† V)||^2 / N^2)`.

Lean declaration:

| Lean declaration | File | Alignment |
|---|---|---|
| `hsDistance` | [`Distance.lean`](../../../TwoControl/Clifford/Universal/Distance.lean#L385) | Direct formalization. |

Implementation differences:

- Lean works for any square dimension `N`, not just powers of two.
- Lemmas generally require `0 < N` and unitary hypotheses.

### Lemma 7: Distance To Itself Is Zero

Paper label: `lem:hs-distance-to-itself-is-zero`.

Lean declaration:

| Lean declaration | File | Alignment |
|---|---|---|
| `hsDistance_self` | [`Distance.lean`](../../../TwoControl/Clifford/Universal/Distance.lean#L389) | Direct proof. |

Status:
used in final replacement accounting for exact gates and empty circuits.

### Lemma 8: Wang-Zhang Trace Inequality

Paper label: `lem:trace-inequality`.

Lean declaration:

| Lean declaration | File | Alignment |
|---|---|---|
| `trace_inequality` | [`Distance.lean`](../../../TwoControl/Clifford/Universal/Distance.lean#L438) | Proved theorem, not an axiom, with unitary hypotheses. |
| `unit_vector_trace_inequality` | [`Distance.lean`](../../../TwoControl/Clifford/Universal/Distance.lean#L141) | Internal geometric core used to prove `trace_inequality`. |

Status:
used by `hsDistance_mul_le`.

Important note:
the comment in `Distance.lean` still says this "isolates it here as a single
assumption", but the current declaration is a theorem with a proof.  The
comment is stale relative to the implementation.

### Lemma 9: Two-Factor Product Error Bound

Paper label: `lem:hs-small-product-rule`.

Lean declaration:

| Lean declaration | File | Alignment |
|---|---|---|
| `hsDistance_mul_le` | [`Distance.lean`](../../../TwoControl/Clifford/Universal/Distance.lean#L474) | Direct theorem with explicit unitary hypotheses. |

Status:
used in final theorem replacement induction and in Lemma 12's Boykin
three-factor error bound.

### Lemma 10: Product Error Bound

Paper label: `lem:hs-big-product-rule`.

Lean declarations:

| Lean declaration | File | Alignment |
|---|---|---|
| `hsDistance_circuitMatrix_le_sum` | [`Distance.lean`](../../../TwoControl/Clifford/Universal/Distance.lean#L518) | General list version of the paper induction. |
| `clifford_rz_circuit_replacement` | [`MainTheorem.lean`](../../../TwoControl/Clifford/Universal/MainTheorem.lean#L95) | Specialized replacement induction used in the final theorem. |

Status:
used.  The final theorem currently uses a custom induction
`clifford_rz_circuit_replacement` rather than only applying the generic list
lemma, because each `R_z` factor is replaced by a list of gates, not by one
single factor.

### Lemma 11: Two-Qubit Synthesis Into `{C(X), H, T, R_z}`

Paper label: `lem:implementation-of-a-2-qubit-gate`.

Lean declarations:

| Lean declaration | File | Alignment |
|---|---|---|
| `lemma11_two_qubit_synthesis` | [`Statements.lean`](../../../TwoControl/Clifford/Statements.lean#L1229) | Direct two-qubit synthesis theorem, up to global phase. |
| `two_qubit_gate_has_clifford_rz_circuit` | [`CliffordRz.lean`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L14) | Universal-layer wrapper around Lemma 11. |
| `embedded_two_qubit_clifford_rz_lift` | [`CliffordRz.lean`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L177) | Lifts a two-qubit Lemma 11 circuit into an `n`-qubit placement. |
| `easy_gate_factor_to_clifford_rz` | [`CliffordRz.lean`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L263) | Replaces one easy-gate factor by Clifford+`R_z`. |
| `easy_circuit_to_clifford_rz` | [`CliffordRz.lean`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L329) | Replaces all factors of a Lemma 1 easy circuit. |
| `clifford_rz_synthesis_from_lemma1` | [`CliffordRz.lean`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L340) | Combines Lemma 1 and Lemma 11 into Clifford+`R_z` synthesis. |

Supporting exact identities:

| Paper identity | Lean declaration |
|---|---|
| `S = T*T` | [`embedded_phaseS_is_clifford_t`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L218), backed by private `phaseT_sq_eq_phaseS` at [`CliffordRz.lean`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L21). |
| `S† = T^6` | [`embedded_phaseSdagger_is_clifford_t`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L237), backed by private `phaseT_six_eq_phaseSdagger` at [`CliffordRz.lean`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L43). |

Implementation differences:

- Paper states exact equality.  Lean proves `GlobalPhaseEquivalent` for the
  two-qubit synthesis because global phase is irrelevant and necessary for the
  existing Euler/decomposition route.
- Lean has substantial embedding code because Lemma 11 is intrinsically
  two-qubit but Lemma 1 produces arbitrary embedded two-qubit factors.

### Lemma 12: Approximation Of `R_z` By `{H,T}`

Paper label: `lem:approximation-of-rz`.

Paper statement:
for any `ε > 0`, there is an `{H,T}` circuit `C` with
`d(R_z(θ), C) < ε`.

Lean endpoints:

| Lean declaration | File | Alignment |
|---|---|---|
| `lemma12_rz_approximation_by_ht` | [`Lemma12/MainTheorem.lean`](../../../TwoControl/Clifford/Lemma12/MainTheorem.lean#L29) | Direct paper Lemma 12 statement. |
| `HT_Rz_dense` | [`BoykinDensity.lean`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L2406) | Main proof theorem used by Lemma 12. |
| `embedded_rz_approximation_by_clifford_t` | [`RzApproximation.lean`](../../../TwoControl/Clifford/Universal/RzApproximation.lean#L316) | Lifts one-qubit Lemma 12 into arbitrary embedded `n`-qubit gates. |

Status:
proved on the `Universal.MainTheorem` import path.  It is not an axiom there.

#### Lemma 12 Proof Spine

The paper does not explain or prove Lemma 12.  The Lean proof uses a
Boykin-style density argument.

| Step | Lean declaration(s) | Role |
|---|---|---|
| `{H,T}` circuit type | [`HTCircuit`](../../../TwoControl/Clifford/Lemma12/Common/HTCircuit.lean#L18), [`HTCircuit.eval`](../../../TwoControl/Clifford/Lemma12/Common/HTCircuit.lean#L23) | Local list type and semantics for Lemma 12. |
| HT unitarity | [`oneQubitHTPrimitive_eval_mem_unitaryGroup`](../../../TwoControl/Clifford/Lemma12/Common/HTCircuit.lean#L36), [`HTCircuit_eval_mem_unitaryGroup`](../../../TwoControl/Clifford/Lemma12/Common/HTCircuit.lean#L45) | Shows all generated circuits are unitary. |
| Pauli matrices | [`pauliX`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L40), [`pauliY`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L44), [`pauliZ`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L48), [`pauliVec`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L52) | Algebraic basis for axis rotations. |
| Axis rotations | [`axisRotation`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L56), [`axisRotation_closed_form`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L230), [`axisRotation_mem_unitaryGroup`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L235) | Defines and proves unitarity of `exp(i φ n·σ)`. |
| Boykin matrices and axes | [`boykinLambda`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L275), [`boykinA`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L295), [`boykinB`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L304), [`boykinAxis₁`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L323), [`boykinAxis₂`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L327) | Constructs two irrational rotations about orthogonal axes. |
| Axis facts | [`boykin_axes_unit`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L354), [`boykin_axes_orthogonal`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L373), [`boykinA_is_axisRotation`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L822), [`boykinB_is_axisRotation`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L992) | Connects `A`, `B` to concrete rotations. |
| Irrational angle proof | [`boykinZeta`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1072), [`boykinPolynomial`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1077), [`boykin_zeta_not_rootOfUnity`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1177), [`boykinLambda_irrational`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1206) | Proves the generated rotations have dense integer powers. |
| Concrete HT circuits for `A`, `B` | [`boykinA_circuit`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1399), [`boykinB_circuit`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1403), [`boykinA_circuit_eval`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1406), [`boykinB_circuit_eval`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1412) | Proves `A` and `B` are actually generated by `{H,T}`. |
| Integer powers as circuits | [`primitiveInvCircuit`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1421), [`circuitInverse`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1438), [`circuitPower`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1452), [`zpowMatrix`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1467), [`boykinA_power_circuit`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1470), [`boykinB_power_circuit`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1474) | Makes dense powers executable as HT circuit lists. |
| Dense powers | [`boykinA_powers_dense_axis₁`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1630), [`boykinB_powers_dense_axis₂`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1641) | Approximates rotations about each Boykin axis. |
| SU(2)-pair algebra | [`su2Pair`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1715), [`pauliVec_mul_pauliVec`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1757), [`su2Pair_mul`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1808), [`axisRotation_eq_su2Pair`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1857) | Algebra for Euler products. |
| Boykin Euler expansion | [`boykin_euler_product_expansion`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L2021) | Expands the two-axis product. |
| Three-factor error bound | [`hsDistance_triple_mul_le`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L2125) | Uses product-distance bounds for three approximate rotations. |
| Euler-product approximation | [`boykin_HT_approx_euler_product`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L2145) | Builds one HT circuit approximating `R(n₁,α)R(n₂,β)R(n₁,γ)`. |
| Specialization to `R_z` | private `standardZ_axisRotation_boykin_euler` at [`BoykinDensity.lean`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L2230), private `rz_eq_axisRotation_standardZ` at [`BoykinDensity.lean`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L1665), [`HT_Rz_dense`](../../../TwoControl/Clifford/Lemma12/Boykin/BoykinDensity.lean#L2406) | Converts the Boykin density theorem into the exact `R_z` statement needed by the paper. |
| Paper Lemma 12 wrapper | [`lemma12_rz_approximation_by_ht`](../../../TwoControl/Clifford/Lemma12/MainTheorem.lean#L29) | Re-exposes `HT_Rz_dense` as the paper's Lemma 12. |

#### Lemma 12 Embedding Layer

Paper Lemma 12 is one-qubit.  The final theorem must replace embedded `R_z`
factors inside arbitrary `n`-qubit circuits.

| Lean declaration | File | Role |
|---|---|---|
| `hsDistance_eq_embed_oneQubit` | [`RzApproximation.lean`](../../../TwoControl/Clifford/Universal/RzApproximation.lean#L222) | Preserves `hsDistance` when a one-qubit matrix is embedded. |
| `hsDistance_eq_embed_twoQubit` | [`RzApproximation.lean`](../../../TwoControl/Clifford/Universal/RzApproximation.lean#L230) | Same for two-qubit embedding. |
| `hsDistance_localOnFirst` | [`RzApproximation.lean`](../../../TwoControl/Clifford/Universal/RzApproximation.lean#L250) | Preserves distance for `A ⊗ I`. |
| `hsDistance_localOnSecond` | [`RzApproximation.lean`](../../../TwoControl/Clifford/Universal/RzApproximation.lean#L258) | Preserves distance for `I ⊗ A`. |
| `embedded_rz_approximation_by_clifford_t` | [`RzApproximation.lean`](../../../TwoControl/Clifford/Universal/RzApproximation.lean#L316) | The theorem consumed by `MainTheorem.lean`. |

#### Lemma 12 Versus Ross-Selinger

Ross-Selinger is present, but it is not the proof used by the final theorem.

| Area | Status |
|---|---|
| [`TwoControl/RossSelinger/Main.lean`](../../../TwoControl/RossSelinger/Main.lean#L1) | Explicitly says this leg is independent of Lemma 12's universality proof. |
| `TwoControl/RossSelinger/MANormalForm.lean` and `TwoControl/RossSelinger/Algorithm.lean` | Contain remaining `sorry`s in the current repo. |
| Final universality import path | Does not import Ross-Selinger.  It imports `Lemma12.Main` through `RzApproximation.lean`. |

## Final Replacement And Error Accounting

This is the Lean implementation of the paper's final proof paragraph.

| Paper step | Lean declaration | Notes |
|---|---|---|
| Get exact easy circuit `C₁` from Lemma 1. | [`clifford_rz_synthesis_from_lemma1`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L340) | Uses `lemma1_decomposition_to_easy_gate_set`. |
| Replace 2-qubit easy gates by Clifford+`R_z`. | [`easy_gate_factor_to_clifford_rz`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L263), [`easy_circuit_to_clifford_rz`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L329) | Uses Lemma 11 and embedded lifting. |
| Replace `S`, `S†`. | [`embedded_phaseS_is_clifford_t`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L218), [`embedded_phaseSdagger_is_clifford_t`](../../../TwoControl/Clifford/Universal/CliffordRz.lean#L237) | Formal versions of `S=T*T`, `S†=T^6`. |
| Replace each `R_z(θ_j)` by `{H,T}`. | [`one_gate_replacement`](../../../TwoControl/Clifford/Universal/MainTheorem.lean#L65), [`clifford_rz_circuit_replacement`](../../../TwoControl/Clifford/Universal/MainTheorem.lean#L95) | Uses `embedded_rz_approximation_by_clifford_t`. |
| Bound total error. | [`clifford_rz_synthesis_approximates_by_clifford_t`](../../../TwoControl/Clifford/Universal/MainTheorem.lean#L175) | Uses `hsDistance_mul_le`, exact-gate zero distance, and arithmetic budget. |
| Global phase does not matter for distance. | private [`hsDistance_eq_of_globalPhaseEquivalent_left`](../../../TwoControl/Clifford/Universal/MainTheorem.lean#L19), [`hsDistance_eq_zero_of_globalPhaseEquivalent`](../../../TwoControl/Clifford/Universal/Distance.lean#L404) | Lean-only bridge because synthesis is up to global phase. |

## Paper Items Not Used Or Not Formalized

| Paper item | Current Lean status |
|---|---|
| `R_x(θ)` definition | Not used on the final theorem path; no direct universality-path declaration. |
| Controlled-`R_z` gate count `3 * 2^(n-2) - 2` | Not formalized and not used. |
| General unitary gate-count recurrence and closed form | Not formalized and not used. |
| "Call to action" compiler procedure | The Lean code proves existence/synthesis witnesses, but does not implement an extracted compiler with complexity guarantees. |

## Lean Ideas Not In The Paper

| Lean idea | Why it exists |
|---|---|
| `GlobalPhaseEquivalent` | Exact matrix equality is too strict for quantum circuits; Lemma 11 and one-qubit synthesis naturally produce global phase. |
| Explicit gate placement structures | Paper diagrams hide wire-placement details; Lean must encode embeddings and permutations. |
| Zero-qubit and one-qubit final theorem branches | Paper states the theorem informally for all unitaries; Lean theorem is indexed by `n : ℕ`, so edge cases must be handled. |
| `length + 1` error budget | Avoids the `k = 0` division issue in the paper's `ε/k` sketch. |
| Boykin proof of Lemma 12 | Paper only states Lemma 12.  Lean gives a full independent density proof. |
| Ross-Selinger branch | Separate compiler/optimality work; not part of the current final theorem proof. |

## Current Assumption / `sorry` Status

Relevant search:

```text
rg -n "\b(sorry|axiom|opaque|admit)\b" \
  TwoControl/Clifford/Lemma12 \
  TwoControl/Clifford/Universal \
  TwoControl/RossSelinger \
  -g '*.lean'
```

Observed status:

| Area | Status |
|---|---|
| `TwoControl/Clifford/Universal` | No `sorry`, `axiom`, `opaque`, or `admit` matches in the searched files. |
| `TwoControl/Clifford/Lemma12` | No `sorry`, `axiom`, `opaque`, or `admit` matches in the searched files. |
| `TwoControl/RossSelinger` | Contains `sorry`s in the Ross-Selinger leg, which is not imported by `Universal.MainTheorem`. |

So, for the path ending at
[`clifford_t_is_universal`](../../../TwoControl/Clifford/Universal/MainTheorem.lean#L356),
the project currently uses the proved Boykin Lemma 12 route, not a Lemma 12
axiom and not the incomplete Ross-Selinger route.

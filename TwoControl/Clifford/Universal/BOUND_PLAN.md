# Plan For A Clifford+T Upper-Bound Theorem

This document lays out a reasonable path for proving an upper bound for the
length of the circuits produced by the Clifford+T universality development.

The main point is that there are two different problems:

1. bounding the exact recursive synthesis skeleton from Lemma 1 through
   Clifford+`R_z`;
2. bounding the cost of approximating each `R_z` gate by `{H,T}` as a function
   of precision.

The first problem should be done inside the current `Universal` development.
The second problem belongs to the Lemma 12 approximation branch and necessarily
depends on `ε`.

## Current Theorem Path

The current final theorem is:

```lean
TwoControl.Clifford.Universal.clifford_t_is_universal
```

Its proof path is:

```text
lemma1_decomposition_to_easy_gate_set
  -> clifford_rz_synthesis_from_lemma1
  -> clifford_rz_synthesis_approximates_by_clifford_t
  -> clifford_t_is_universal
```

The relevant files are:

```text
TwoControl/Clifford/Universal/GateSets.lean
TwoControl/Clifford/Universal/RecursiveDecomposition.lean
TwoControl/Clifford/Universal/CliffordRz.lean
TwoControl/Clifford/Universal/RzApproximation.lean
TwoControl/Clifford/Universal/MainTheorem.lean
TwoControl/Clifford/Lemma12/
```

The current proof establishes existence of circuits, but it does not preserve a
length bound in the theorem statements.

## Target Shape

The final theorem should not claim a bound depending only on `n` unless `ε` is
fixed.  Approximation by `{H,T}` must become more expensive as `ε` decreases.

A realistic final theorem should have the shape:

```lean
theorem clifford_t_is_universal_bounded {n : ℕ}
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      hsDistance U (circuitMatrix gates) < ε ∧
      gates.length ≤ cliffordTBound n ε := by
  ...
```

The exact definition of `cliffordTBound` should be built from smaller
component bounds rather than guessed as one closed form.

## Phase 1: Add Bounded Synthesis Predicates

Do not try to recover bounds from existing `Synthesizes` proofs after the fact.
The current statements intentionally hide the producing list inside an
existential.  Instead, add bounded variants that build the list and the bound at
the same time.

Suggested predicates:

```lean
def SynthesizesWithLength {N : ℕ}
    (allowed : Square N → Prop) (U : Square N) (bound : ℕ) : Prop :=
  ∃ gates : List (Square N),
    CircuitOver allowed gates ∧
    circuitMatrix gates = U ∧
    gates.length ≤ bound

def SynthesizesUpToGlobalPhaseWithLength {N : ℕ}
    (allowed : Square N → Prop) (U : Square N) (bound : ℕ) : Prop :=
  ∃ gates : List (Square N),
    CircuitOver allowed gates ∧
    GlobalPhaseEquivalent U (circuitMatrix gates) ∧
    gates.length ≤ bound
```

Likely location:

```text
TwoControl/Clifford/Universal/GateSets.lean
```

Useful helper lemmas:

```lean
SynthesizesWithLength.toSynthesizes
SynthesizesUpToGlobalPhaseWithLength.toSynthesizesUpToGlobalPhase
SynthesizesWithLength.singleton
SynthesizesWithLength.mul
SynthesizesWithLength.append
SynthesizesWithLength.map_or_lift
SynthesizesUpToGlobalPhaseWithLength.mul
```

The most important arithmetic helper is:

```lean
(g₁ ++ g₂).length = g₁.length + g₂.length
```

Use additive bounds at first.  Avoid optimizing constants until the whole bound
pipeline compiles.

## Phase 2: Bound Uniformly Controlled `R_z`

The paper has a recurrence:

```text
R(n) = 2 R(n-1) + 2
R(2) = 1
R(n) = 3 * 2^(n-2) - 2
```

The Lean development uses `controlledRzFamily m`, where the family has `m`
control wires and total size `m + 1`.  So it is cleaner to define the bound in
Lean's indexing first.

Suggested definition:

```lean
def controlledRzEasyBound : ℕ → ℕ
| 0 => 1
| m + 1 => 2 * controlledRzEasyBound m + 2
```

Intended theorem:

```lean
theorem synthesizes_controlled_rz_family_bounded (m : ℕ)
    (α : Fin (2 ^ m) → ℝ) :
    SynthesizesWithLength
      (EasyGate (m + 1))
      (controlledRzFamily m α)
      (controlledRzEasyBound m)
```

This should follow the proof of:

```lean
synthesizes_controlled_rz_family
```

in `RecursiveDecomposition.lean`.

Expected proof structure:

```text
base m = 0:
  controlledRzFamily 0 α = embedded one-qubit Rz
  length bound = 1

step m+1:
  use controlled_rz_reduction_step
  circuit shape:
    CX, lifted smaller Rz family, CX, lifted smaller Rz family
  length bound:
    1 + controlledRzEasyBound m + 1 + controlledRzEasyBound m
    = 2 * controlledRzEasyBound m + 2
```

Do not initially prove the closed form.  The recurrence is enough for the next
phase.

Optional later theorem:

```lean
theorem controlledRzEasyBound_closed_form :
    controlledRzEasyBound m = 3 * 2 ^ m - 2
```

Check the indexing before committing to the exact closed form.  It may differ
from the paper by a shift because paper `n` is total qubits while Lean `m` is
number of controls.

## Phase 3: Bound Uniformly Controlled `R_y`

The paper converts controlled `R_y` families to controlled `R_z` using
`S†`, `H`, controlled `R_z`, `H`, `S`.

Lean theorem:

```lean
controlled_ry_family_via_controlled_rz
```

Suggested bound:

```lean
def controlledRyEasyBound (m : ℕ) : ℕ :=
  controlledRzEasyBound m + 4
```

Intended theorem:

```lean
theorem synthesizes_controlled_ry_family_bounded (m : ℕ)
    (θ : Fin (2 ^ m) → ℝ) :
    SynthesizesWithLength
      (EasyGate (m + 1))
      (controlledRyFamily m θ)
      (controlledRyEasyBound m)
```

This should mirror:

```lean
synthesizes_controlled_ry_family
```

The `+ 4` accounts for `S†`, `H`, `H`, `S` as embedded easy gates.

## Phase 4: Bound First-Qubit Block-Diagonal Synthesis

Lean theorem:

```lean
synthesizes_first_qubit_block_diag
```

It uses:

```text
general_demultiplexing_step
recursive synthesis of Q
controlledRzFamily
recursive synthesis of P
```

If `easyBound m` bounds arbitrary `m`-qubit exact synthesis, then a first-qubit
block-diagonal gate on `m + 1` qubits should be bounded by:

```lean
2 * easyBound m + controlledRzEasyBound m
```

Suggested theorem:

```lean
theorem synthesizes_first_qubit_block_diag_bounded {m : ℕ} (hm : 1 ≤ m)
    (ih : ∀ W : Square (2 ^ m),
      W ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ →
        SynthesizesWithLength (EasyGate m) W (easyBound m))
    (U₀ U₁ : Square (2 ^ m))
    (hU₀ : U₀ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ)
    (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ) :
    SynthesizesWithLength
      (EasyGate (m + 1))
      (firstQubitBlockDiag m U₀ U₁)
      (2 * easyBound m + controlledRzEasyBound m)
```

This theorem is a direct bounded version of the current unbounded one.

## Phase 5: Bound Lemma 1

The paper's recursive shape is:

```text
U(n) = 4 U(n-1) + 3 R(n)
```

The Lean recursion has:

```text
P block diagonal
controlled Ry/Rz middle
Q block diagonal
```

Each block diagonal contributes two recursive lower-unitary syntheses plus one
controlled `R_z` family.  The middle contributes one controlled `R_y` family.

A conservative Lean-native recurrence is:

```lean
def easyBound : ℕ → ℕ
| 0 => 1
| 1 => 1
| 2 => 1
| n + 1 =>
    4 * easyBound n
      + 2 * controlledRzEasyBound n
      + controlledRyEasyBound n
```

Since `controlledRyEasyBound n = controlledRzEasyBound n + 4`, this is:

```text
easyBound(n+1) = 4 * easyBound(n) + 3 * controlledRzEasyBound(n) + 4
```

The extra `+4` is real in Lean because `R_y` is synthesized using explicit
`S† H Rz H S` gates.  The paper's recurrence may hide those one-qubit gates or
count only two-qubit gates, which is why the paper formula should not be copied
directly.

Intended theorem:

```lean
theorem lemma1_decomposition_to_easy_gate_set_bounded {n : ℕ} (hn : 2 ≤ n)
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    SynthesizesWithLength (EasyGate n) U (easyBound n)
```

This should be proved by strengthening the existing strong-induction proof in:

```lean
lemma1_decomposition_to_easy_gate_set
```

Do not replace the existing theorem.  Add the bounded theorem and then derive
the existing theorem from it later if that cleanup is useful.

## Phase 6: Bound Lemma 11 Locally

The universal proof uses Lemma 11 to replace arbitrary embedded two-qubit gates
by Clifford+`R_z` circuits.

Current theorem:

```lean
lemma11_two_qubit_synthesis
```

Target:

```lean
def lemma11Bound : ℕ := ...

theorem lemma11_two_qubit_synthesis_bounded (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ gates : List TwoQubitPrimitive,
      GlobalPhaseEquivalent U (twoQubitCircuitMatrix gates) ∧
      gates.length ≤ lemma11Bound
```

This belongs near `lemma11_two_qubit_synthesis` in:

```text
TwoControl/Clifford/Statements.lean
```

There are two possible approaches:

1. Prove a coarse bound from the known fixed list shapes in the proof.
2. Refactor the private helper theorems to return length bounds.

Prefer the coarse bound first.  It can be intentionally loose.  For the final
asymptotic theorem, any constant bound is enough.

## Phase 7: Bound Easy-Gate To Clifford+`R_z`

Current bridge:

```lean
easy_gate_factor_to_clifford_rz
easy_circuit_to_clifford_rz
clifford_rz_synthesis_from_lemma1
```

Suggested factor bound:

```lean
def easyFactorToCliffordRzBound : ℕ :=
  max lemma11Bound 6
```

Rationale:

- an embedded arbitrary two-qubit gate uses Lemma 11;
- an embedded `H` is one gate;
- an embedded `S` is two `T` gates;
- an embedded `S†` is six `T` gates;
- an embedded `R_z` is one gate.

Target theorem:

```lean
theorem easy_gate_factor_to_clifford_rz_bounded {n : ℕ}
    {U : Square (2 ^ n)}
    (hU : EasyGate n U) :
    SynthesizesUpToGlobalPhaseWithLength
      (CliffordTRzGate n) U easyFactorToCliffordRzBound
```

Then:

```lean
theorem easy_circuit_to_clifford_rz_bounded {n : ℕ}
    {U : Square (2 ^ n)}
    {easyLen : ℕ}
    (hU : SynthesizesWithLength (EasyGate n) U easyLen) :
    SynthesizesUpToGlobalPhaseWithLength
      (CliffordTRzGate n) U
      (easyFactorToCliffordRzBound * easyLen)
```

Finally:

```lean
def cliffordRzSkeletonBound (n : ℕ) : ℕ :=
  easyFactorToCliffordRzBound * easyBound n

theorem clifford_rz_synthesis_from_lemma1_bounded {n : ℕ} (hn : 2 ≤ n)
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    SynthesizesUpToGlobalPhaseWithLength
      (CliffordTRzGate n) U
      (cliffordRzSkeletonBound n)
```

## Phase 8: Track Number Of `R_z` Gates Separately

For the final Clifford+T bound, total Clifford+`R_z` length is not enough.
We need the number of `R_z` factors because only those factors expand by the
precision-dependent Lemma 12 approximation.

Add a count function:

```lean
def rzGateCount {n : ℕ} (gates : List (Square (2 ^ n))) : ℕ :=
  gates.countP (fun gate => ∃ θ : ℝ, IsEmbeddedOneQubitGate n (rz θ) gate)
```

But `countP` over existential propositions may require decidability.  If this
gets annoying, avoid computable counting and instead carry a theorem:

```lean
def HasAtMostRzGates {n : ℕ}
    (gates : List (Square (2 ^ n))) (k : ℕ) : Prop :=
  ∃ marked : List Bool,
    marked.length = gates.length ∧
    marked.count true ≤ k ∧
    ...
```

Simpler first target:

```lean
number of Rz gates ≤ total number of CliffordTRz gates
```

Then the final theorem can use the total skeleton length as the number of
possible approximated gates.  This is loose but easy:

```text
k ≤ cliffordRzSkeletonBound n
```

That avoids a separate `R_z` counting system initially.

## Phase 9: Quantitative Lemma 12 Interface

The current Lemma 12 is qualitative:

```lean
lemma12_rz_approximation_by_ht :
  ∀ θ ε, 0 < ε →
    ∃ gates, hsDistance (rz θ) (oneQubitHTCircuitMatrix gates) < ε
```

For length bounds, we need:

```lean
def rzApproxBound (δ : ℝ) : ℕ := ...

theorem lemma12_rz_approximation_by_ht_bounded
    (θ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ gates : List OneQubitHTPrimitive,
      hsDistance (rz θ) (oneQubitHTCircuitMatrix gates) < δ ∧
      gates.length ≤ rzApproxBound δ
```

There are two tracks:

1. Add this as an abstract theorem/interface first, if the goal is to finish
   the universal bound modulo quantitative Lemma 12.
2. Prove it later in `TwoControl/Clifford/Lemma12`, either from the Boykin
   density proof with an explicit density modulus or from a Ross-Selinger style
   compiler theorem.

Important: a bound depending only on `n` cannot be true for arbitrary `ε`.
This bound must depend on precision.

## Phase 10: Bound Embedded Lemma 12 Replacement

Current theorem:

```lean
embedded_rz_approximation_by_clifford_t
```

Bounded target:

```lean
theorem embedded_rz_approximation_by_clifford_t_bounded {n : ℕ}
    {R : Square (2 ^ n)} {θ δ : ℝ}
    (hδ : 0 < δ)
    (hR : IsEmbeddedOneQubitGate n (rz θ) R) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      hsDistance R (circuitMatrix gates) < δ ∧
      gates.length ≤ rzApproxBound δ
```

This should be a bounded version of:

```lean
embedded_rz_approximation_by_clifford_t
```

in `RzApproximation.lean`.

The existing embedding lemmas already show distance preservation.  The new work
is only proving that embedding an HT circuit preserves list length.

## Phase 11: Final Clifford+T Bound

Let:

```lean
def skeletonBound (n : ℕ) : ℕ :=
  cliffordRzSkeletonBound n
```

Use the same error-budget idea as the current final theorem:

```lean
δ = ε / (skeletonBound n + 1)
```

This is more conservative than dividing by the actual number of `R_z` gates,
but it avoids needing a precise `R_z` count.

Suggested final bound:

```lean
def cliffordTBound (n : ℕ) (ε : ℝ) : ℕ :=
  skeletonBound n * max 1 (rzApproxBound (ε / ((skeletonBound n : ℝ) + 1)))
```

This is intentionally loose.  It says every Clifford+`R_z` skeleton factor may
expand to at most the `R_z` approximation cost.  Exact Clifford+T factors really
only cost one gate, but the coarse bound is much easier to prove.

More precise later:

```text
nonRzCount + rzCount * rzApproxBound(ε / (rzCount + 1))
```

First target theorem:

```lean
theorem clifford_t_is_universal_bounded_of_two_le {n : ℕ} (hn : 2 ≤ n)
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      hsDistance U (circuitMatrix gates) < ε ∧
      gates.length ≤ cliffordTBound n ε
```

Then add wrappers for `n = 0` and `n = 1`, mirroring:

```lean
zero_qubit_clifford_t_is_universal
one_qubit_clifford_t_is_universal
clifford_t_is_universal
```

Final theorem:

```lean
theorem clifford_t_is_universal_bounded {n : ℕ}
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      hsDistance U (circuitMatrix gates) < ε ∧
      gates.length ≤ cliffordTBound n ε
```

## Optional Phase 12: Closed Forms And Big-O Style Theorems

Once recursive bounds compile, prove closed forms or simpler asymptotic upper
bounds.

Useful targets:

```lean
theorem controlledRzEasyBound_le_exp :
    controlledRzEasyBound m ≤ C₁ * 2 ^ m

theorem easyBound_le_exp :
    easyBound n ≤ C₂ * 4 ^ n

theorem cliffordRzSkeletonBound_le_exp :
    cliffordRzSkeletonBound n ≤ C₃ * 4 ^ n
```

This is likely easier than proving the exact paper closed form.  It also
matches what we actually need: a reasonable upper bound in terms of `n`.

For the final Clifford+T theorem, the meaningful asymptotic statement is:

```text
length ≤ O(4^n * rzApproxBound(ε / O(4^n)))
```

If the quantitative Lemma 12 branch later proves:

```text
rzApproxBound δ ≤ C * log(1/δ)
```

then the final theorem can become:

```text
length ≤ O(4^n * (n + log(1/ε)))
```

But that depends on the quantitative approximation theorem, not just the
current qualitative universality proof.

## Recommended Order Of Work

1. Add bounded synthesis predicates in `GateSets.lean`.
2. Prove bounded append/multiplication helper lemmas.
3. Add `controlledRzEasyBound` and prove
   `synthesizes_controlled_rz_family_bounded`.
4. Add `controlledRyEasyBound` and prove
   `synthesizes_controlled_ry_family_bounded`.
5. Add `easyBound` and prove
   `lemma1_decomposition_to_easy_gate_set_bounded`.
6. Prove a coarse constant `lemma11Bound`.
7. Prove `clifford_rz_synthesis_from_lemma1_bounded`.
8. Add a quantitative Lemma 12 interface.
9. Prove `embedded_rz_approximation_by_clifford_t_bounded`.
10. Prove `clifford_t_is_universal_bounded_of_two_le`.
11. Add zero- and one-qubit wrappers.
12. Add simpler exponential corollaries such as `easyBound_le_const_mul_four_pow`.

## Practical Guidance

Use loose constants.  The first successful theorem should prioritize a clean
dependency story over tightness.

Avoid proving the exact paper formula until after a recursive Lean bound works.
The paper counts a different thing than the Lean circuit lists currently count:
it focuses on two-qubit gates, while Lean's `EasyGate` and `CliffordTGate`
lists include embedded one-qubit gates as list factors.

The most robust first milestone is:

```text
There exists a Clifford+Rz circuit of length ≤ C * 4^n.
```

The most robust second milestone is:

```text
There exists a Clifford+T circuit of length
≤ C * 4^n * rzApproxBound(ε / (C * 4^n + 1)).
```


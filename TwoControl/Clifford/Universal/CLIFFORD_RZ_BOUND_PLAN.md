# Stage 1 Bound Plan: Exact Clifford+Rz Synthesis

This is the first staged upper-bound target.  It deliberately stops before
Lemma 12.  There is no approximation parameter, no `ε`, and no `{H,T}`
approximation of `R_z`.

The goal is to prove a bounded version of the exact Clifford+`R_z` synthesis
theorem:

```lean
clifford_rz_synthesis_from_lemma1
```

The target gate set is:

```lean
CliffordTRzGate n
```

which represents embedded gates from:

```text
{ C(X), H, T, R_z(θ) }
```

The desired theorem should say: for every `n ≥ 2` and every `n`-qubit unitary
`U`, there is a Clifford+`R_z` circuit synthesizing `U` up to global phase, and
the circuit length is bounded by a function of `n` alone.

## Target Theorem

First prove the paper-facing `n ≥ 2` version:

```lean
theorem clifford_rz_synthesis_bounded_of_two_le {n : ℕ} (hn : 2 ≤ n)
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTRzGate n) gates ∧
      GlobalPhaseEquivalent U (circuitMatrix gates) ∧
      gates.length ≤ cliffordRzBound n
```

Then, optionally, add zero- and one-qubit wrappers later.  The paper's
recursive argument starts at two qubits, and the current Lean recursive Lemma 1
also has the hypothesis `2 ≤ n`, so the first milestone should match that.

The first useful asymptotic corollary is:

```lean
theorem cliffordRzBound_le_const_mul_four_pow {n : ℕ} (hn : 2 ≤ n) :
    cliffordRzBound n ≤ C * 4 ^ n
```

for some deliberately loose constant `C`.

Tight constants do not matter in this stage.  The point is to formalize the
paper intuition that the exact decomposition has exponential size on the order
of `4^n`.

## Why This Is Not The Same Count As `doc.tex`

The paper's counting section counts "2-qubit gates" in a macro sense.  In
particular, the paper treats some two-qubit operations as one unit in the
easy-gate stage.

The Lean Clifford+`R_z` theorem counts a different object:

```lean
List (Square (2 ^ n))
```

whose entries each satisfy `CliffordTRzGate n`.  This means embedded one-qubit
gates such as `H`, `T`, and `R_z` are list entries, and embedded CNOT gates are
list entries.  So the exact closed form in `doc.tex` should not be copied as a
Lean theorem for `CliffordTRzGate` length.

The correct Lean goal is:

```text
same recursive shape, possibly different constants, still O(4^n).
```

## Proposed File Layout

Keep this staged work separate from the final approximation theorem.

Suggested files:

```text
TwoControl/Clifford/Universal/BoundedSynthesis.lean
TwoControl/Clifford/Universal/RecursiveBounds.lean
TwoControl/Clifford/Universal/CliffordRzBounds.lean
```

Suggested imports:

```lean
-- BoundedSynthesis.lean
import TwoControl.Clifford.Universal.GateSets

-- RecursiveBounds.lean
import TwoControl.Clifford.Universal.RecursiveDecomposition
import TwoControl.Clifford.Universal.BoundedSynthesis

-- CliffordRzBounds.lean
import TwoControl.Clifford.Universal.CliffordRz
import TwoControl.Clifford.Universal.RecursiveBounds
```

Once stable, add:

```lean
import TwoControl.Clifford.Universal.CliffordRzBounds
```

to:

```text
TwoControl/Clifford/Universal/Main.lean
```

Do not import these into `MainTheorem.lean` until the bounded theorem is needed
there.

## Phase 1: Bounded Synthesis Infrastructure

Add bounded variants of the existing synthesis predicates.

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

Helper lemmas:

```lean
theorem SynthesizesWithLength.toSynthesizes :
    SynthesizesWithLength allowed U b → Synthesizes allowed U

theorem SynthesizesUpToGlobalPhaseWithLength.toSynthesizesUpToGlobalPhase :
    SynthesizesUpToGlobalPhaseWithLength allowed U b →
      SynthesizesUpToGlobalPhase allowed U

theorem synthesizesWithLength_singleton :
    allowed U → SynthesizesWithLength allowed U 1

theorem synthesizesWithLength_mul :
    SynthesizesWithLength allowed U bU →
    SynthesizesWithLength allowed V bV →
    SynthesizesWithLength allowed (U * V) (bU + bV)

theorem synthesizesUpToGlobalPhaseWithLength_mul :
    SynthesizesUpToGlobalPhaseWithLength allowed U bU →
    SynthesizesUpToGlobalPhaseWithLength allowed V bV →
    SynthesizesUpToGlobalPhaseWithLength allowed (U * V) (bU + bV)
```

Also add monotonicity:

```lean
theorem SynthesizesWithLength.mono_bound :
    b₁ ≤ b₂ →
    SynthesizesWithLength allowed U b₁ →
    SynthesizesWithLength allowed U b₂

theorem SynthesizesUpToGlobalPhaseWithLength.mono_bound :
    b₁ ≤ b₂ →
    SynthesizesUpToGlobalPhaseWithLength allowed U b₁ →
    SynthesizesUpToGlobalPhaseWithLength allowed U b₂
```

These helpers prevent arithmetic cleanup from polluting every construction
proof.

## Phase 2: Bound Controlled `R_z` Families

The Lean object is:

```lean
controlledRzFamily m α
```

It is an `(m+1)`-qubit gate: one target wire and `m` control wires.

Define the Lean-native recursive bound:

```lean
def controlledRzBound : ℕ → ℕ
| 0 => 1
| m + 1 => 2 * controlledRzBound m + 2
```

Interpretation:

```text
m = 0:
  one embedded R_z gate

m + 1:
  CNOT
  smaller controlled R_z family
  CNOT
  smaller controlled R_z family
```

Bounded theorem:

```lean
theorem synthesizes_controlled_rz_family_bounded (m : ℕ)
    (α : Fin (2 ^ m) → ℝ) :
    SynthesizesWithLength
      (EasyGate (m + 1))
      (controlledRzFamily m α)
      (controlledRzBound m)
```

This follows the current proof of:

```lean
synthesizes_controlled_rz_family
```

The proof should reuse:

```lean
controlled_rz_reduction_step
synthesizes_liftMiddle
EasyGate.of_embedded_two_qubit
EasyGate.rz
```

Closed form is optional:

```lean
theorem controlledRzBound_closed_form :
    controlledRzBound m = 3 * 2 ^ m - 2
```

This closed form is in Lean's indexing.  It is not literally the paper's
`3 * 2^(n-2) - 2`, because the paper's `n` is total qubits and the paper uses
a different gate-count unit.

## Phase 3: Bound Controlled `R_y` Families

Lean theorem:

```lean
controlled_ry_family_via_controlled_rz
```

Define:

```lean
def controlledRyBound (m : ℕ) : ℕ :=
  controlledRzBound m + 4
```

The `+ 4` accounts for:

```text
S†, H, H, S
```

Bounded theorem:

```lean
theorem synthesizes_controlled_ry_family_bounded (m : ℕ)
    (θ : Fin (2 ^ m) → ℝ) :
    SynthesizesWithLength
      (EasyGate (m + 1))
      (controlledRyFamily m θ)
      (controlledRyBound m)
```

This theorem is still in the easy-gate layer, because Lemma 1 is an easy-gate
decomposition.

## Phase 4: Bound First-Qubit Block-Diagonal Synthesis

Current theorem:

```lean
synthesizes_first_qubit_block_diag
```

It decomposes:

```text
blockdiag(U₀, U₁)
```

into:

```text
lower Q
controlled R_z family
lower P
```

If `easyBound m` bounds arbitrary `m`-qubit easy synthesis, then the
block-diagonal bound is:

```lean
2 * easyBound m + controlledRzBound m
```

Target theorem:

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
      (2 * easyBound m + controlledRzBound m)
```

This is the first place where the paper's `4 U(n-1)` shape becomes visible:
there are two recursive calls for each block-diagonal factor, and there are
two such factors in the CS decomposition.

## Phase 5: Bound Lemma 1 In The Easy-Gate Layer

Current theorem:

```lean
lemma1_decomposition_to_easy_gate_set
```

Define the recursive easy-gate bound:

```lean
def easyBound : ℕ → ℕ
| 0 => 1
| 1 => 1
| 2 => 1
| n + 1 =>
    4 * easyBound n
      + 2 * controlledRzBound n
      + controlledRyBound n
```

Equivalently:

```text
easyBound(n+1)
  = 4 * easyBound(n) + 3 * controlledRzBound(n) + 4
```

The terms correspond to:

```text
4 * easyBound(n):
  four recursive lower unitaries from the two block-diagonal factors

2 * controlledRzBound(n):
  one controlled R_z family for each block-diagonal demultiplexing

controlledRyBound(n):
  the middle CS controlled R_y family
```

Target theorem:

```lean
theorem lemma1_decomposition_to_easy_gate_set_bounded {n : ℕ} (hn : 2 ≤ n)
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    SynthesizesWithLength (EasyGate n) U (easyBound n)
```

Proof strategy:

1. Copy the strong-induction shape from
   `lemma1_decomposition_to_easy_gate_set`.
2. Base case `n = 2` uses one easy embedded two-qubit gate, so length is `1`.
3. Recursive case uses:
   - `general_cosine_sine_step`;
   - bounded block-diagonal synthesis for `P`;
   - bounded controlled `R_y` synthesis for `R`;
   - bounded block-diagonal synthesis for `Q`;
   - bounded multiplication helpers.
4. Use `mono_bound` and `ring_nf` / `omega` / `nlinarith` only at the end of
   each construction step.

At the end of this phase, we have a paper-aligned exact decomposition bound,
but still over `EasyGate`.

## Phase 6: Add A Constant Bound For Lemma 11

Current theorem:

```lean
lemma11_two_qubit_synthesis
```

It returns a two-qubit circuit over `TwoQubitPrimitive`, up to global phase.

We need a constant bound:

```lean
def lemma11Bound : ℕ := ...
```

Target theorem:

```lean
theorem lemma11_two_qubit_synthesis_bounded (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ gates : List TwoQubitPrimitive,
      GlobalPhaseEquivalent U (twoQubitCircuitMatrix gates) ∧
      gates.length ≤ lemma11Bound
```

This should live near `lemma11_two_qubit_synthesis` in:

```text
TwoControl/Clifford/Statements.lean
```

Use a coarse constant first.  It is acceptable if the first version overcounts.
The asymptotic theorem only needs this to be independent of `n`.

Recommended route:

1. Inspect the proof of `lemma11_two_qubit_synthesis`.
2. Add bounded versions of its private helper constructions only where needed.
3. Avoid optimizing the exact list length.
4. Pick `lemma11Bound` generously enough that list arithmetic is painless.

## Phase 7: Bound One Easy Gate Converted To Clifford+Rz

Current theorem:

```lean
easy_gate_factor_to_clifford_rz
```

Define:

```lean
def easyFactorToCliffordRzBound : ℕ :=
  max lemma11Bound 6
```

Reason:

```text
arbitrary embedded two-qubit gate:
  Lemma 11, at most lemma11Bound

embedded H:
  one Clifford+Rz gate

embedded S:
  T T, length 2

embedded S†:
  T T T T T T, length 6

embedded R_z:
  one Clifford+Rz gate
```

Bounded theorem:

```lean
theorem easy_gate_factor_to_clifford_rz_bounded {n : ℕ}
    {U : Square (2 ^ n)}
    (hU : EasyGate n U) :
    SynthesizesUpToGlobalPhaseWithLength
      (CliffordTRzGate n) U
      easyFactorToCliffordRzBound
```

This proof should follow the cases in `easy_gate_factor_to_clifford_rz`.

## Phase 8: Bound An Easy Circuit Converted To Clifford+Rz

Current theorem:

```lean
easy_circuit_to_clifford_rz
```

Target theorem:

```lean
theorem easy_circuit_to_clifford_rz_bounded {n : ℕ}
    {U : Square (2 ^ n)} {b : ℕ}
    (hU : SynthesizesWithLength (EasyGate n) U b) :
    SynthesizesUpToGlobalPhaseWithLength
      (CliffordTRzGate n) U
      (easyFactorToCliffordRzBound * b)
```

Proof strategy:

1. Induct over the easy-gate list from `hU`.
2. Convert each factor using `easy_gate_factor_to_clifford_rz_bounded`.
3. Append the resulting Clifford+`R_z` circuits.
4. The length arithmetic is:

```text
sum over b factors of at most easyFactorToCliffordRzBound
≤ easyFactorToCliffordRzBound * b
```

This is easier if the induction tracks:

```lean
processed.length ≤ easyFactorToCliffordRzBound * original.length
```

## Phase 9: First Stage Main Bound

Define:

```lean
def cliffordRzBound (n : ℕ) : ℕ :=
  easyFactorToCliffordRzBound * easyBound n
```

Target theorem:

```lean
theorem clifford_rz_synthesis_from_lemma1_bounded {n : ℕ} (hn : 2 ≤ n)
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    SynthesizesUpToGlobalPhaseWithLength
      (CliffordTRzGate n) U
      (cliffordRzBound n)
```

Equivalent unpacked theorem:

```lean
theorem clifford_rz_synthesis_bounded_of_two_le {n : ℕ} (hn : 2 ≤ n)
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTRzGate n) gates ∧
      GlobalPhaseEquivalent U (circuitMatrix gates) ∧
      gates.length ≤ cliffordRzBound n
```

This theorem is the exact Clifford+`R_z` analogue of the final universality
theorem, minus approximation.

## Phase 10: Prove A Coarse `4^n` Corollary

The theorem above gives a recursive bound.  To match the paper's intuition,
prove a coarse exponential corollary.

First prove:

```lean
theorem controlledRzBound_le_const_mul_two_pow :
    controlledRzBound m ≤ C₁ * 2 ^ m
```

Then prove:

```lean
theorem easyBound_le_const_mul_four_pow {n : ℕ} (hn : 2 ≤ n) :
    easyBound n ≤ C₂ * 4 ^ n
```

Finally:

```lean
theorem cliffordRzBound_le_const_mul_four_pow {n : ℕ} (hn : 2 ≤ n) :
    cliffordRzBound n ≤ C₃ * 4 ^ n
```

Use intentionally large constants.

## Proving The `4^n` Bound Cleanly

The recurrence has the shape:

```text
easyBound(n+1) = 4 * easyBound(n) + O(2^n)
```

A direct induction on:

```lean
easyBound n ≤ C * 4 ^ n
```

will not close without slack, because the recursive step leaves an extra
positive `O(2^n)` term.

Use a stronger induction invariant with slack:

```lean
easyBound n + A * 2 ^ n + B ≤ C * 4 ^ n
```

for constants `A`, `B`, `C` chosen generously.

This works because:

```text
4 * (A * 2^n) dominates A * 2^(n+1) plus the new O(2^n) error.
```

After proving the slack theorem, derive:

```lean
easyBound n ≤ C * 4 ^ n
```

by `linarith` / `omega` from nonnegativity of the slack terms.

This is usually easier in Lean than proving the exact closed form.

## Acceptance Criteria

This first stage is complete when these compile:

```lean
SynthesizesWithLength
SynthesizesUpToGlobalPhaseWithLength
synthesizes_controlled_rz_family_bounded
synthesizes_controlled_ry_family_bounded
lemma1_decomposition_to_easy_gate_set_bounded
lemma11_two_qubit_synthesis_bounded
easy_gate_factor_to_clifford_rz_bounded
easy_circuit_to_clifford_rz_bounded
clifford_rz_synthesis_from_lemma1_bounded
clifford_rz_synthesis_bounded_of_two_le
cliffordRzBound_le_const_mul_four_pow
```

No theorem in this stage should import or mention:

```text
TwoControl.Clifford.Lemma12
embedded_rz_approximation_by_clifford_t
lemma12_rz_approximation_by_ht
ε
rzApproxBound
```

Those belong to the later approximation stage.

## Suggested Agent Work Split

The work can be parallelized after `BoundedSynthesis.lean` exists.

1. Infrastructure agent:
   bounded synthesis predicates and append/mul helper lemmas.

2. Recursive exact agent:
   controlled `R_z`, controlled `R_y`, block diagonal, and bounded Lemma 1.

3. Lemma 11 constant agent:
   bounded version of the two-qubit Clifford+`R_z` theorem.

4. Clifford+`R_z` bridge agent:
   bounded easy-factor conversion, bounded easy-circuit conversion, and first
   stage main theorem.

5. Arithmetic agent:
   closed/coarse exponential bounds, especially the `4^n` corollary.

The connection point is:

```lean
lemma1_decomposition_to_easy_gate_set_bounded
lemma11_two_qubit_synthesis_bounded
```

Once those two compile, the exact Clifford+`R_z` bound should be mostly list
length bookkeeping.


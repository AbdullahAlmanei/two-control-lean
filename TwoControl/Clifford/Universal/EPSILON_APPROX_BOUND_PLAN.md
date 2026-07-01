# Epsilon Approximation Bound Investigation

This is the staged plan for extending the exact Clifford+`R_z` bound to a full
Clifford+T bound with an epsilon-dependent length bound.

The current exact stage is proved:

```lean
clifford_rz_synthesis_bounded_of_two_le
cliffordRzBound_le_const_mul_four_pow
```

That stage deliberately stops before Lemma 12.  The remaining work is to prove
a bounded version of the `R_z` approximation step and then compose it with the
already proved Clifford+`R_z` skeleton bound.

## Current Lemma 12 Path

The current qualitative endpoint is:

```lean
TwoControl.Clifford.Lemma12.lemma12_rz_approximation_by_ht
```

It has shape:

```lean
theorem lemma12_rz_approximation_by_ht
    (theta : R) {epsilon : R} (hepsilon : 0 < epsilon) :
    exists gates : List OneQubitHTPrimitive,
      hsDistance (rz theta) (oneQubitHTCircuitMatrix gates) < epsilon
```

The proof delegates to:

```lean
HT_Rz_dense
boykin_HT_approx_euler_product
boykinA_powers_dense_axis1
boykinB_powers_dense_axis2
axisRotation_powers_dense
```

The important issue is that `axisRotation_powers_dense` currently uses
topological density:

```lean
Dense.exists_dist_lt
Metric.continuousAt_iff
```

This proves existence of a good integer power, but it does not retain any bound
on the size of that integer.  Since the HT circuit length is proportional to
the chosen integer powers, the present Lemma 12 proof is not yet quantitative.

## Bound We Need

For the full Clifford+T theorem, the useful one-qubit approximation theorem is
uniform in the angle:

```lean
noncomputable def rzApproxBound (epsilon : R) : N := ...

theorem lemma12_rz_approximation_by_ht_bounded
    (theta : R) {epsilon : R} (hepsilon : 0 < epsilon) :
    exists gates : List OneQubitHTPrimitive,
      hsDistance (rz theta) (oneQubitHTCircuitMatrix gates) < epsilon
        /\ gates.length <= rzApproxBound epsilon
```

The word "uniform" matters.  A target-specific bound depending on `theta` is
much easier, but it would not give a final theorem bounded only by `n` and
`epsilon`.  We want `rzApproxBound epsilon`, not `rzApproxBound theta epsilon`.

## Recommended First Proof Strategy

The most realistic first theorem is a noncomputable uniform bound from
compactness, not an explicit asymptotic bound.

The reason this should work is:

1. For every angle `theta`, qualitative Lemma 12 gives some HT circuit.
2. For a fixed HT circuit `C`, the function
   `theta |-> hsDistance (rz theta) (oneQubitHTCircuitMatrix C)` is continuous.
3. Therefore the set of angles approximated by `C` within `epsilon` is open.
4. It is enough to cover one compact period of `rz`, for example `[0, 4*pi]`.
5. The qualitative theorem gives an open cover of this compact interval.
6. Compactness gives a finite subcover.
7. The maximum length of the finitely many circuits in that subcover is a
   uniform bound for all angles in that period.
8. Periodicity of `rz` extends the result to all real angles.

This route gives a real theorem of the desired shape.  It will not give a nice
closed form such as `O(log(1/epsilon))`, but it gives a valid function
`rzApproxBound epsilon` that is independent of `theta`.

## Stage A: Bounded Lemma 12 Shape

Suggested file:

```text
TwoControl/Clifford/Lemma12/Bounded.lean
```

Imports:

```lean
import TwoControl.Clifford.Lemma12.MainTheorem
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact
```

The exact imports may need adjustment after implementation begins.

Top-level definitions and theorems:

```lean
noncomputable def rzApproxBound (epsilon : R) : N := ...

theorem continuous_rz :
    Continuous fun theta : R => rz theta

theorem continuous_hsDistance_rz_fixed
    (C : List OneQubitHTPrimitive) :
    Continuous fun theta : R =>
      hsDistance (rz theta) (oneQubitHTCircuitMatrix C)

theorem rz_period_four_pi (theta : R) :
    rz (theta + 4 * Real.pi) = rz theta

theorem exists_periodic_representative
    (theta : R) :
    exists theta0 : R,
      theta0 in Set.Icc 0 (4 * Real.pi) /\ rz theta0 = rz theta

theorem lemma12_rz_approximation_by_ht_bounded
    (theta : R) {epsilon : R} (hepsilon : 0 < epsilon) :
    exists gates : List OneQubitHTPrimitive,
      hsDistance (rz theta) (oneQubitHTCircuitMatrix gates) < epsilon
        /\ gates.length <= rzApproxBound epsilon
```

Implementation note: if proving a representative in `[0, 4*pi]` becomes
annoying, use `AddCircle` or `Complex.Circle` instead.  The project already
uses circle-related imports in the Lemma 12 branch, and the statement can still
export a real-angle theorem at the end.

## Stage B: Length-Preserving Embedding

Suggested file:

```text
TwoControl/Clifford/Universal/RzApproximationBounds.lean
```

Imports:

```lean
import TwoControl.Clifford.Universal.RzApproximation
import TwoControl.Clifford.Lemma12.Bounded
import TwoControl.Clifford.Universal.BoundedSynthesis
```

Top-level helper theorems:

```lean
theorem length_embedOneQubitHTCircuit
    (p : OneQubitPlacement n) (gates : List OneQubitHTPrimitive) :
    (embedOneQubitHTCircuit p gates).length = gates.length

theorem length_embedTwoQubitCliffordTCircuit
    (p : TwoQubitPlacement n) (gates : List TwoQubitCliffordTPrimitive) :
    (embedTwoQubitCliffordTCircuit p gates).length = gates.length

theorem length_map_onFirst
    (gates : List OneQubitHTPrimitive) :
    (gates.map TwoQubitCliffordTPrimitive.onFirst).length = gates.length

theorem length_map_onSecond
    (gates : List OneQubitHTPrimitive) :
    (gates.map TwoQubitCliffordTPrimitive.onSecond).length = gates.length
```

Bounded embedded replacement:

```lean
theorem embedded_rz_approximation_by_clifford_t_bounded {n : N}
    {R : Square (2 ^ n)} {theta delta : R}
    (hdelta : 0 < delta)
    (hR : IsEmbeddedOneQubitGate n (rz theta) R) :
    exists gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates
        /\ hsDistance R (circuitMatrix gates) < delta
        /\ gates.length <= rzApproxBound delta
```

This proof should mirror the existing unbounded theorem:

```lean
embedded_rz_approximation_by_clifford_t
```

The only new work is carrying list lengths through `map`.

## Stage C: Bounded Replacement Of A Clifford+Rz Circuit

Suggested file:

```text
TwoControl/Clifford/Universal/MainTheoremBounds.lean
```

Imports:

```lean
import TwoControl.Clifford.Universal.MainTheorem
import TwoControl.Clifford.Universal.CliffordRzBounds
import TwoControl.Clifford.Universal.RzApproximationBounds
```

Define a per-factor replacement bound:

```lean
noncomputable def oneGateApproxBound (delta : R) : N :=
  max 1 (rzApproxBound delta)
```

The `max 1` handles Clifford+T gates that are already exact and are replaced
by a singleton list.

Bound one gate:

```lean
theorem one_gate_replacement_bounded {n : N}
    (hn : 0 < 2 ^ n)
    {gate : Square (2 ^ n)}
    (hgate : CliffordTRzGate n gate)
    {delta : R} (hdelta : 0 < delta) :
    exists replacement : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) replacement
        /\ hsDistance gate (circuitMatrix replacement) < delta
        /\ circuitMatrix replacement in Matrix.unitaryGroup (Fin (2 ^ n)) C
        /\ replacement.length <= oneGateApproxBound delta
```

Bound a whole Clifford+`R_z` list:

```lean
theorem clifford_rz_circuit_replacement_bounded {n : N}
    (hn : 0 < 2 ^ n)
    {gates : List (Square (2 ^ n))}
    (hGates : CircuitOver (CliffordTRzGate n) gates)
    {delta : R} (hdelta : 0 < delta) :
    exists replacement : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) replacement
        /\ hsDistance (circuitMatrix gates) (circuitMatrix replacement)
             <= (gates.length : R) * delta
        /\ circuitMatrix replacement in Matrix.unitaryGroup (Fin (2 ^ n)) C
        /\ replacement.length <= gates.length * oneGateApproxBound delta
```

This is the bounded version of the private theorem currently named:

```lean
clifford_rz_circuit_replacement
```

The proof is the same induction, with one extra length inequality using:

```lean
List.length_append
Nat.add_le_add
Nat.mul_succ
```

## Stage D: Final Clifford+T Bound

Use the exact stage-one skeleton bound as the number of possible replacement
sites:

```lean
noncomputable def cliffordTBound (n : N) (epsilon : R) : N :=
  cliffordRzBound n *
    oneGateApproxBound (epsilon / ((cliffordRzBound n : R) + 1))
```

Main theorem for `n >= 2`:

```lean
theorem clifford_t_is_universal_bounded_of_two_le {n : N} (hn : 2 <= n)
    (U : Square (2 ^ n))
    (hU : U in Matrix.unitaryGroup (Fin (2 ^ n)) C)
    {epsilon : R} (hepsilon : 0 < epsilon) :
    exists gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates
        /\ hsDistance U (circuitMatrix gates) < epsilon
        /\ gates.length <= cliffordTBound n epsilon
```

Proof sketch:

1. Use `clifford_rz_synthesis_from_lemma1_bounded` to get a Clifford+`R_z`
   skeleton with length at most `cliffordRzBound n`.
2. Set
   `delta = epsilon / ((cliffordRzBound n : R) + 1)`.
3. Replace each skeleton gate using
   `clifford_rz_circuit_replacement_bounded`.
4. Error is at most `actualSkeletonLength * delta`.
5. Since `actualSkeletonLength <= cliffordRzBound n`,
   this is strictly less than `epsilon`.
6. Length is at most
   `actualSkeletonLength * oneGateApproxBound delta`, hence at most
   `cliffordTBound n epsilon`.

After that, add the zero- and one-qubit wrappers following the existing
structure in `MainTheorem.lean`.

## What This Proves And What It Does Not Prove

This staged path proves a valid epsilon-dependent length bound for the full
Clifford+T theorem:

```text
length <= cliffordTBound n epsilon
```

It does not prove a simple closed-form rate for `rzApproxBound epsilon`.
The compactness proof gives existence of a uniform finite bound, not an
efficient compiler.

For a rate such as `O(log(1/epsilon))`, the current Boykin-density proof is not
enough as written.  We would need a quantitative Diophantine approximation
branch, or a different compiler theorem such as a Ross-Selinger style result.

## Recommended Order

1. Prove `lemma12_rz_approximation_by_ht_bounded` using compactness.
2. Prove the embedding length lemmas in `RzApproximationBounds.lean`.
3. Prove `embedded_rz_approximation_by_clifford_t_bounded`.
4. Prove bounded one-gate replacement.
5. Prove bounded replacement for a whole Clifford+`R_z` circuit.
6. Prove `clifford_t_is_universal_bounded_of_two_le`.
7. Add zero- and one-qubit wrappers.
8. Only after that, decide whether to pursue an explicit asymptotic bound for
   `rzApproxBound epsilon`.

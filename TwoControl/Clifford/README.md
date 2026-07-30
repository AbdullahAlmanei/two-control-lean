# Clifford+T universality

This directory formalizes Clifford+T universality (project 2 in the
[root README](../../README.md)), building on the "two controls" vocabulary in
`TwoControl/`. The headline result is
`Universal.MainTheorem.clifford_t_is_universal`: every `n`-qubit unitary is
approximable to arbitrary Hilbert-Schmidt precision by a Clifford+T circuit.
It is `sorry`-free, and its axiom closure is exactly
`[propext, Classical.choice, Quot.sound]`.

The proof follows `reference/cliff/universal_new_gates.tex` (July 2026). The
`R_z`-approximation half (Lemma 12) uses that paper's `G₁ = e^{-3iπ/8}THTHT`
and `G₂ = (HT⁴)G₁(HT⁴)†`, whose rotation axes are orthogonal. An earlier
Boykin-style density track was deleted when this route landed; nothing here
depends on it.

For the paper-level theorem statements and their formal dependency graph, see
the Blueprint (`blueprint/`): `overview.tex` for scope and per-node status,
then `clifford_circuits.tex`, `clifford_exact.tex`, `clifford_lemma12.tex`,
`clifford_universal.tex`, `clifford_lemma11.tex`, and `clifford_bounds.tex`.
This file is a code-level map for reading and extending the Lean source.

## Two tracks

The Lean code splits into two tracks that share vocabulary but have
different status:

1. **Exact synthesis (complete, no `sorry`s):** every `n`-qubit unitary is
   exactly synthesized (up to global phase) over `{CX, H, S, S†, R_z}`, and
   Lemma 12 shows `{H,T}` approximates any single `R_z(θ)` in Hilbert-Schmidt
   distance. This is `Definitions.lean`, `Statements.lean`,
   `Universal/GateSets.lean`, `Universal/Distance.lean`,
   `Universal/CosineSineStep.lean`, `Universal/RecursiveDecomposition.lean`,
   `Universal/CliffordRz.lean`, `Universal/MainTheorem.lean`, and all of
   `Lemma12/` except `Bounded.lean`.
2. **Quantitative bounds (in progress, several `sorry`s):** length bounds
   (`gates.length ≤ ...`) on top of the exact-synthesis route, aiming for a
   closed-form `C · 4^n · (n + log(1/ε))` Clifford+T circuit-length bound.
   This is every file whose name ends in `Bounds`
   (`Universal/RecursiveBounds.lean`, `Universal/CliffordRzBounds.lean`,
   `Universal/RzApproximationBounds.lean`, `Universal/MainTheoremBounds.lean`)
   plus `Lemma12/LogPrecision.lean` and `Lemma12/Bounded.lean`.

   Each `*Bounds.lean` file already imports its exact-track counterpart and
   reuses its generic helper lemmas directly — don't hand-copy a proof from
   the exact file into the bounds file; remove `private` from the shared
   lemma instead. (We deduped one round of exactly that anti-pattern; see the
   commit history for `Universal/CliffordRz.lean` and
   `Universal/RecursiveDecomposition.lean`.)

   Open `sorry`s live in `Lemma12/LogPrecision.lean` (the `logPrecision`
   bookkeeping lemmas), `Lemma12/Bounded.lean` (the quantitative Lemma 12
   interface — the module doc there records the intended Ross-Selinger/KMM
   proof route), `Universal/RzApproximationBounds.lean`, and
   `Universal/MainTheoremBounds.lean` (the final closed-form bound, staged as
   a plan with each stage stubbed until the pieces above land).

## Directory guide

- **`Definitions.lean`, `Statements.lean`** — shared gate matrices (`hadamard2`,
  `phaseS`, `phaseT`, `rz`, `cnot`, ...) and the one-qubit exact ZYZ/Euler
  synthesis statements the rest of the project builds on.
- **`Universal/`** — the arbitrary-`n`-qubit synthesis and bound layer.
  Import order (each file only imports earlier ones in this list, plus
  `Statements.lean` and, for `RzApproximation`/`RzApproximationBounds`, the
  `Lemma12/` result described below):
  `GateSets` → `Distance` / `CosineSineStep` → `RecursiveDecomposition` →
  `CliffordRz` → `BoundedSynthesis` → `RecursiveBounds` → `CliffordRzBounds`
  → `RzApproximation` → `RzApproximationBounds` → `MainTheorem` →
  `MainTheoremBounds` → `Main` (a thin import-only aggregator).
- **`Lemma12/`** — the one-qubit `{H,T}` approximates `R_z` result
  (Nielsen–Chuang-style density argument via two non-commuting rotations
  `G₁, G₂`). `Common/HTCircuit.lean` is the shared `{H,T}` circuit type;
  `G1G2/` builds the angle/axis/spectral machinery for `G₁, G₂`
  (`AxisRotation` → `SpectralForm` / `Generators` → `AngleIdentification` →
  `Orthogonality` → `RzApprox`); `MainTheorem.lean` assembles the Lemma 12
  theorem from those; `LogPrecision.lean` and `Bounded.lean` are the
  quantitative extension described above; `Main.lean` aggregates.
- **`Main.lean`** (this directory's root) — the top-level import-only
  aggregator for the whole Clifford+T project, imported by `TwoControl/Main.lean`.

## Relationship to other projects in this repo

Clifford+T universality does **not** depend on the paused Ross-Selinger
circuit-synthesis engine (`RossSelinger/`, `KMM/`, both at the repo root) —
that dependency runs the other way: `RossSelinger/` imports
`Universal.GateSets`, `Universal.Distance`, and `Lemma12.Common.HTCircuit`
from here, not the reverse. See the root [README](../../README.md) for the
full three-project map.

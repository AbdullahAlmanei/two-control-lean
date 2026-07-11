# Ross-Selinger (paused)

This is the Ross-Selinger optimal ancilla-free single-qubit circuit synthesis
project: given a target unitary and precision `ε`, produce a Clifford+T
circuit approximating it, with a conditional T-count optimality guarantee.
It is a separate research effort from the "two controls" paper (`TwoControl/`)
and from the Clifford+T universality work (`TwoControl/Clifford/`), though it
depends on the latter (`TwoControl.Clifford.Universal.GateSets`, `.Distance`,
`TwoControl.Clifford.Lemma12.Common.HTCircuit`).

**Status: paused.** Not built by default — `RossSelinger` and `KMM` are
`[[lean_lib]]` targets in `lakefile.toml` but are not in `defaultTargets`, so
plain `lake build` and CI skip them. Build explicitly when picking this back
up:

```bash
lake build RossSelinger KMM
```

## What's proved, conditionally

* `Correctness.rossSelingerSearch_sound_if_returns` — the search's returned
  circuit ε-approximates `Rz θ`, *if* the search returns.
* `Optimality.rossSelingerOracle_optimal_if_returns` — the factoring-oracle
  variant's returned circuit has optimal T-count, *if* it returns.
* `Grid.boundedGridCandidatesAtLevel` — the finite candidate-generation
  kernel: scans a concrete integer coordinate box at a fixed denominator
  level, with both emitted-candidate soundness and bounded completeness
  proved.

Unconditional termination is **not** claimed. The remaining geometric work is
providing bounds large enough for full fixed-level completeness (see
`RossSelinger/Main.lean`'s module doc for the current framing).

## Open `sorry`s

* `RossSelinger/MANormalForm.lean` — `dyadic_unitary_has_ma_figure2_witness`
* `RossSelinger/Algorithm.lean` — `selinger_lemma_7_5`

Both are documented in place as "the remaining paper theorem," not
placeholders for unfinished scaffolding.

## Pipeline shape

Roughly: `GridLemma` → `Grid` (candidate generation) feeds `DiophantineCore`
/ `ZomegaRingTheory` → `Diophantine` (Theorem 6.2 packaging), while `Basic` →
`Selinger75` → `MANormalForm` (Matsumoto-Amano normal form, using the
hand-transcribed Giles-Selinger Figure 2 table) runs in parallel and pulls in
`KMM.ExactSynthesis` for exact synthesis over `ℤ[ω]`. Both feed `Algorithm` →
`Correctness` → `Optimality`, wired together in `Main.lean`.

`CircuitTranslation.lean`, `DistanceBridge.lean`, and `Oracle.lean` are
optional adapters, intentionally not imported by `Main.lean` — kept as
scaffolding for when this resumes, not dead code to prune.

`KMM/` (`KMM.lean` + `KMM/*.lean`) is the exact-synthesis engine this project
leans on: `OmegaArithmetic` (`ℤ[ω]` coordinates, mod-8 residues) →
`Denominator` (smallest-denominator-exponent bookkeeping) →
`ExactSynthesis` (the `HT^k` denominator-descent pipeline, culminating in
`kmm_exact_synthesis`). `DyadicCyclotomic` and `MatrixCompletion` (top-level,
alongside `RossSelinger`/`KMM`) are shared arithmetic/matrix-completion
libraries this pipeline depends on.

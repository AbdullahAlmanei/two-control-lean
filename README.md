# two-control-lean

A Lean + Blueprint project for translating and reconstructing the proof of
"Optimal implementation of quantum gates with two controls".

Visit [this](https://abdullahalmanei.github.io/two-control-lean/) page to view the current status of the proof.

## Projects in this repo

This repo hosts three separate proof efforts sharing one Lean package:

1. **The two-controls paper** (`TwoControl/Section3.lean`-`Section7.lean` plus
   the shared helper files below them) — the project this repo is named for.
   Complete and stable.
2. **Clifford+T universality** (`TwoControl/Clifford/`, `TwoControl/CosineSine/`)
   — every `n`-qubit unitary is approximable to arbitrary Hilbert-Schmidt
   precision by a Clifford+T circuit, following
   `reference/cliff/universal_new_gates.tex` (July 2026). The theorem is
   `sorry`-free; the remaining work is quantitative circuit-length bounds. See
   [`TwoControl/Clifford/README.md`](TwoControl/Clifford/README.md).
3. **Ross-Selinger circuit synthesis** (`RossSelinger/`, `KMM/`, plus the
   top-level `DyadicCyclotomic/` and `MatrixCompletion/` support trees) —
   optimal ancilla-free circuit synthesis. Paused: none of its four libraries
   are registered in `lakefile.toml`, so nothing builds it. See
   [`RossSelinger/README.md`](RossSelinger/README.md).

## Status

`lake build` is green. The numbers below come from auditing `#print axioms`
for every public declaration in the built library:

| Track | Status |
|---|---|
| Two-control paper, Sections 3–7 | complete, `sorry`-free |
| Clifford+T universality (`TwoControl/Clifford/`, `TwoControl/CosineSine/`) | complete, `sorry`-free |
| Quantitative circuit-length bounds (`*Bounds.lean`, `Lemma12/{LogPrecision,Bounded}.lean`) | statements written, proofs pending |
| Ross-Selinger / KMM synthesis engine | paused, not registered as a library, not built |

The headline theorem is
`TwoControl.Clifford.Universal.clifford_t_is_universal`, whose axiom closure is
exactly `[propext, Classical.choice, Quot.sound]` — no `sorry`, and no
`native_decide`. (Sections 3–7 and the shared helper layer do use
`native_decide` for finite case checks, so those results additionally rest on
`Lean.ofReduceBool`; nothing in the Clifford+T cone does.)

There are 14 `sorry` sites in the built library, all in the bounds track:
`TwoControl/Clifford/Lemma12/{LogPrecision,Bounded}.lean` and
`TwoControl/Clifford/Universal/{RzApproximationBounds,MainTheoremBounds}.lean`.
They make 26 public declarations `sorry`-dependent. Each corresponding
blueprint node says so explicitly.

Two scope notes. The exact two-qubit synthesis route ("Lemma 11") is fully
proved but is **not** on the critical path of the main theorem — the paper's
own route is a one-qubit-base induction that never introduces arbitrary
two-qubit gates. It is retained because the bounds track is stated against it.
And the source paper's explicit gate counts (`14·4^{n-1} − 9·2^{n-1}`) are out
of scope by prior agreement; the bounds track develops independent, coarser
closed-form bounds instead.

## Structure
- `TwoControl/`: Lean formalization of projects 1 and 2 above
- `RossSelinger/`, `KMM/`, `DyadicCyclotomic/`, `MatrixCompletion/`: paused Ross-Selinger circuit-synthesis engine (project 3). None of the four is registered in `lakefile.toml`, so nothing builds them; see [`RossSelinger/README.md`](RossSelinger/README.md) for how to re-register when resuming
- `blueprint/`: Blueprint proof map and dependency graph. Start with `blueprint/src/chapters/overview.tex` — it states the scope, the per-track status, and what the status marks in the dependency graph mean
- `reference/cliff/`: the Clifford+T universality papers and related sources
- `reference/rocq/`: original Rocq reference repo
- `reference/paper/`: source paper
- `docs/`: migration methodology, theorem map, journal

## Local workflow

The blueprint tooling is Python; the Lean side is Lake.

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install leanblueprint

lake build
lake build TwoControl:docs
leanblueprint checkdecls   # every \lean{...} in the blueprint exists
leanblueprint pdf          # blueprint/print/print.pdf
leanblueprint web          # blueprint/web/, and regenerates blueprint/lean_decls
leanblueprint serve
```

`leanblueprint web` rewrites `blueprint/lean_decls`, which is committed and is
what `checkdecls` reads — regenerate it whenever you add, rename, or remove a
`\lean{}` reference, or CI will fail on a stale entry.

To reproduce the status audit for a single result:

```bash
printf 'import TwoControl\n#print axioms TwoControl.Clifford.Universal.clifford_t_is_universal\n' > /tmp/chk.lean
lake env lean /tmp/chk.lean
```

`[propext, Classical.choice, Quot.sound]` means no `sorry` and no
compiler-trust axiom. Grepping for `sorry` is not enough on its own: a proof
can be complete and still inherit a `sorry` from something it uses.

Local API docs are written to `.lake/build/doc/`.

`leanblueprint serve` only serves the blueprint itself.

To preview the full local site, including the homepage and API docs:

```bash
cd home_page
bundle install
cd ..
scripts/serve_local_site.sh
```

This serves a combined local site at `http://127.0.0.1:8000/` by default.

You can also serve just the API docs with:

```bash
cd .lake/build/doc
python3 -m http.server 8001
```

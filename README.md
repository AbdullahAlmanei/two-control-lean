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
   — a quantitative Boykin-style density bound for Clifford+T universality,
   built on top of the two-controls vocabulary. Active; see
   [`TwoControl/Clifford/README.md`](TwoControl/Clifford/README.md).
3. **Ross-Selinger circuit synthesis** (`RossSelinger/`, `KMM/`, plus the
   top-level `DyadicCyclotomic`/`MatrixCompletion` libraries) — optimal
   ancilla-free circuit synthesis. Paused; see
   [`RossSelinger/README.md`](RossSelinger/README.md). Not built by default.

## Structure
- `TwoControl/`: Lean formalization of projects 1 and 2 above
- `RossSelinger/`, `KMM/`: paused Ross-Selinger circuit-synthesis engine (project 3), not built by default (not in `defaultTargets`); build explicitly with `lake build RossSelinger KMM` when resumed
- `blueprint/`: Blueprint proof map and dependency graph
- `reference/rocq/`: original Rocq reference repo
- `reference/paper/`: source paper
- `docs/`: migration methodology, theorem map, journal

## Local workflow
```bash
source .venv/bin/activate
lake build
lake build TwoControl:docs
leanblueprint checkdecls
leanblueprint web
leanblueprint serve
```

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

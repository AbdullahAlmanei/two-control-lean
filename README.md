# two-control-lean

A Lean + Blueprint project for translating and reconstructing the proof of
"Optimal implementation of quantum gates with two controls".

Visit [this](https://abdullahalmanei.github.io/two-control-lean/) page to view the current status of the proof.

## Structure
- `TwoControl/`: Lean formalization
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

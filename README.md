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

# two-control-lean

A Lean 4 + [Blueprint](https://github.com/PatrickMassot/leanblueprint) project
formalizing two results in quantum circuit synthesis:

1. **Optimal implementation of quantum gates with two controls** — the original
   target of the project (Sections 3–7).
2. **Clifford+T is universal** — following
   `reference/cliff/universal_new_gates.tex` (July 2026), together with the
   exact-synthesis and optimal-approximation machinery it needs.

Visit [this page](https://abdullahalmanei.github.io/two-control-lean/) for the
rendered blueprint, dependency graph, and API documentation.

## Status

`lake build` is green.  Formalization status was measured by auditing
`#print axioms` for every public declaration:

| Track | Status |
|---|---|
| Two-control paper, Sections 3–7 (`Section3.lean` … `Section7.lean`) | complete, `sorry`-free |
| Clifford+T universality (`Clifford/Universal/`, `Clifford/Lemma12/`) | complete, `sorry`-free |
| Exact synthesis over `D[ω]`, Kliuchnikov–Maslov–Mosca (`KMM/`) | complete, `sorry`-free |
| Quantitative length bounds (`*Bounds.lean`, `Lemma12/{Bounded,LogPrecision}.lean`) | statements written, proofs pending |
| Ross–Selinger approximation compiler (`RossSelinger/`) | architecture proved; two named inputs pending |

The headline theorem is
`TwoControl.Clifford.Universal.clifford_t_is_universal`, whose axiom closure is
exactly `[propext, Classical.choice, Quot.sound]` — no `sorry`, and no
`native_decide`.  (Sections 3–7 and the KMM track do use `native_decide` for
finite case checks, so those results additionally rest on
`Lean.ofReduceBool`.)

There are 16 `sorry` sites in total, all in the last two rows above:
`Clifford/Lemma12/{LogPrecision,Bounded}.lean`,
`Clifford/Universal/{RzApproximationBounds,MainTheoremBounds}.lean`, and
`RossSelinger/{Algorithm,MANormalForm}.lean`.  Each corresponding blueprint
node says so explicitly.

Two notes on scope.  The exact two-qubit synthesis route ("Lemma 11") is fully
proved but is **not** on the critical path of the main theorem — the paper's
own route is a one-qubit-base induction that never introduces arbitrary
two-qubit gates.  It is retained because the bounds track is stated against it.
And the source paper's explicit gate counts (`14·4^{n-1} − 9·2^{n-1}`) are out
of scope by prior agreement; the bounds track develops independent, coarser
closed-form bounds instead.

## Structure

- `TwoControl/`: Lean formalization
  - `Section3.lean` … `Section7.lean`: the two-control paper
  - `CosineSine/`: cosine–sine decomposition
  - `Clifford/`: gate definitions, exact two-qubit synthesis
  - `Clifford/Universal/`: gate sets, distance layer, recursion, main theorem
  - `Clifford/Lemma12/`: the `G₁/G₂` track proving `{H,T}` approximates `R_z`
  - `KMM/`: exact Clifford+T synthesis over `D[ω]`
  - `RossSelinger/`: the optimal approximation compiler (conditional)
- `blueprint/src/chapters/`: blueprint chapters, one per topic.  Start with
  `overview.tex` — it explains the scope, the status of each track, and what
  the status marks in the dependency graph mean.
- `reference/`: source papers (`reference/cliff/`, `reference/paper/`) and the
  original Rocq reference repo (`reference/rocq/`)
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

Local API docs are written to `.lake/build/doc/`.

`leanblueprint serve` only serves the blueprint itself.  To preview the full
local site, including the homepage and API docs:

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

## Checking the `sorry` inventory

To reproduce the audit behind the status table, ask Lean for the axiom closure
of the declarations you care about:

```bash
printf 'import TwoControl\n#print axioms TwoControl.Clifford.Universal.clifford_t_is_universal\n' > /tmp/chk.lean
lake env lean /tmp/chk.lean
```

A result of `[propext, Classical.choice, Quot.sound]` means no `sorry` and no
compiler-trust axiom.  Grepping for `sorry` is not sufficient on its own: a
proof can be complete and still inherit a `sorry` from a declaration it uses.

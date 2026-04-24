# Shared Project Context

Last updated: 2026-04-23

## Purpose

This repo has two equally important goals.

- Build a real Lean formalization of the paper "Optimal implementation of quantum gates with two controls".
- Develop a reusable AI-agent workflow for migrating a large proof from paper and Rocq/Coq into Lean without collapsing the source structure or hallucinating missing steps.

Any new agent should treat both goals as first-class. The mathematics matters, but the project is also explicitly about how to organize agent-assisted proof migration in a disciplined way.

## Ground Truth Priority

When different files disagree about project status, use this order.

1. Lean files in `TwoControl/`.
2. Recent journal entries in `docs/journal/`.
3. Migration packets and appendix citation packets in `docs/migration/packets/`.
4. Blueprint files in `blueprint/src/chapters/`.
5. Older status tables in `docs/migration/`.

Reason: some migration docs were written when the pipeline stopped at Blueprint generation. The repo has moved well beyond that stage.

## Repo Layout

- `TwoControl/`: main Lean formalization, shared helper modules, and section files for the paper.
- `TwoControl/CosineSine/`: focused appendix-style formalization of the 4-by-4 cosine-sine decomposition and its translation into controlled `R_y` gates.
- `blueprint/`: proof map, dependency graph, and generated web/print blueprint artifacts.
- `reference/paper/`: source paper and supporting references.
- `reference/rocq/`: original Rocq formalization that the migration work is based on.
- `docs/migration/`: migration rules, packets, naming conventions, structure audit, theorem map, and context docs.
- `docs/journal/`: day-by-day log of actual progress, proof strategy, failures, and build validation.
- `home_page/` and `build/site-preview/`: generated site assets for local/public browsing.

## Source Layers

1. The paper: official numbering, public theorem identity, and proof narrative.
2. The Rocq proof: existing formal proof, helper lemmas, and decomposition strategy.
3. The packet layer: reconciled migration ledger tying paper objects to Rocq declarations and dependencies.
4. The Blueprint layer: first public-facing proof map and dependency graph.
5. The Lean layer: the actual target formalization now present in this repo.

The early project plan stopped at Blueprint generation. That is no longer the actual scope of the repo.

## Agent Workflow

The project is organized around strict role separation. The core migration pipeline is:

- Paper Extractor: reads the paper and writes only the paper packet.
- Rocq Mapper: reads the Rocq formalization and the paper packet and writes only the Rocq packet.
- Reconciler: merges paper and Rocq packets into one reconciled packet.
- Theorem Map Merger: updates the global theorem ledger.
- Generation Planner: turns reconciled packets into generation packets.
- Blueprint Stub Generator: writes Blueprint section files from generation packets.

The current workspace orchestration also uses Lean-facing roles:

- Lean Symbol Inventory: identifies shared statement-level symbols needed before Lean section stubs.
- Lean Core Scaffolder: creates shared Lean foundations such as `Prelude.lean` and `Definitions.lean`.
- Lean Section Stub Generator: creates theorem declarations with placeholder proofs for one section.
- Lean Root Scaffolder: updates root import files once section files exist.
- Explore: fast read-only codebase exploration.

The design goal is high recall, low hallucination, and clean phase boundaries. Do not silently resolve conflicts between paper and Rocq. Surface ambiguity instead of guessing.

## Current Formalization State

### Main paper path

- `TwoControl/Main.lean` imports `Section3` through `Section7`, so the main Lean story is no longer hypothetical.
- `2026-04-04`: established the AI-agent pipeline and first Blueprint layer.
- `2026-04-08`: stabilized Section 3 and extracted `DiagonalizationHelpers.lean`.
- `2026-04-09`: completed the main Section 4 proofs with a structural block/tensor approach.
- `2026-04-10`: completed Sections 5, 6, and 7 and restored successful module builds.

### Appendix / cosine-sine path

- `docs/migration/packets/appendix_cosinesine_citation_packet.md` explains the mathematical source for the local `cosinesine` claim: the square-block cosine-sine decomposition specialized to 4-by-4 unitaries, traced back to Paige and Wei.
- `TwoControl/CosineSine/Definitions.lean` defines the appendix-facing objects such as `blockDiag2`, `realDiag2`, `csBlockCore`, `ry`, and `conditionalRy`.
- `TwoControl/CosineSine/Statements.lean` contains the local theorem chain that bridges the matrix decomposition to the circuit statement.
- `TwoControl/CosineSine/Main.lean` is an isolated import target for the appendix work.

## What This Conversation Added

This conversation focused first on the cosine-sine appendix layer, not on the main section files.

The following theorems in `TwoControl/CosineSine/Statements.lean` were completed and stabilized:

- `ry_unitary`
- `csParameters_exist_angle`
- `squareBlockCSD_exists`
- `csBlockCore_eq_conditionalRy`
- `cosinesine_exists`

The key mathematical flow is:

1. `squareBlockCSD_exists` gives the square-block cosine-sine factorization of a 4-by-4 unitary.
2. `csParameters_exist_angle` turns the cosine/sine parameters into real angles.
3. `csBlockCore_eq_conditionalRy` identifies the middle cosine-sine block with a controlled pair of `R_y` rotations.
4. `cosinesine_exists` packages the whole factorization as a 2-qubit gate decomposition.

This work was validated with a successful full `lake build` after the final proof cleanup.

## What Works In This Repo

- Preserve the source structure. Use the paper for theorem identity and Rocq for proof discovery, but do not force Rocq names or file boundaries onto Lean.
- Prefer structural proofs over expansion. Block-matrix, Kronecker, and conjugation arguments are far more stable when phrased through small helper lemmas than when expanded entrywise.
- Use narrow helper layers. Short local lemmas for basis-vector `mulVec`, block extraction, projector transport, and tensor reassociation pay off repeatedly.
- For 2-by-2 witness constructions, direct explicit matrices usually beat abstract detours. In the cosine-sine appendix, explicit unitary witnesses built from orthogonal columns worked better than Gram-Schmidt-style Euclidean-space conversions.
- Validate aggressively. Focused builds like `lake build TwoControl.Section4` or `lake build TwoControl.CosineSine.Statements` should be used during local work, and a final full `lake build` is the real arbiter.
- Extract helpers conservatively. The April 8 refactor shows that obviously reusable helpers should move out of section files, but theorem-local witness code should not be extracted too early.

## What Does Not Work Well

- Broad `simp` or `nlinarith` on large tensor/block goals.
- Giant finite-case matrix expansions when a block or Kronecker argument exists.
- Assuming editor diagnostics are enough. Several failures in this repo only appeared under `lake build`.
- Mixing too many abstraction layers at once. Many bad proof attempts came from jumping between raw matrices, block views, and high-level gate language without a stable local bridge.
- For the cosine-sine appendix specifically, Gram-Schmidt and Euclidean-space conversion detours were brittle and expensive compared to direct 2-by-2 constructions.

## Current Architectural Friction

- `docs/migration/theorem_map.md` and some older generation docs are historically useful, but they do not fully reflect current Lean completion status.
- `docs/migration/lean_structure_audit.md` is still relevant: many repeated helper families remain duplicated across section files and should eventually be extracted into shared helper modules.
- Performance matters. Some proofs are logically correct but elaboration-sensitive, so proof shape and local helper design matter as much as the theorem statement.
- In the cosine-sine appendix, `squareBlockCSD_exists` is proof-heavy enough that build-time elaboration cost became part of the engineering problem.

## Key Files For A New Agent

- `README.md`: high-level project purpose and local workflow commands.
- `docs/migration/agent_rules.md`: hard constraints for the migration workflow.
- `docs/migration/lean_structure_audit.md`: current picture of helper duplication and recommended module boundaries.
- `docs/journal/2026-04-04.md`: why the AI-agent pipeline exists.
- `docs/journal/2026-04-08.md`: helper extraction and conservative refactor pattern.
- `docs/journal/2026-04-09.md`: Section 4 proof-hardening lessons.
- `docs/journal/2026-04-10.md`: completion of Sections 5-7 and build validation.
- `docs/migration/packets/appendix_cosinesine_citation_packet.md`: source justification for the local cosine-sine appendix statement.
- `TwoControl/Main.lean`: current main Lean entry point.
- `TwoControl/CosineSine/Statements.lean`: current appendix proof hotspot.

## Workflow Expectations

- Work from the Lean project root when running `lake` commands.
- Use focused validation while editing, then a full `lake build` before treating the state as stable.
- If you are touching a section file, prefer the smallest structural change that exposes the next proof step.
- If you are touching migration docs, remember that some tables are snapshots from an earlier phase of the project.
- If you are asked to explain the math to a human, translate the matrix statements into controlled-gate language and basis-state action; that has been much easier to communicate than raw theorem syntax.

## Useful Commands

- `source .venv/bin/activate`
- `lake build`
- `lake build TwoControl.Section4`
- `lake build TwoControl.Section7`
- `lake build TwoControl.CosineSine.Statements`
- `lake build TwoControl:docs`
- `leanblueprint checkdecls`
- `leanblueprint web`

## Near-Term Next Work

- Sync stale migration status docs with the now-existing Lean section files.
- Continue helper extraction in line with `lean_structure_audit.md`.
- If more work happens in `TwoControl/CosineSine/Statements.lean`, keep the current proof architecture unless there is a clearly simpler structural replacement.
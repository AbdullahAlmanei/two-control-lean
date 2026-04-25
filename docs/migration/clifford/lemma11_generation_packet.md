# Clifford Lemma 11 — Generation Packet

Derived from:
- `docs/migration/clifford/lemma11_paper_packet.md`
- `docs/migration/clifford/lemma11_theorem_map.md`

## Lemma 2 (2-qubit specialization)

- object_id: Lemma 2 (2-qubit specialization)
- blueprint_label: `lem:cliff_2_2q`
- blueprint_section_file: `blueprint/src/chapters/clifford_lemma11.tex`
- blueprint_uses: []
- lean_name: `TwoControl.CosineSine.cosinesine_exists`
- lean_target_file: `TwoControl/CosineSine/Statements.lean`
- lean_namespace: `TwoControl.CosineSine`
- statement_generation_status: imported
- stub_generation_notes: Existing Lean theorem reused directly as the imported cosine-sine node for this blueprint.

## Lemma 3

- object_id: Lemma 3
- blueprint_label: `lem:cliff_3`
- blueprint_section_file: `blueprint/src/chapters/clifford_lemma11.tex`
- blueprint_uses: []
- lean_name: `TwoControl.Clifford.lemma3_ry_via_rz`
- lean_target_file: `TwoControl/Clifford/Statements.lean`
- lean_namespace: `TwoControl.Clifford`
- statement_generation_status: ready
- stub_generation_notes: Keep the statement as a direct matrix identity so the later controlled-rotation argument can use it without introducing a circuit DSL too early.

## Lemma 4 (2-qubit specialization)

- object_id: Lemma 4 (2-qubit specialization)
- blueprint_label: `lem:cliff_4_2q`
- blueprint_section_file: `blueprint/src/chapters/clifford_lemma11.tex`
- blueprint_uses: [`lem:cliff_2_2q`, `lem:cliff_3`]
- lean_name: `TwoControl.Clifford.lemma4_demultiplex_two_qubit`
- lean_target_file: `TwoControl/Clifford/Statements.lean`
- lean_namespace: `TwoControl.Clifford`
- statement_generation_status: ready
- stub_generation_notes: The blueprint proof should present this as the two-qubit demultiplexing consequence of the imported cosine-sine theorem and the `R_y` to `R_z` identity.

## Controlled `R_z` Pair Synthesis

- object_id: Controlled `R_z` pair synthesis
- blueprint_label: `prop:cliff_controlled_rz`
- blueprint_section_file: `blueprint/src/chapters/clifford_lemma11.tex`
- blueprint_uses: []
- lean_name: `TwoControl.Clifford.controlled_rz_pair_uses_standard_gates`
- lean_target_file: `TwoControl/Clifford/Statements.lean`
- lean_namespace: `TwoControl.Clifford`
- statement_generation_status: ready
- stub_generation_notes: Phrase the statement in terms of the target two-qubit primitive set so Lemma 11 can consume it directly.

## One-Qubit Exact Synthesis over `{H, T, R_z(θ)}`

- object_id: One-qubit exact synthesis over `{H, T, R_z(θ)}`
- blueprint_label: `prop:cliff_1q_exact`
- blueprint_section_file: `blueprint/src/chapters/clifford_lemma11.tex`
- blueprint_uses: []
- lean_name: `TwoControl.Clifford.one_qubit_exact_h_t_rz`
- lean_target_file: `TwoControl/Clifford/Statements.lean`
- lean_namespace: `TwoControl.Clifford`
- statement_generation_status: ready
- stub_generation_notes: This local proposition is included because the blueprint would otherwise leave the one-qubit factors from Lemmas 2 and 4 unresolved.

## Lemma 11

- object_id: Lemma 11
- blueprint_label: `lem:cliff_11`
- blueprint_section_file: `blueprint/src/chapters/clifford_lemma11.tex`
- blueprint_uses: [`lem:cliff_2_2q`, `lem:cliff_3`, `lem:cliff_4_2q`, `prop:cliff_controlled_rz`, `prop:cliff_1q_exact`]
- lean_name: `TwoControl.Clifford.lemma11_two_qubit_synthesis`
- lean_target_file: `TwoControl/Clifford/Statements.lean`
- lean_namespace: `TwoControl.Clifford`
- statement_generation_status: ready
- stub_generation_notes: Keep the target statement as a synthesis theorem over the standard two-qubit primitive set. Do not introduce the recursive Lemma 1 track in this first chapter.
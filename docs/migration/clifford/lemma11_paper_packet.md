# Clifford Lemma 11 — Paper Packet

## Scope

- target_object: Lemma 11 from `reference/cliff/clifford-plus-t-is-universal.pdf`
- workflow_mode: paper-only
- rocq_source: none
- dependency_policy: include only nodes explicitly used in the planned proof of Lemma 11
- excluded_from_first_track: the recursive `n`-qubit Lemma 1 argument

## Imported Node — Lemma 2 (2-qubit specialization)

- object_id: Lemma 2 (2-qubit specialization)
- object_type: imported_lemma
- source_anchor: `/tmp/cliff.txt` lines 131-145
- local_support_anchor: `reference/toff_ref/main.tex` label `cosinesine`
- statement_summary: Every `4 x 4` unitary admits a `2 + 2` cosine-sine decomposition with block-diagonal one-qubit factors and a middle conditional-`R_y` pair.
- direct_dependencies: []
- lean_status: already_proved
- lean_declaration: `TwoControl.CosineSine.cosinesine_exists`
- lean_source_file: `TwoControl/CosineSine/Statements.lean`
- notes: Reused as an imported theorem rather than reproved in the Clifford track.

## Node — Lemma 3

- object_id: Lemma 3
- object_type: lemma
- source_anchor: `/tmp/cliff.txt` lines 145-169
- statement_summary: `R_y(α)` is equal to `S^† H R_z(-α) H S`.
- direct_dependencies: []
- lean_status: new_stub_needed
- planned_lean_declaration: `TwoControl.Clifford.lemma3_ry_via_rz`
- notes: This is a direct matrix identity and should stay as a short standalone node.

## Node — Lemma 4 (2-qubit specialization)

- object_id: Lemma 4 (2-qubit specialization)
- object_type: lemma
- source_anchor: `/tmp/cliff.txt` lines 171-179
- local_support_anchor: `reference/toff_ref/main.tex` label `demultiplexing`
- statement_summary: A block-diagonal two-qubit gate `|0><0| ⊗ U0 + |1><1| ⊗ U1` can be rewritten using two one-qubit gates and a conditional `R_z` pair.
- direct_dependencies: [Lemma 2 (2-qubit specialization), Lemma 3]
- lean_status: new_stub_needed
- planned_lean_declaration: `TwoControl.Clifford.lemma4_demultiplex_two_qubit`
- notes: In this project this node is treated as the paper-facing two-qubit demultiplexing lemma derived from the imported cosine-sine theorem plus the `R_y` to `R_z` conversion.

## Node — Controlled `R_z` Pair Synthesis

- object_id: Controlled `R_z` pair synthesis
- object_type: proposition
- source_anchor: `reference/toff_ref/main.tex` label `lemmadiag`
- statement_summary: A two-qubit gate of the form `R_z(α0) ⊗ |0><0| + R_z(α1) ⊗ |1><1|` can be synthesized from `C(X)` and one-qubit gates from `{H, T, R_z(θ)}`.
- direct_dependencies: []
- lean_status: new_stub_needed
- planned_lean_declaration: `TwoControl.Clifford.controlled_rz_pair_uses_standard_gates`
- notes: This is the bridge from paper-level controlled diagonals to the target two-qubit gate set.

## Node — One-Qubit Exact Synthesis

- object_id: One-qubit exact synthesis over `{H, T, R_z(θ)}`
- object_type: proposition
- source_anchor: local proof ingredient
- statement_summary: Every one-qubit unitary can be synthesized exactly using one-qubit gates from `{H, T, R_z(θ)}`.
- direct_dependencies: []
- lean_status: new_stub_needed
- planned_lean_declaration: `TwoControl.Clifford.one_qubit_exact_h_t_rz`
- notes: This is not a numbered Clifford-paper lemma, but it is needed to discharge the one-qubit factors produced by the cosine-sine and demultiplexing steps.

## Target Node — Lemma 11

- object_id: Lemma 11
- object_type: lemma
- source_anchor: `/tmp/cliff.txt` lines 612-616
- statement_summary: Every two-qubit unitary can be synthesized using a circuit built from `{C(X), H, T, R_z(θ)}`.
- direct_dependencies: [Lemma 2 (2-qubit specialization), Lemma 3, Lemma 4 (2-qubit specialization), Controlled `R_z` pair synthesis, One-qubit exact synthesis over `{H, T, R_z(θ)}`]
- lean_status: new_stub_needed
- planned_lean_declaration: `TwoControl.Clifford.lemma11_two_qubit_synthesis`
- notes: The recursive `n`-qubit Lemma 1 proof is intentionally excluded from this first blueprint because it is not needed to reach the two-qubit target.
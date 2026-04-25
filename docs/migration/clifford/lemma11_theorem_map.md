# Clifford Lemma 11 — Theorem Map

| object_id | object_type | paper_source | lean_decl | blueprint_label | status | direct_dependencies | notes |
|---|---|---|---|---|---|---|---|
| Lemma 2 (2-qubit specialization) | imported_lemma | clifford-plus-t-is-universal.pdf + toff_ref `cosinesine` | `TwoControl.CosineSine.cosinesine_exists` | `lem:cliff_2_2q` | imported-proved | none | Existing Lean theorem reused directly |
| Lemma 3 | lemma | clifford-plus-t-is-universal.pdf | `TwoControl.Clifford.lemma3_ry_via_rz` | `lem:cliff_3` | planned-stub | none | Direct matrix identity |
| Lemma 4 (2-qubit specialization) | lemma | clifford-plus-t-is-universal.pdf + toff_ref `demultiplexing` | `TwoControl.Clifford.lemma4_demultiplex_two_qubit` | `lem:cliff_4_2q` | planned-stub | `lem:cliff_2_2q`, `lem:cliff_3` | Paper-only two-qubit demultiplexing node |
| Controlled `R_z` pair synthesis | proposition | toff_ref `lemmadiag` | `TwoControl.Clifford.controlled_rz_pair_uses_standard_gates` | `prop:cliff_controlled_rz` | planned-stub | none | Converts controlled diagonals into the target gate set |
| One-qubit exact synthesis over `{H, T, R_z(θ)}` | proposition | local ingredient | `TwoControl.Clifford.one_qubit_exact_h_t_rz` | `prop:cliff_1q_exact` | planned-stub | none | Used for the remaining one-qubit factors |
| Lemma 11 | lemma | clifford-plus-t-is-universal.pdf | `TwoControl.Clifford.lemma11_two_qubit_synthesis` | `lem:cliff_11` | planned-stub | `lem:cliff_2_2q`, `lem:cliff_3`, `lem:cliff_4_2q`, `prop:cliff_controlled_rz`, `prop:cliff_1q_exact` | First target theorem for the Clifford track |
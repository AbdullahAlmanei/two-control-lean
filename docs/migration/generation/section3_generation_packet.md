# Section 3 — Generation Packet

Derived from:
- section3_reconciled_packet.md

## Lemma 3.1

- paper_id: Lemma 3.1
- blueprint_label: lem:s3_1
- blueprint_section_file: blueprint/src/chapters/section3.tex
- blueprint_uses: []
- lean_name: TwoControl.section3_lemma_3_1
- lean_target_file: TwoControl/Section3.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: No paper-numbered dependencies. Only Rocq helpers (block_decomp, block_multiply, block_equalities, diag2_decomp, Mscale_cancel_l) from MatrixHelpers; no Appendix lemmas needed.
- unresolved_formalization_questions: none

## Lemma 3.2

- paper_id: Lemma 3.2
- blueprint_label: lem:s3_2
- blueprint_section_file: blueprint/src/chapters/section3.tex
- blueprint_uses: []
- lean_name: TwoControl.section3_lemma_3_2
- lean_target_file: TwoControl/Section3.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: Paper cites Theorem A.3 and Lemma A.5, both Appendix items excluded from first Blueprint. Lemma A.5 has no separate Rocq declaration; its content is absorbed into perm_eigenvalues + diag_kron. Rocq formalises the eigenvalue condition via explicit diagonalisation (∃ P Q V with P ⊗ Q = V × diag4 1 1 u0 u1 × V†) rather than eigenvalue-multiset notation.
- unresolved_formalization_questions: none

## Lemma 3.3

- paper_id: Lemma 3.3
- blueprint_label: lem:s3_3
- blueprint_section_file: blueprint/src/chapters/section3.tex
- blueprint_uses: []
- lean_name: TwoControl.section3_lemma_3_3
- lean_target_file: TwoControl/Section3.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: Paper cites Theorem A.3, Lemma A.1, and Lemma A.6, all Appendix items excluded from first Blueprint. All three map directly to Rocq declarations (a3, a1, a6). Rocq formalises the eigenvalue condition via explicit diagonalisation (∃ P U c d with (I 2 ⊗ P) × control (diag2 u0 u1) = U × diag4 c d c d × U†). Longest Section 3 proof (~500 Rocq lines).
- unresolved_formalization_questions: none
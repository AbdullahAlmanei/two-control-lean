# Section 3 — Paper Packet

## Lemma 3.1

- paper_id: Lemma 3.1
- object_type: lemma
- section: 3
- source_pages: [213]
- paper_statement_summary: Suppose u0, u1 are unit complex numbers. A 3-qubit unitary U commutes with Diag(u0, u1) ⊗ I ⊗ I if and only if either u0 = u1 or U is of the form U = |0⟩⟨0| ⊗ V00 + |1⟩⟨1| ⊗ V11 where V00, V11 are 2-qubit unitaries.
- paper_dependencies: []
- rocq_files: []
- rocq_declarations: []
- rocq_helper_declarations: []
- rocq_notes:
- blueprint_label: lem:s3_1
- blueprint_uses: []
- lean_name: TwoControl.section3_lemma_3_1
- lean_file: TwoControl/Section3.lean
- statement_status: not_started
- proof_status: not_started
- extraction_confidence: high
- ambiguities: none

## Lemma 3.2

- paper_id: Lemma 3.2
- object_type: lemma
- section: 3
- source_pages: [213, 214]
- paper_statement_summary: Suppose u0, u1 are unit complex numbers. There exist 1-qubit unitaries P, Q such that Eigenvalues(P ⊗ Q) = [1, 1, u0, u1] if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies: [Theorem A.3, Lemma A.5]
- rocq_files: []
- rocq_declarations: []
- rocq_helper_declarations: []
- rocq_notes:
- blueprint_label: lem:s3_2
- blueprint_uses: []
- lean_name: TwoControl.section3_lemma_3_2
- lean_file: TwoControl/Section3.lean
- statement_status: not_started
- proof_status: not_started
- extraction_confidence: high
- ambiguities: none

## Lemma 3.3

- paper_id: Lemma 3.3
- object_type: lemma
- section: 3
- source_pages: [214, 215, 216]
- paper_statement_summary: Suppose u0, u1 are unit complex numbers. There exist a 1-qubit unitary P and complex numbers c, d such that Eigenvalues((I ⊗ P) C(Diag(u0, u1))) = [c, c, d, d] if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies: [Theorem A.3, Lemma A.1, Lemma A.6]
- rocq_files: []
- rocq_declarations: []
- rocq_helper_declarations: []
- rocq_notes:
- blueprint_label: lem:s3_3
- blueprint_uses: []
- lean_name: TwoControl.section3_lemma_3_3
- lean_file: TwoControl/Section3.lean
- statement_status: not_started
- proof_status: not_started
- extraction_confidence: high
- ambiguities: none
# Section 4 — Paper Packet

Extracted from: "Linear Algebra and its Applications 694 (2024) 206–261"
Section title: "4. Four key building blocks"

---

## Lemma 4.1

- paper_id: Lemma 4.1
- object_type: lemma
- section: 4
- source_pages: [216, 217]
- paper_statement_summary: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. There exist 2-qubit unitaries U, V and 1-qubit unitaries P0, P1, Q0, Q1 such that |0⟩⟨0| ⊗ U_BC (P0 ⊗ Q0) V_BC + |1⟩⟨1| ⊗ U_BC (P1 ⊗ Q1) V_BC = CC(Diag(u0, u1)) if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies: [Lemma A.4, Lemma 3.2]
- rocq_files: []
- rocq_declarations: []
- rocq_helper_declarations: []
- rocq_notes: (not extracted — paper extractor only)
- blueprint_label: lem:s4_1
- blueprint_uses: [lem:s3_2]
- lean_name: TwoControl.section4_lemma_4_1
- lean_file: TwoControl/Section4.lean
- statement_status: not_started
- proof_status: not_started
- extraction_confidence: high
- ambiguities: none

---

## Lemma 4.2

- paper_id: Lemma 4.2
- object_type: lemma
- section: 4
- source_pages: [217, 218]
- paper_statement_summary: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. Suppose Q is a 1-qubit unitary and let |β⟩ = Q|0⟩ and |β⊥⟩ = Q|1⟩. There exist 1-qubit unitaries P0, P1 such that I ⊗ I ⊗ |β⟩⟨β| + P0 ⊗ P1 ⊗ |β⊥⟩⟨β⊥| = CC(Diag(u0, u1)) if and only if u0 = 1 = u1.
- paper_dependencies: [Lemma A.8, Lemma 3.2]
- rocq_files: []
- rocq_declarations: []
- rocq_helper_declarations: []
- rocq_notes: (not extracted — paper extractor only)
- blueprint_label: lem:s4_2
- blueprint_uses: [lem:s3_2]
- lean_name: TwoControl.section4_lemma_4_2
- lean_file: TwoControl/Section4.lean
- statement_status: not_started
- proof_status: not_started
- extraction_confidence: high
- ambiguities: none

---

## Lemma 4.3

- paper_id: Lemma 4.3
- object_type: lemma
- section: 4
- source_pages: [219, 220, 221]
- paper_statement_summary: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. There exist 2-qubit unitaries V1, V2, V3, V4 and 1-qubit unitaries P0, P1, where V1 = |0⟩⟨0| ⊗ P0 + |1⟩⟨1| ⊗ P1, such that V1_AC V2_BC V3_AC V4_BC = CC(Diag(u0, u1)) if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies: [Lemma A.27, Lemma A.4, Theorem A.3, Lemma 3.3, Lemma A.11]
- rocq_files: []
- rocq_declarations: []
- rocq_helper_declarations: []
- rocq_notes: (not extracted — paper extractor only)
- blueprint_label: lem:s4_3
- blueprint_uses: [lem:s3_3]
- lean_name: TwoControl.section4_lemma_4_3
- lean_file: TwoControl/Section4.lean
- statement_status: not_started
- proof_status: not_started
- extraction_confidence: high
- ambiguities: none

---

## Lemma 4.4

- paper_id: Lemma 4.4
- object_type: lemma
- section: 4
- source_pages: [222]
- paper_statement_summary: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. There exist 2-qubit unitaries V1, V2, V3, V4 and 1-qubit unitaries P0, P1, where V4 = |0⟩⟨0| ⊗ P0 + |1⟩⟨1| ⊗ P1, such that V1_AC V2_BC V3_AC V4_BC = CC(Diag(u0, u1)) if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies: [Lemma 4.3]
- rocq_files: []
- rocq_declarations: []
- rocq_helper_declarations: []
- rocq_notes: (not extracted — paper extractor only)
- blueprint_label: lem:s4_4
- blueprint_uses: [lem:s4_3]
- lean_name: TwoControl.section4_lemma_4_4
- lean_file: TwoControl/Section4.lean
- statement_status: not_started
- proof_status: not_started
- extraction_confidence: high
- ambiguities: The paper states this "follows easily from Lemma 4.3 by exchanging the roles of A and B and considering the conjugate transpose of the product." No independent proof is given.
# Section 4 — Paper Packet

Extracted from: "Linear Algebra and its Applications 694 (2024) 206–261"
Section title: "4. Four key building blocks"

---

## Lemma 4.1

- paper_id: Lemma 4.1
- object_type: lemma
- section: 4
- source_pages: [216, 217]
- exact_statement_or_close_paraphrase: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. There exist 2-qubit unitaries U, V and 1-qubit unitaries P0, P1, Q0, Q1 such that |0⟩⟨0| ⊗ U(P0 ⊗ Q0)V + |1⟩⟨1| ⊗ U(P1 ⊗ Q1)V = CC(Diag(u0, u1)) if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies_explicit: [Lemma 3.2]
- paper_dependencies_implicit: [Lemma A.4]
- proof_sketch_summary: Forward direction: decompose CC(Diag(u0,u1)) via direct sum into I₄ and C(Diag(u0,u1)). The hypothesis forces U(P0⊗Q0)V = I₄ and U(P1⊗Q1)V = C(Diag(u0,u1)). Combining these yields Diag(1,1,u0,u1) = U((P1P0†)⊗(Q1Q0†))U†, which is a similarity relation on a tensor product of 1-qubit unitaries. Apply Lemma 3.2 to conclude u0 = u1 or u0 u1 = 1. Reverse direction: explicit constructions — if u0 = u1, use identity matrices; if u0 u1 = 1, use CNOT-based witnesses.
- extraction_confidence: high
- ambiguities: none

---

## Lemma 4.2

- paper_id: Lemma 4.2
- object_type: lemma
- section: 4
- source_pages: [217, 218]
- exact_statement_or_close_paraphrase: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. Suppose Q is a 1-qubit unitary and let |β⟩ = Q|0⟩ and |β⊥⟩ = Q|1⟩. There exist 1-qubit unitaries P0, P1 such that I ⊗ I ⊗ |β⟩⟨β| + P0 ⊗ P1 ⊗ |β⊥⟩⟨β⊥| = CC(Diag(u0, u1)) if and only if u0 = 1 and u1 = 1.
- paper_dependencies_explicit: [Lemma 3.2]
- paper_dependencies_implicit: [Lemma A.8]
- proof_sketch_summary: Forward direction: case-split on whether the components a, b of |β⟩ are zero. If a = 0 then |β⟩⟨β| = |1⟩⟨1| and |β⊥⟩⟨β⊥| = |0⟩⟨0|; extracting diagonal entries of the CC gate forces u0 = 1 and u1 = 1. Similarly if b = 0. If both are nonzero, multiply both sides by |1⟩⊗|1⟩⊗|β⟩; the |β⊥⟩ term vanishes by orthogonality, yielding |1⟩⊗|1⟩⊗|β⟩ = |1⟩⊗|1⟩⊗Diag(u0,u1)|β⟩, so Diag(u0,u1)|β⟩ = |β⟩, giving u0 = 1 and u1 = 1 by cancellation. Reverse direction: when u0 = u1 = 1, take P0 = P1 = I and use Lemma A.8 (Q|0⟩⟨0|Q† + Q|1⟩⟨1|Q† = I).
- extraction_confidence: high
- ambiguities: none

---

## Lemma 4.3

- paper_id: Lemma 4.3
- object_type: lemma
- section: 4
- source_pages: [219, 220, 221]
- exact_statement_or_close_paraphrase: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. There exist 2-qubit unitaries V1, V2, V3, V4 and 1-qubit unitaries P0, P1, where V1 = |0⟩⟨0| ⊗ P0 + |1⟩⟨1| ⊗ P1, such that V1_AC · V2_BC · V3_AC · V4_BC = CC(Diag(u0, u1)) if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies_explicit: [Lemma A.27, Theorem A.3, Lemma 3.3]
- paper_dependencies_implicit: [Lemma A.4, Lemma A.11]
- proof_sketch_summary: Forward direction: decompose CC(Diag(u0,u1)) as |0⟩⟨0|⊗I₄ + |1⟩⟨1|⊗C(Diag(u0,u1)). Since V1 is controlled on qubit A, apply Lemma A.27 to the alternating AC/BC product to extract 1-qubit unitaries Q0, Q1 such that the three-factor product V1·V2·V3 decomposes blockwise. Eliminate V4 to obtain (I⊗P1)V2(I⊗Q1) = C(Diag(u0,u1))·((I⊗P0)V2(I⊗Q0))†. This yields a similarity relation on a controlled unitary. Apply spectral decomposition (Theorem A.3) to Q1Q0† to obtain a diagonal matrix D, then invoke Lemma 3.3 on the resulting eigenvalue condition. Reverse direction: if u0 = u1, use V1 = I₄, V2 = swap, V3 = C(Diag(1,u1)), V4 = swap. If u0 u1 = 1, write u1 = e^{iθ}, set u = e^{iθ/2}, P = Diag(u⁻¹, u), and construct V1 = V3 = C(P) on AC, V2 = |0⟩⟨0|⊗σx + |1⟩⟨1|⊗I on BC, V4 = V2†.
- extraction_confidence: high
- ambiguities: none

---

## Lemma 4.4

- paper_id: Lemma 4.4
- object_type: lemma
- section: 4
- source_pages: [222]
- exact_statement_or_close_paraphrase: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. There exist 2-qubit unitaries V1, V2, V3, V4 and 1-qubit unitaries P0, P1, where V4 = |0⟩⟨0| ⊗ P0 + |1⟩⟨1| ⊗ P1, such that V1_AC · V2_BC · V3_AC · V4_BC = CC(Diag(u0, u1)) if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies_explicit: [Lemma 4.3]
- paper_dependencies_implicit: []
- proof_sketch_summary: Follows from Lemma 4.3 by exchanging the roles of A and B and taking the conjugate transpose of the entire product. Given a decomposition for CC(Diag(u0,u1)) with V1 controlled, take adjoints of all factors and reverse their order; the controlled structure migrates from V1 to V4. The condition u0 = u1 or u0 u1 = 1 is preserved under conjugation since |u0*| = |u0| and u0* u1* = (u0 u1)*.
- extraction_confidence: high
- ambiguities: The paper states this "follows easily from Lemma 4.3 by exchanging the roles of A and B and considering the conjugate transpose of the product." No independent proof is given.

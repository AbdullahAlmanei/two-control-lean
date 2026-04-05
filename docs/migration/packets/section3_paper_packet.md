# Section 3 — Paper Packet

## Lemma 3.1

- paper_id: Lemma 3.1
- object_type: lemma
- section: 3
- source_pages: [213]
- exact_statement_or_close_paraphrase: Suppose u₀, u₁ are complex numbers with |u₀| = |u₁| = 1. An 8×8 unitary U commutes with Diag(u₀, u₁) ⊗ I₂ ⊗ I₂ if and only if either u₀ = u₁ or U = |0⟩⟨0| ⊗ V₀₀ + |1⟩⟨1| ⊗ V₁₁ for some 4×4 unitaries V₀₀, V₁₁.
- paper_dependencies_explicit: none
- paper_dependencies_implicit: none
- proof_sketch_summary: Decompose U into a 2×2 block matrix of 4×4 submatrices via |0⟩⟨0| ⊗ V₀₀ + |0⟩⟨1| ⊗ V₀₁ + |1⟩⟨0| ⊗ V₁₀ + |1⟩⟨1| ⊗ V₁₁. Similarly decompose Diag(u₀, u₁) ⊗ I₂ ⊗ I₂ as a block-diagonal matrix with blocks u₀·I₄ and u₁·I₄. Compute UW and WU and compare blocks: commutativity forces u₁·V₀₁ = u₀·V₀₁ and u₀·V₁₀ = u₁·V₁₀. When u₀ ≠ u₁, this implies V₀₁ = V₁₀ = 0, giving the block-diagonal form. Unitarity of U then forces V₀₀ and V₁₁ to be individually unitary. The converse is straightforward.
- extraction_confidence: high
- ambiguities: none

## Lemma 3.2

- paper_id: Lemma 3.2
- object_type: lemma
- section: 3
- source_pages: [213, 214]
- exact_statement_or_close_paraphrase: Suppose u₀, u₁ are complex numbers with |u₀| = |u₁| = 1. There exist 2×2 unitaries P, Q such that the eigenvalues of P ⊗ Q are {1, 1, u₀, u₁} (as a multiset, up to permutation) if and only if either u₀ = u₁ or u₀u₁ = 1.
- paper_dependencies_explicit: [Theorem A.3, Lemma A.5]
- paper_dependencies_implicit: none
- proof_sketch_summary: (Forward direction) Diagonalize P and Q via the spectral theorem (Theorem A.3) to write P = Vₚ Dₚ Vₚ† and Q = V_Q D_Q V_Q†. The eigenvalues of P ⊗ Q are the pairwise products of eigenvalues of P and Q (by Lemma A.5). These four products must be a permutation of {1, 1, u₀, u₁}. Exhaustive case analysis over all 24 permutations of four elements shows each case yields either u₀ = u₁ or u₀u₁ = 1. (Backward direction) If u₀ = u₁, take P = Diag(1, u₁) and Q = I₂. If u₀u₁ = 1, take P = Diag(1, u₀) and Q = Diag(1, u₁) with suitable diagonalizing unitary (the NOT gate).
- extraction_confidence: high
- ambiguities: none

## Lemma 3.3

- paper_id: Lemma 3.3
- object_type: lemma
- section: 3
- source_pages: [214, 215, 216]
- exact_statement_or_close_paraphrase: Suppose u₀, u₁ are complex numbers with |u₀| = |u₁| = 1. There exist a 2×2 unitary P and complex numbers c, d such that the eigenvalues of (I₂ ⊗ P) · C(Diag(u₀, u₁)) are {c, c, d, d} (each with multiplicity two) if and only if either u₀ = u₁ or u₀u₁ = 1. Here C(Diag(u₀, u₁)) denotes the controlled-Diag(u₀, u₁) gate.
- paper_dependencies_explicit: [Theorem A.3, Lemma A.1, Lemma A.6]
- paper_dependencies_implicit: none
- proof_sketch_summary: (Forward direction) Rewrite (I₂ ⊗ P) · C(Diag(u₀, u₁)) as the direct sum P ⊕ (P · Diag(u₀, u₁)). Diagonalize P and P · Diag(u₀, u₁) separately via the spectral theorem (Theorem A.3). Apply Lemma A.6 to relate the eigenvalues of the direct sum to those of the combined diagonal form {c, c, d, d}. Exhaustive case analysis on all permutations of four eigenvalues: if both eigenvalues of P equal the same value c, then P is a scalar multiple of the identity, and a cancellation argument forces u₀ = u₁. In the remaining cases, a determinant argument using Lemma A.1 (det(AB) = det(A)·det(B)) yields u₀u₁ = 1. (Backward direction) Explicit constructions for each case.
- extraction_confidence: high
- ambiguities: none

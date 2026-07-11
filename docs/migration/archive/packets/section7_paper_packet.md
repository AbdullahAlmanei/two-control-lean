# Section 7 — Paper Packet

## Lemma 7.1

- paper_id: Lemma 7.1
- object_type: lemma
- section: 7
- source_pages: [230]
- exact_statement_or_close_paraphrase: (Change a diagonal element to one.) Suppose u₀, u₁ are complex numbers such that |u₀| = |u₁| = 1. For a 2-qubit unitary W and a 3-qubit unitary U, if CC(Diag(u₀, u₁)) = W_AB · U, then there exists a 2-qubit unitary V such that CC(Diag(1, u₀*u₁)) = V_AB · U.
- paper_dependencies_explicit: none
- paper_dependencies_implicit: none
- proof_sketch_summary: Define V = C(Diag(1, u₀*)) · W. Compute V_AB · U by expanding as (C(Diag(1, u₀*)) ⊗ I_C)(W_AB ⊗ I_C) · U = (C(Diag(1, u₀*)) ⊗ I_C) · CC(Diag(u₀, u₁)). Multiply the two 8×8 diagonal matrices to get Diag(1,1,1,1,1,1,1, u₀*u₁) = CC(Diag(1, u₀*u₁)).
- extraction_confidence: high
- ambiguities: none

## Lemma 7.2

- paper_id: Lemma 7.2
- object_type: lemma
- section: 7
- source_pages: [230, 231, 232, 233, 234, 235]
- exact_statement_or_close_paraphrase: (Reduction.) Suppose u₀, u₁ are complex numbers such that |u₀| = |u₁| = 1. If there exists a product of at most four elements of G₂ \ G₁ and any number of elements of G₁ that is equal to CC(Diag(u₀, u₁)), then either (1) there exist 2-qubit unitaries U₁, U₂, U₃, U₄ and complex numbers u₂, u₃ such that (u₂, u₃) ∈ R(u₀, u₁) and U₁_BC · U₂_AC · U₃_AB · U₄_BC = CC(Diag(u₂, u₃)), or (2) there exist 2-qubit unitaries U₁, U₂, U₃, U₄ and complex numbers u₂, u₃ such that (u₂, u₃) ∈ R(u₀, u₁) and U₁_AC · U₂_BC · U₃_AC · U₄_BC = CC(Diag(u₂, u₃)).
- paper_dependencies_explicit: [Lemma 7.1, Lemma A.12, Lemma A.13]
- paper_dependencies_implicit: none
- proof_sketch_summary: Four steps. Step 1: Transform the given product E to a product E₂ of at most four elements of G₂ equal to CC(Diag(u₀, u₁)), by absorbing and condensing G₁ factors; five cases depending on which subsets (G_AB, G_AC, G_BC) the G₂ \ G₁ factors belong to. Step 2: Transform E₂ to a canonical product E₄ of exactly four elements of G₂ by combining adjacent factors on the same qubit pair and padding with identity matrices. Step 3: Transform E₄ to a canonical product E₆ of four elements of G₂ whose last factor is in G_BC, with (u₆, u₇) ∈ R(u₀, u₁) and E₆ = CC(Diag(u₆, u₇)); three cases based on the last factor's qubit pair (AB, AC, BC), using Lemma 7.1 and qubit swaps S_AC or S_AB via Lemma A.12 and Lemma A.13. Step 4: Transform E₆ to one of the two required canonical forms; eight cases covering all canonical orderings ending in BC, using Lemma 7.1, Lemma A.12, Lemma A.13, and qubit swaps.
- extraction_confidence: high
- ambiguities: The paper introduces the notion of a "canonical" product and the set R(u₀, u₁) as inline (unnumbered) definitions at the start of Section 7. These are not given formal paper-numbered labels but are used throughout Lemma 7.2 and later objects.

## Lemma 7.3

- paper_id: Lemma 7.3
- object_type: lemma
- section: 7
- source_pages: [235, 236]
- exact_statement_or_close_paraphrase: Suppose u₀, u₁ are complex numbers such that |u₀| = |u₁| = 1. Suppose also that (u₂, u₃) ∈ R(u₀, u₁). If (u₂ = u₃ or u₂u₃ = 1), then (u₀ = u₁ or u₀u₁ = 1).
- paper_dependencies_explicit: none
- paper_dependencies_implicit: none
- proof_sketch_summary: Case analysis on which member of R(u₀, u₁) equals (u₂, u₃). If (u₂, u₃) = (u₀, u₁) and u₂ = u₃, then u₀ = u₁. If (u₂, u₃) = (u₀, u₁) and u₂u₃ = 1, then u₀u₁ = 1. If (u₂, u₃) = (1, u₀*u₁) and u₂ = u₃, then 1 = u₀*u₁, so u₀ = u₁. If (u₂, u₃) = (1, u₀*u₁) and u₂u₃ = 1, then u₀*u₁ = 1, so u₀ = u₁. All four subcases yield the conclusion.
- extraction_confidence: high
- ambiguities: none

## Theorem 7.4

- paper_id: Theorem 7.4
- object_type: theorem
- section: 7
- source_pages: [236]
- exact_statement_or_close_paraphrase: (Main result for a diagonal matrix.) Suppose u₀, u₁ are complex numbers such that |u₀| = |u₁| = 1. There exists a product of at most four elements of G₂ \ G₁ and any number of elements of G₁ that is equal to CC(Diag(u₀, u₁)) if and only if either u₀ = u₁ or u₀u₁ = 1.
- paper_dependencies_explicit: [Lemma 7.2, Lemma 5.1, Lemma 6.4, Lemma 7.3]
- paper_dependencies_implicit: none
- proof_sketch_summary: Left-to-right: By Lemma 7.2, reduce to one of two canonical forms. Apply Lemma 5.1 to the first canonical form and Lemma 6.4 to the second; in both cases obtain u₂ = u₃ or u₂u₃ = 1. Since (u₂, u₃) ∈ R(u₀, u₁), Lemma 7.3 gives u₀ = u₁ or u₀u₁ = 1. Right-to-left: follows from Lemma 5.1.
- extraction_confidence: high
- ambiguities: none

## Corollary 7.5

- paper_id: Corollary 7.5
- object_type: corollary
- section: 7
- source_pages: [236, 237]
- exact_statement_or_close_paraphrase: (Main result for a gate with two controls.) For a 1-qubit unitary U, there exists a product of at most four elements of G₂ \ G₁ and any number of elements of G₁ that is equal to CC(U) if and only if either the eigenvalues of U are equal or det(U) = 1.
- paper_dependencies_explicit: [Theorem 7.4, Theorem A.3]
- paper_dependencies_implicit: none
- proof_sketch_summary: Use the Spectral Theorem A.3 to write U = V · Diag(u₀, u₁) · V†. Then CC(Diag(u₀, u₁)) = (I_A ⊗ I_B ⊗ V†) · CC(U) · (I_A ⊗ I_B ⊗ V). Since (I_A ⊗ I_B ⊗ V†) and (I_A ⊗ I_B ⊗ V) are elements of G₁, the number of G₂ \ G₁ elements needed to implement CC(U) equals the number needed for CC(Diag(u₀, u₁)). Apply Theorem 7.4. Translate: det(U) = u₀u₁, so "u₀ = u₁ or u₀u₁ = 1" becomes "eigenvalues equal or det(U) = 1".
- extraction_confidence: high
- ambiguities: none

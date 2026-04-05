# Section 3 — Reconciled Packet

Merged from:
- section3_paper_packet.md
- section3_rocq_packet.md

## Lemma 3.1

- paper_id: Lemma 3.1
- object_type: lemma
- section: 3
- source_pages: [213]
- paper_statement_summary: Suppose u₀, u₁ are complex numbers with |u₀| = |u₁| = 1. An 8×8 unitary U commutes with Diag(u₀, u₁) ⊗ I₂ ⊗ I₂ if and only if either u₀ = u₁ or U = |0⟩⟨0| ⊗ V₀₀ + |1⟩⟨1| ⊗ V₁₁ for some 4×4 unitaries V₀₀, V₁₁.
- paper_dependencies_explicit: none
- paper_dependencies_implicit: none
- matched_rocq_primary_declaration: m3_1 (Lemma, Main.v:24)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: none
- matched_rocq_helper_declarations: [block_decomp (Lemma, Helpers/MatrixHelpers.v:900), block_multiply (Lemma, Helpers/MatrixHelpers.v:349), block_equalities (Lemma, Helpers/MatrixHelpers.v:377), diag2_decomp (Lemma, Helpers/MatrixHelpers.v:73), Mscale_cancel_l (Lemma, Helpers/MatrixHelpers.v:269), adjoint00 (Lemma, Helpers/MatrixHelpers.v:1175), adjoint01 (Lemma, Helpers/MatrixHelpers.v:1176), adjoint10 (Lemma, Helpers/MatrixHelpers.v:1177), adjoint11 (Lemma, Helpers/MatrixHelpers.v:1178)]
- matched_rocq_definitions_used: [diag2 (QuantumLib), control (QuantumLib)]
- reconciliation_notes: Paper and Rocq match exactly. Rocq uses diag2 u0 u1 ⊗ I 2 ⊗ I 2 for the paper's Diag(u₀, u₁) ⊗ I₂ ⊗ I₂. Proof strategy is identical: block decomposition, commutativity comparison, scalar cancellation for off-diagonal blocks, unitarity recovery. No appendix lemmas needed; only local MatrixHelpers block-algebra infrastructure.
- dependency_divergence_notes: none
- reconciliation_confidence: high
- ambiguities: none

## Lemma 3.2

- paper_id: Lemma 3.2
- object_type: lemma
- section: 3
- source_pages: [213, 214]
- paper_statement_summary: Suppose u₀, u₁ are complex numbers with |u₀| = |u₁| = 1. There exist 2×2 unitaries P, Q such that the eigenvalues of P ⊗ Q are {1, 1, u₀, u₁} (as a multiset, up to permutation) if and only if either u₀ = u₁ or u₀u₁ = 1.
- paper_dependencies_explicit: [Theorem A.3, Lemma A.5]
- paper_dependencies_implicit: none
- matched_rocq_primary_declaration: m3_2 (Lemma, Main.v:272)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: none
- matched_rocq_helper_declarations: [a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10), perm_eigenvalues (Lemma, Helpers/Permutations.v:252), permutation_4_decomp (Lemma, Helpers/Permutations.v:311), Diag_diag4 (Lemma, Helpers/DiagonalHelpers.v:25), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46), Det_diag2 (Lemma, Helpers/MatrixHelpers.v:79)]
- matched_rocq_definitions_used: [diag2 (QuantumLib), diag4 (Helpers/MatrixHelpers.v:49), notc (QuantumLib)]
- reconciliation_notes: Paper and Rocq match on the mathematical content. Rocq formalises the eigenvalue condition as ∃ P Q V, WF_Unitary P ∧ WF_Unitary Q ∧ WF_Unitary V ∧ P ⊗ Q = V × diag4 1 1 u0 u1 × V† (explicit diagonalisation) rather than a direct eigenvalue-multiset statement. Proof structure is the same: spectral decomposition, 24-permutation case analysis, algebraic conclusion.
- dependency_divergence_notes: Paper cites Lemma A.5 (eigenvalues of a tensor product are pairwise products of eigenvalues). No separate Rocq declaration a5 exists; its content is absorbed into the perm_eigenvalues + diag_kron (QuantumLib) argument. Theorem A.3 maps to a3 directly.
- reconciliation_confidence: high
- ambiguities: none

## Lemma 3.3

- paper_id: Lemma 3.3
- object_type: lemma
- section: 3
- source_pages: [214, 215, 216]
- paper_statement_summary: Suppose u₀, u₁ are complex numbers with |u₀| = |u₁| = 1. There exist a 2×2 unitary P and complex numbers c, d such that the eigenvalues of (I₂ ⊗ P) · C(Diag(u₀, u₁)) are {c, c, d, d} (each with multiplicity two) if and only if either u₀ = u₁ or u₀u₁ = 1. Here C(Diag(u₀, u₁)) denotes the controlled-Diag(u₀, u₁) gate.
- paper_dependencies_explicit: [Theorem A.3, Lemma A.1, Lemma A.6]
- paper_dependencies_implicit: none
- matched_rocq_primary_declaration: m3_3 (Lemma, Main.v:504)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: none
- matched_rocq_helper_declarations: [a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10), a1 (Lemma, Appendix/A1_SquareMatrices.v:6), a6 (Lemma, Appendix/A2_UnitaryMatrices.v:76), control_decomp (Lemma, Helpers/MatrixHelpers.v:2078), permutation_4_decomp (Lemma, Helpers/Permutations.v:311), Diag_diag4 (Lemma, Helpers/DiagonalHelpers.v:25), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46), Det_diag2 (Lemma, Helpers/MatrixHelpers.v:79)]
- matched_rocq_definitions_used: [diag2 (QuantumLib), diag4 (Helpers/MatrixHelpers.v:49), control (QuantumLib), direct_sum (QuantumLib), swap (QuantumLib), cnot (QuantumLib)]
- reconciliation_notes: Paper and Rocq match on the mathematical content. Rocq formalises the eigenvalue condition as ∃ P U c d, WF_Unitary P ∧ WF_Unitary U ∧ (I 2 ⊗ P) × control (diag2 u0 u1) = U × diag4 c d c d × U†. Proof strategy matches the paper: rewrite as direct sum P ⊕ (P·Diag(u₀,u₁)), spectral decompose both summands, apply a6 for eigenvalue permutation, exhaustive 24-case analysis. Three internal case lemmas (case_A, case_B, case_C) implement the paper's two proof branches (scalar identity vs. determinant argument). Reverse direction constructs P = I₂ (with swap) when u₀ = u₁ and P = diag2 1 u₀ (with cnot) when u₀u₁ = 1. This is the longest Section 3 proof (~500 lines).
- dependency_divergence_notes: All three paper dependencies map directly to Rocq declarations: Theorem A.3 → a3, Lemma A.1 → a1, Lemma A.6 → a6. No divergences.
- reconciliation_confidence: high
- ambiguities: none
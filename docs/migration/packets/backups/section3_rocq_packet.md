# Section 3 — Rocq Packet

## Lemma 3.1

- paper_id: Lemma 3.1
- object_type: lemma
- section: 3
- source_pages: [213]
- paper_statement_summary: Suppose u0, u1 are unit complex numbers. A 3-qubit unitary U commutes with Diag(u0, u1) ⊗ I ⊗ I if and only if either u0 = u1 or U is of the form U = |0⟩⟨0| ⊗ V00 + |1⟩⟨1| ⊗ V11 where V00, V11 are 2-qubit unitaries.
- paper_dependencies: []
- rocq_files: [Main.v]
- rocq_declarations: [m3_1 (Lemma, Main.v:24)]
- rocq_helper_declarations: [block_decomp (Lemma, Helpers/MatrixHelpers.v:900), block_multiply (Lemma, Helpers/MatrixHelpers.v:349), block_equalities (Lemma, Helpers/MatrixHelpers.v:377), diag2_decomp (Lemma, Helpers/MatrixHelpers.v:73)]
- rocq_notes: Rocq statement uses diag2 u0 u1 ⊗ I 2 ⊗ I 2 for the 8×8 diagonal. Proof decomposes U into four blocks via block_decomp, shows off-diagonal blocks are Zero using commutativity, then recovers unitarity of V00, V11 from U† × U = I. Reverse direction verified by direct block multiplication. No appendix lemmas needed; only local MatrixHelpers block-algebra infrastructure.
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
- rocq_files: [Main.v]
- rocq_declarations: [m3_2 (Lemma, Main.v:272)]
- rocq_helper_declarations: [a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10), perm_eigenvalues (Lemma, Helpers/Permutations.v:252), permutation_4_decomp (Lemma, Helpers/Permutations.v:311), diag_kron (QuantumLib — not locally defined), Diag_diag4 (Lemma, Helpers/DiagonalHelpers.v:25), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46)]
- rocq_notes: Rocq formalises the eigenvalue condition as ∃ P Q V, WF_Unitary P ∧ WF_Unitary Q ∧ WF_Unitary V ∧ P ⊗ Q = V × diag4 1 1 u0 u1 × V†. This expresses "Eigenvalues(P⊗Q) = {1,1,u0,u1}" via explicit diagonalisation. Forward direction spectral-decomposes P and Q via Theorem A.3 (a3), forms a combined diagonalisation V†×(VP⊗VQ), then uses perm_eigenvalues + permutation_4_decomp to case-split all 24 permutations and derive u0=u1 or u0·u1=1. Reverse direction constructs explicit P = diag2 1 u0, Q = diag2 1 u1 (or similar) as diagonal unitaries. Paper's reference to "Lemma A.5" is not present as a separate Rocq declaration; its content is absorbed into the permutation argument. diag_kron is a QuantumLib lemma used to establish WF_Diagonal (DP ⊗ DQ).
- blueprint_label: lem:s3_2
- blueprint_uses: []
- lean_name: TwoControl.section3_lemma_3_2
- lean_file: TwoControl/Section3.lean
- statement_status: not_started
- proof_status: not_started
- extraction_confidence: high
- ambiguities: Paper cites Lemma A.5 but no separate Rocq declaration named a5 is used in m3_2; functionality appears folded into the perm_eigenvalues + permutation_4_decomp argument.

## Lemma 3.3

- paper_id: Lemma 3.3
- object_type: lemma
- section: 3
- source_pages: [214, 215, 216]
- paper_statement_summary: Suppose u0, u1 are unit complex numbers. There exist a 1-qubit unitary P and complex numbers c, d such that Eigenvalues((I ⊗ P) C(Diag(u0, u1))) = [c, c, d, d] if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies: [Theorem A.3, Lemma A.1, Lemma A.6]
- rocq_files: [Main.v]
- rocq_declarations: [m3_3 (Lemma, Main.v:504)]
- rocq_helper_declarations: [a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10), a1 (Lemma, Appendix/A1_SquareMatrices.v:6), a6 (Lemma, Appendix/A2_UnitaryMatrices.v:76), control_decomp (Lemma, Helpers/MatrixHelpers.v:2078), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46), Diag_diag4 (Lemma, Helpers/DiagonalHelpers.v:25), permutation_4_decomp (Lemma, Helpers/Permutations.v:311)]
- rocq_notes: Rocq formalises the eigenvalue condition as ∃ P U c d, WF_Unitary P ∧ WF_Unitary U ∧ (I 2 ⊗ P) × control (diag2 u0 u1) = U × diag4 c d c d × U†. The controlled gate is decomposed via control_decomp into |0⟩⟨0|⊗I .+ |1⟩⟨1|⊗(diag2 u0 u1). Forward direction: form PD = P × diag2 u0 u1, spectral-decompose both P and PD via a3, then apply a6 (eigenvalue matching under direct-sum diagonalisation) to get a permutation σ. The repeated-eigenvalue constraint diag4 c d c d forces specific pairing; determinant arguments using a1 (det(AB)=det(A)·det(B)) constrain possibilities, yielding u0=u1 or u0·u1=1. The proof case-splits all 24 permutations via permutation_4_decomp. Reverse direction constructs P = I 2 when u0 = u1, and P = σx (Pauli-X) when u0·u1 = 1, then verifies by direct computation. This is the longest Section 3 proof (~500 lines).
- blueprint_label: lem:s3_3
- blueprint_uses: []
- lean_name: TwoControl.section3_lemma_3_3
- lean_file: TwoControl/Section3.lean
- statement_status: not_started
- proof_status: not_started
- extraction_confidence: high
- ambiguities: none

## Rocq-only helper notes

### Block-algebra infrastructure (Helpers/MatrixHelpers.v)
- block_decomp (line 900): Decomposes any 2n×2n matrix into four n×n blocks via |0⟩⟨0|⊗TL .+ |0⟩⟨1|⊗TR .+ |1⟩⟨0|⊗BL .+ |1⟩⟨1|⊗BR. Used by m3_1.
- block_multiply (line 349): Multiplies two block-decomposed matrices, yielding block products. Used by m3_1.
- block_equalities (line 377): Extracts component-wise equalities from matching block decompositions. Used by m3_1.
- diag2_decomp (line 73): Rewrites diag2 c1 c2 as c1 .* |0⟩⟨0| .+ c2 .* |1⟩⟨1|. Used by m3_1.
- control_decomp (line 2078): Rewrites control A as |0⟩⟨0| ⊗ I n .+ |1⟩⟨1| ⊗ A. Used by m3_3.

### Eigenvalue/permutation infrastructure (Helpers/Permutations.v)
- perm_eigenvalues (line 252): If U×D×U† = D' with D,D' diagonal and U unitary, then diagonal entries of D are a permutation of those of D'. Used by m3_2.
- permutation_4_decomp (line 311): Enumerates all 24 permutations of {0,1,2,3}. Used by m3_2 and m3_3.

### Diagonal helpers (Helpers/DiagonalHelpers.v)
- Diag_diag4 (line 25): Establishes WF_Diagonal (diag4 c1 c2 c3 c4). Used by m3_2 and m3_3.

### Unitary helpers (Helpers/UnitaryHelpers.v)
- diag2_unitary (line 46): diag2 c1 c2 is unitary when Cmod c1 = 1 and Cmod c2 = 1. Used by m3_2 and m3_3.

### Appendix declarations
- a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10): Spectral theorem — every unitary has a diagonalisation U = V×D×V† with V unitary and D diagonal. Used by m3_2 and m3_3.
- a1 (Lemma, Appendix/A1_SquareMatrices.v:6): Determinant is multiplicative: det(D×E) = det(D)·det(E). Used by m3_3.
- a6 (Lemma, Appendix/A2_UnitaryMatrices.v:76): If P = VP×DP×VP† and Q = VQ×DQ×VQ† and P⊕Q = V×D×V† then diagonal entries of DP⊕DQ are a permutation of D. Used by m3_3.

### QuantumLib dependencies (not locally defined)
- diag_kron: WF_Diagonal (D ⊗ E) when D,E are WF_Diagonal. Used by m3_2.
- direct_sum_decomp: Decomposes direct sum into block form. Used internally by control_decomp.
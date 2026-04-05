# Section 3 — Rocq Packet

## Lemma 3.1

- paper_id_or_best_match: Lemma 3.1
- rocq_primary_declaration: m3_1 (Lemma, Main.v:24)
- rocq_primary_file: Main.v
- rocq_supporting_files: Helpers/MatrixHelpers.v
- rocq_direct_dependencies: none
- rocq_helper_declarations: [block_decomp (Lemma, Helpers/MatrixHelpers.v:900), block_multiply (Lemma, Helpers/MatrixHelpers.v:349), block_equalities (Lemma, Helpers/MatrixHelpers.v:377), diag2_decomp (Lemma, Helpers/MatrixHelpers.v:73), Mscale_cancel_l (Lemma, Helpers/MatrixHelpers.v:269), adjoint00 (Lemma, Helpers/MatrixHelpers.v:1175), adjoint01 (Lemma, Helpers/MatrixHelpers.v:1176), adjoint10 (Lemma, Helpers/MatrixHelpers.v:1177), adjoint11 (Lemma, Helpers/MatrixHelpers.v:1178)]
- rocq_definitions_used: [diag2 (QuantumLib), control (QuantumLib)]
- rocq_external_library_items: [QuantumLib.Matrix, QuantumLib.Quantum]
- rocq_proof_strategy_summary: Decompose U into four 4×4 blocks via block_decomp. Decompose diag2 u0 u1 ⊗ I 2 ⊗ I 2 into block-diagonal form with blocks u0·I4 and u1·I4 via diag2_decomp. Compute both products UW and WU using block_multiply. Extract component-wise equalities via block_equalities: commutativity forces u1·V01 = u0·V01 and u0·V10 = u1·V10. When u0 ≠ u1, a scalar cancellation argument (Mscale_cancel_l) shows V01 = V10 = Zero, yielding the block-diagonal form. Unitarity of V00 and V11 is recovered from U†×U = I using block_equalities again. Reverse direction verified by direct block multiplication. ~250 lines.
- rocq_match_confidence: high
- ambiguities: none

---

## Lemma 3.2

- paper_id_or_best_match: Lemma 3.2
- rocq_primary_declaration: m3_2 (Lemma, Main.v:272)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Appendix/A2_UnitaryMatrices.v, Helpers/Permutations.v, Helpers/DiagonalHelpers.v, Helpers/UnitaryHelpers.v]
- rocq_direct_dependencies: none
- rocq_helper_declarations: [a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10), perm_eigenvalues (Lemma, Helpers/Permutations.v:252), permutation_4_decomp (Lemma, Helpers/Permutations.v:311), Diag_diag4 (Lemma, Helpers/DiagonalHelpers.v:25), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46), Det_diag2 (Lemma, Helpers/MatrixHelpers.v:79)]
- rocq_definitions_used: [diag2 (QuantumLib), diag4 (Helpers/MatrixHelpers.v:49), notc (QuantumLib)]
- rocq_external_library_items: [QuantumLib.Matrix, QuantumLib.Quantum, QuantumLib.Eigenvectors, QuantumLib.Permutations]
- rocq_proof_strategy_summary: Formalises eigenvalue condition as ∃ P Q V, WF_Unitary P ∧ WF_Unitary Q ∧ WF_Unitary V ∧ P ⊗ Q = V × diag4 1 1 u0 u1 × V†. Forward direction: spectral-decompose P and Q via a3, form combined diagonalisation V†×(VP⊗VQ), use perm_eigenvalues to establish that diagonal entries of DP⊗DQ are a permutation of {1,1,u0,u1}, then exhaustive case analysis via permutation_4_decomp over all 24 permutations. Each case reduces to either u0=u1 (case_A) or u0·u1=1 (case_B) by algebraic manipulation of eigenvalue products. Reverse direction: if u0=u1, take P=diag2 1 u1, Q=I2; if u0·u1=1, take P=diag2 1 u0, Q=diag2 1 u1 with diagonalising unitary notc (NOT gate). ~230 lines.
- rocq_match_confidence: high
- ambiguities: Paper cites Lemma A.5 (eigenvalues of tensor products) but no separate Rocq declaration named a5 exists; its content is absorbed into the perm_eigenvalues + kron of diagonal matrices argument. diag_kron from QuantumLib establishes WF_Diagonal for the Kronecker product of diagonals.

---

## Lemma 3.3

- paper_id_or_best_match: Lemma 3.3
- rocq_primary_declaration: m3_3 (Lemma, Main.v:504)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Appendix/A1_SquareMatrices.v, Appendix/A2_UnitaryMatrices.v, Helpers/Permutations.v, Helpers/DiagonalHelpers.v, Helpers/UnitaryHelpers.v, Helpers/MatrixHelpers.v]
- rocq_direct_dependencies: none
- rocq_helper_declarations: [a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10), a1 (Lemma, Appendix/A1_SquareMatrices.v:6), a6 (Lemma, Appendix/A2_UnitaryMatrices.v:76), control_decomp (Lemma, Helpers/MatrixHelpers.v:2078), permutation_4_decomp (Lemma, Helpers/Permutations.v:311), Diag_diag4 (Lemma, Helpers/DiagonalHelpers.v:25), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46), Det_diag2 (Lemma, Helpers/MatrixHelpers.v:79)]
- rocq_definitions_used: [diag2 (QuantumLib), diag4 (Helpers/MatrixHelpers.v:49), control (QuantumLib), direct_sum (QuantumLib), swap (QuantumLib), cnot (QuantumLib)]
- rocq_external_library_items: [QuantumLib.Matrix, QuantumLib.Quantum, QuantumLib.Eigenvectors, QuantumLib.Permutations]
- rocq_proof_strategy_summary: Formalises eigenvalue condition as ∃ P U c d, WF_Unitary P ∧ WF_Unitary U ∧ (I 2 ⊗ P) × control (diag2 u0 u1) = U × diag4 c d c d × U†. Forward direction: rewrite (I 2 ⊗ P) × control (diag2 u0 u1) as P ⊕ PD where PD = P × diag2 u0 u1 via control_decomp and direct_sum_decomp. Spectral-decompose both P and PD via a3. Apply a6 to obtain a permutation σ relating eigenvalues of DP⊕DPD to those of diag4 c d c d. Exhaustive case analysis over all 24 permutations via permutation_4_decomp. Three internal case lemmas: case_A (both eigenvalues of P equal c → P is scalar → cancellation forces u0=u1), case_B (eigenvalues in same order → determinant argument via a1 yields u0·u1=1), case_C (eigenvalues cross → determinant argument via a1 yields u0·u1=1). Each uses unit_det_neq_0 (QuantumLib) and Cmult_cancel_l (QuantumLib) for algebraic reasoning. Reverse direction: if u0=u1, take P=I2 with diagonalising unitary swap; if u0·u1=1, take P=diag2 1 u0 with diagonalising unitary cnot. ~500 lines, the longest Section 3 proof.
- rocq_match_confidence: high
- ambiguities: none

---

## Rocq-only helper notes

### Block-algebra infrastructure (Helpers/MatrixHelpers.v)
- block_decomp (line 900): Decomposes any 2n×2n WF_Matrix into four n×n blocks via |0⟩⟨0|⊗V00 .+ |0⟩⟨1|⊗V01 .+ |1⟩⟨0|⊗V10 .+ |1⟩⟨1|⊗V11. Used by m3_1.
- block_multiply (line 349): Computes the product of two block-decomposed matrices as a block matrix. Used by m3_1.
- block_equalities (line 377): Extracts component-wise equalities from two equal block decompositions. Used by m3_1.
- diag2_decomp (line 73): Rewrites diag2 c1 c2 as c1 .* |0⟩⟨0| .+ c2 .* |1⟩⟨1|. Used by m3_1.
- control_decomp (line 2078): Rewrites control A as |0⟩⟨0| ⊗ I n .+ |1⟩⟨1| ⊗ A. Used by m3_3.
- Mscale_cancel_l (line 269): If c ≠ 0 and c .* A = c .* B then A = B. Used by m3_1.
- Det_diag2 (line 79): det(diag2 c1 c2) = c1 * c2. Used by m3_2 and m3_3.

### Eigenvalue/permutation infrastructure (Helpers/Permutations.v)
- perm_eigenvalues (line 252): If U×D×U† = D' with D, D' diagonal and U unitary, then diagonal entries of D are a permutation of those of D'. Used by m3_2.
- permutation_4_decomp (line 311): Enumerates all 24 permutations of {0,1,2,3} as a disjunction. Used by m3_2 and m3_3; drives the exhaustive case analysis.

### Diagonal helpers (Helpers/DiagonalHelpers.v)
- Diag_diag4 (line 25): Establishes WF_Diagonal (diag4 c1 c2 c3 c4). Used by m3_2 and m3_3.

### Unitary helpers (Helpers/UnitaryHelpers.v)
- diag2_unitary (line 46): diag2 c1 c2 is unitary when Cmod c1 = 1 and Cmod c2 = 1. Used by m3_2 and m3_3 reverse directions.

### Appendix declarations
- a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10): Spectral theorem — every unitary has a diagonalisation U = V×D×V† with V unitary and D diagonal. Used by m3_2 and m3_3.
- a1 (Lemma, Appendix/A1_SquareMatrices.v:6): det(D×E) = det(D)·det(E). Used by m3_3 determinant arguments.
- a6 (Lemma, Appendix/A2_UnitaryMatrices.v:76): If P⊕Q has two diagonalisations, their eigenvalues are related by a permutation. Used by m3_3.

### QuantumLib items used (not locally defined)
- diag_kron: WF_Diagonal (D ⊗ E) when D, E are WF_Diagonal. Used by m3_2.
- swap, swap_unitary: The 4×4 SWAP gate and its unitarity. Used by m3_3 reverse direction.
- cnot, cnot_unitary: The CNOT gate and its unitarity. Used by m3_3 reverse direction.
- notc, notc_unitary: The NOT-controlled (reverse CNOT) gate and its unitarity. Used by m3_2 reverse direction.
- unit_det_neq_0: Determinant of a unitary is nonzero. Used by m3_3 case_A and case_B/case_C.
- Cmult_cancel_l: Left cancellation for nonzero complex multiplication. Used by m3_3 case_A.
- direct_sum_decomp: Decomposes a direct sum into block form. Used internally by m3_3.
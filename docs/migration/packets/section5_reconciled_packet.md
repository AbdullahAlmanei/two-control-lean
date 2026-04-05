# Section 5 — Reconciled Packet

Merged from:
- section5_paper_packet.md
- section5_rocq_packet.md

## Lemma 5.1

- paper_id: Lemma 5.1
- object_type: lemma
- section: 5
- source_pages: [222, 223, 224]
- paper_statement_summary: Suppose $u_0, u_1$ are complex numbers such that $|u_0| = |u_1| = 1$. There exist 2-qubit unitaries $U_1, U_2, U_3, U_4$ such that $U_1^{BC} U_2^{AC} U_3^{AB} U_4^{BC} = CC(\mathrm{Diag}(u_0, u_1))$ if and only if either $u_0 = u_1$ or $u_0 u_1 = 1$.
- paper_dependencies_explicit: [Lemma 3.1, Lemma 4.1, Lemma A.24]
- paper_dependencies_implicit: [properties of CC and Diag constructions, commutativity of diagonal matrices, tensor product structure of BC-type gates]
- matched_rocq_primary_declaration: m5_1 (Lemma, Main.v:1923)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: [m3_1 (Lemma, Main.v:24), m4_1 (Lemma, Main.v:1008), a24 (Lemma, Appendix/A6_TensorProducts.v:1045)]
- matched_rocq_helper_declarations: [bcgate_unitary (Lemma, Helpers/GateHelpers.v:48), id_tens_equiv_block_diag (Lemma, Helpers/MatrixHelpers.v:2014), block_decomp (Lemma, Helpers/MatrixHelpers.v:900), block_multiply (Lemma, Helpers/MatrixHelpers.v:349), block_equalities (Lemma, Helpers/MatrixHelpers.v:377), control_direct_sum (Lemma, Helpers/MatrixHelpers.v:2023), direct_sum_simplify (Lemma, Helpers/MatrixHelpers.v:2086), notc_notc (Lemma, Helpers/MatrixHelpers.v:2168), diag_commute (Lemma, Helpers/DiagonalHelpers.v:148), ccu_diag (Lemma, Helpers/DiagonalHelpers.v:105), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46), swap_2gate (Lemma, Helpers/SwapHelpers.v:94)]
- matched_rocq_definitions_used: [bcgate (Helpers/GateHelpers.v:10), acgate (Helpers/GateHelpers.v:11), abgate (Helpers/GateHelpers.v:9), ccu (Helpers/GateHelpers.v:12), swapbc (Helpers/SwapHelpers.v:7), diag2 (Helpers/MatrixHelpers.v:41), diag4 (Helpers/MatrixHelpers.v:49), control (QuantumLib), notc (QuantumLib)]
- reconciliation_notes: Exact match. The paper's Lemma 5.1 maps directly to Rocq's m5_1. The statement is identical: an iff characterizing when a BC-AC-AB-BC product of 2-qubit unitaries equals CC(Diag(u0, u1)). The paper's proof structure (forward: isolate middle product, apply Lemma 3.1 then A.24 then 4.1; reverse: two explicit witness constructions) is faithfully reproduced in the Rocq formalization. The Rocq forward direction additionally requires an explicit block decomposition and scalar cancellation argument to establish the |0⟩⟨0|⊗V0 + |1⟩⟨1|⊗V1 form before invoking a24, and an explicit diagonal commutativity chain (ccu_diag, diag_commute, diag_kron, diag_I) that the paper handles in one sentence. The reverse case u0·u1=1 uses notc (CNOT) as the bcgate witness, corresponding to the paper's explicit permutation matrix U.
- dependency_divergence_notes: none — paper explicitly cites Lemma 3.1, Lemma 4.1, and Lemma A.24, and Rocq uses exactly m3_1, m4_1, and a24 as direct dependencies.
- reconciliation_confidence: high
- ambiguities: none

# Section 6 — Reconciled Packet

Merged from:
- section6_paper_packet.md
- section6_rocq_packet.md

## Lemma 6.1

- paper_id: Lemma 6.1
- object_type: lemma
- section: 6
- source_pages: [224]
- paper_statement_summary: (Case analysis of a unitary.) For a 2-qubit unitary $V$, either $\exists |x\rangle : V(|x\rangle \otimes |0\rangle)$ is entangled, or $\exists |\psi\rangle : \forall |x\rangle : \exists |z\rangle : V(|x\rangle \otimes |0\rangle) = |z\rangle \otimes |\psi\rangle$, or $\exists |\psi\rangle : \forall |x\rangle : \exists |z\rangle : V(|x\rangle \otimes |0\rangle) = |\psi\rangle \otimes |z\rangle$.
- paper_dependencies_explicit: [Lemma A.23]
- paper_dependencies_implicit: none
- matched_rocq_primary_declaration: m6_1 (Lemma, Main.v:2274)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: [a23 (Lemma, Appendix/A6_TensorProducts.v:718)]
- matched_rocq_helper_declarations: [qubit0_qubit (Lemma, Helpers/QubitHelpers.v:83), Mmult_qubit (Lemma, Helpers/QubitHelpers.v:794), kron_qubit (Lemma, Helpers/QubitHelpers.v:805), tensor_prod_of_qubit (Lemma, Helpers/QubitHelpers.v:561)]
- matched_rocq_definitions_used: [Entangled (Helpers/MatrixHelpers.v:581), WF_Qubit (Helpers/WFHelpers.v:6)]
- reconciliation_notes: Exact match. The paper's Lemma 6.1 maps directly to Rocq's m6_1. Statement is identical: a three-way case analysis on V(x⊗|0⟩) — entangled, z⊗ψ, or ψ⊗z. The proof structure matches: classical case split on entanglement, then apply Lemma A.23 (a23) for the tensor-product subdivision. The Rocq proof additionally uses classical logic (NNPP) to push the negation inward (¬∃ to ∀¬), which the paper handles implicitly.
- dependency_divergence_notes: none — paper cites Lemma A.23, Rocq uses a23.
- reconciliation_confidence: high
- ambiguities: none

## Lemma 6.2

- paper_id: Lemma 6.2
- object_type: lemma
- section: 6
- source_pages: [224, 225, 226]
- paper_statement_summary: Suppose $u_0, u_1$ are complex numbers such that $|u_0| = |u_1| = 1$. For 2-qubit unitaries $U_1, W_2, V_3, U_4$, if $U_1^{AC} W_2^{BC} V_3^{AC} U_4^{BC} = CC(\mathrm{Diag}(u_0, u_1))$, $V_3(|0\rangle \otimes |0\rangle) = |0\rangle \otimes |0\rangle$, and for any $|x_A\rangle$: $U_1^{AC}(|x_A\rangle \otimes |0_B\rangle \otimes |0_C\rangle) = U_4^{BC\dagger} V_3^{AC\dagger}(|x_A\rangle \otimes |0_B\rangle \otimes |0_C\rangle)$, then either $u_0 = u_1$ or $u_0 u_1 = 1$ or there exist 2-qubit unitaries $W_1, W_3, W_4$ and a 1-qubit unitary $P_3$ such that $U_1^{AC} W_2^{BC} V_3^{AC} U_4^{BC} = W_1^{AC} W_2^{BC} W_3^{AC} W_4^{BC}$ and $W_3 = I \otimes |0\rangle\langle 0| + P_3 \otimes |1\rangle\langle 1|$.
- paper_dependencies_explicit: [Lemma 6.1, Lemma A.10, Lemma A.12, Lemma A.19, Lemma 4.4, Lemma A.31, Lemma A.25, Lemma A.22, Lemma A.17]
- paper_dependencies_implicit: none
- matched_rocq_primary_declaration: m6_2 (Lemma, Main.v:2321)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: [m6_1 (Lemma, Main.v:2274), m4_4 (Lemma, Main.v:1762), a10 (Lemma, Appendix/A3_Swaps.v:7), a12 (Lemma, Appendix/A3_Swaps.v:21), a17 (Lemma, Appendix/A5_ControlledUnitaries.v:13), a19 (Lemma, Appendix/A5_ControlledUnitaries.v:294), a22 (Lemma, Appendix/A6_TensorProducts.v:597), a25 (Lemma, Appendix/A6_TensorProducts.v:1298), a31 (Lemma, Appendix/A7_OtherProperties.v:664)]
- matched_rocq_helper_declarations: [swapab_inverse (Lemma, Helpers/SwapHelpers.v:46), other_unitary_decomp (Lemma, Helpers/UnitaryHelpers.v:7), qubit0_qubit (Lemma, Helpers/QubitHelpers.v:83), qubit1_qubit (Lemma, Helpers/QubitHelpers.v:93), Mmult_qubit (Lemma, Helpers/QubitHelpers.v:794), kron_qubit (Lemma, Helpers/QubitHelpers.v:805), inner_product_kron (Lemma, Helpers/QubitHelpers.v:889), acgate_adjoint (Lemma, Helpers/GateHelpers.v:128), bcgate_adjoint (Lemma, Helpers/GateHelpers.v:66)]
- matched_rocq_definitions_used: [acgate (Helpers/GateHelpers.v:11), bcgate (Helpers/GateHelpers.v:10), abgate (Helpers/GateHelpers.v:9), ccu (Helpers/GateHelpers.v:12), swapab (Helpers/SwapHelpers.v:6), swapbc (Helpers/SwapHelpers.v:7), diag2 (Helpers/MatrixHelpers.v:41), Entangled (Helpers/MatrixHelpers.v:581), WF_Qubit (Helpers/WFHelpers.v:6)]
- reconciliation_notes: Exact match. The paper's Lemma 6.2 maps directly to Rocq's m6_2. Statement is identical: a three-hypothesis implication yielding a three-way disjunction. The proof follows the same three-case analysis of V3† via Lemma 6.1 (m6_1). All three cases (entangled, z⊗ψ, ψ⊗z) use the same lemma sequence as the paper. The Rocq proof's case A uses the swapab conjugation pattern (swapab × acgate U × swapab = bcgate U via a12) to convert an AC-gate identity to BC-gate form before applying a19; the paper describes this as swap-based manipulation with Lemma A.10 and A.12. Case B applies a31 directly. Case C uses a25 then a22 then a17, matching the paper exactly.
- dependency_divergence_notes: none — all nine paper-cited dependencies (Lemma 6.1, A.10, A.12, A.19, 4.4, A.31, A.25, A.22, A.17) have exact Rocq counterparts (m6_1, a10, a12, a19, m4_4, a31, a25, a22, a17).
- reconciliation_confidence: high
- ambiguities: none

## Lemma 6.3

- paper_id: Lemma 6.3
- object_type: lemma
- section: 6
- source_pages: [226, 227, 228]
- paper_statement_summary: Suppose $u_0, u_1$ are complex numbers such that $|u_0| = |u_1| = 1$. For 2-qubit unitaries $V_1, V_2, V_3, V_4$, if $V_1^{AC} V_2^{BC} V_3^{AC} V_4^{BC} = CC(\mathrm{Diag}(u_0, u_1))$, $\exists |\psi\rangle : \forall |x\rangle : \exists |z\rangle : V_2(|x\rangle \otimes |0\rangle) = |z\rangle \otimes |\psi\rangle$, and $V_3(|0\rangle \otimes |0\rangle) = |0\rangle \otimes |0\rangle$, then either $u_0 = u_1$ or $u_0 u_1 = 1$ or there exist 2-qubit unitaries $W_1, W_2, W_3, W_4$ and 1-qubit unitaries $P_1, P_2, P_3, P_4, Q$ such that $W_1^{AC} W_2^{BC} W_3^{AC} W_4^{BC} = CC(\mathrm{Diag}(u_0, u_1))$, $W_1 = I \otimes |\beta\rangle\langle 0| + P_1 \otimes |\beta^\perp\rangle\langle 1|$, $W_2 = I \otimes |0\rangle\langle 0| + P_2 \otimes |1\rangle\langle 1|$, $W_3 = I \otimes |0\rangle\langle 0| + P_3 \otimes |1\rangle\langle 1|$, $W_4 = I \otimes |0\rangle\langle\beta| + P_4 \otimes |1\rangle\langle\beta^\perp|$, where $|\beta\rangle = Q|0\rangle$ and $|\beta^\perp\rangle = Q|1\rangle$.
- paper_dependencies_explicit: [Lemma A.30, Lemma A.29, Lemma 6.2, Lemma A.28, Lemma A.22, Lemma A.26, Lemma A.18]
- paper_dependencies_implicit: none
- matched_rocq_primary_declaration: m6_3 (Lemma, Main.v:2532)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: [m6_2 (Lemma, Main.v:2321), a18 (Lemma, Appendix/A5_ControlledUnitaries.v:212), a22 (Lemma, Appendix/A6_TensorProducts.v:597), a26 (Lemma, Appendix/A6_TensorProducts.v:1361), a28 (Lemma, Appendix/A7_OtherProperties.v:254), a29 (Lemma, Appendix/A7_OtherProperties.v:321), a30 (Lemma, Appendix/A7_OtherProperties.v:416)]
- matched_rocq_helper_declarations: [acgate_adjoint (Lemma, Helpers/GateHelpers.v:128), bcgate_adjoint (Lemma, Helpers/GateHelpers.v:66), other_unitary_decomp (Lemma, Helpers/UnitaryHelpers.v:7), qubit0_qubit (Lemma, Helpers/QubitHelpers.v:83), qubit1_qubit (Lemma, Helpers/QubitHelpers.v:93), Mmult_qubit (Lemma, Helpers/QubitHelpers.v:794), kron_qubit (Lemma, Helpers/QubitHelpers.v:805), nonzero_qubit0 (Lemma, Helpers/MatrixHelpers.v:291), kron_cancel_r (Lemma, Helpers/MatrixHelpers.v:223), a11 (Lemma, Appendix/A3_Swaps.v:14), swap_2gate (Lemma, Helpers/SwapHelpers.v:94)]
- matched_rocq_definitions_used: [acgate (Helpers/GateHelpers.v:11), bcgate (Helpers/GateHelpers.v:10), abgate (Helpers/GateHelpers.v:9), ccu (Helpers/GateHelpers.v:12), swapbc (Helpers/SwapHelpers.v:7), diag2 (Helpers/MatrixHelpers.v:41), WF_Qubit (Helpers/WFHelpers.v:6)]
- reconciliation_notes: Exact match. The paper's Lemma 6.3 maps directly to Rocq's m6_3. Statement is identical. The proof structure matches: apply Lemma A.30 (a30) to rewrite using the V2 hypothesis, derive the key identity via Lemma A.29 (a29), invoke Lemma 6.2 (m6_2), then in the third case derive the W4 and W1 decompositions via Lemma A.28 (a28), A.22 (a22), A.26 (a26), and A.18 (a18). The Rocq proof's third case additionally includes an explicit construction of β_perp as the orthogonal complement of β (with concrete coordinate formulas) and verification of Q's unitarity by direct inner-product computation; the paper defines Q = |β⟩⟨0| + |β⊥⟩⟨1| without detailing the construction. The Rocq proof also uses kron_cancel_r and nonzero_qubit0 to factor out a ⊗|0⟩ term when deriving the W1 decomposition — a step the paper handles implicitly.
- dependency_divergence_notes: none — all seven paper-cited dependencies (A.30, A.29, 6.2, A.28, A.22, A.26, A.18) have exact Rocq counterparts (a30, a29, m6_2, a28, a22, a26, a18).
- reconciliation_confidence: high
- ambiguities: none

## Lemma 6.4

- paper_id: Lemma 6.4
- object_type: lemma
- section: 6
- source_pages: [228, 229, 230]
- paper_statement_summary: (The second main lemma.) Suppose $u_0, u_1$ are complex numbers such that $|u_0| = |u_1| = 1$. There exist 2-qubit unitaries $U_1, U_2, U_3, U_4$ such that $U_1^{AC} U_2^{BC} U_3^{AC} U_4^{BC} = CC(\mathrm{Diag}(u_0, u_1))$ if and only if either $u_0 = u_1$ or $u_0 u_1 = 1$.
- paper_dependencies_explicit: [Lemma A.32, Lemma A.28, Lemma 6.1, Lemma A.19, Lemma 4.3, Lemma A.33, Lemma 6.3, Lemma 4.2]
- paper_dependencies_implicit: none
- matched_rocq_primary_declaration: m6_4 (Lemma, Main.v:2894)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: [m6_1 (Lemma, Main.v:2274), m6_3 (Lemma, Main.v:2532), m4_2 (Lemma, Main.v:1097), m4_3 (Lemma, Main.v:1398), a19 (Lemma, Appendix/A5_ControlledUnitaries.v:294), a28 (Lemma, Appendix/A7_OtherProperties.v:254), a32 (Lemma, Appendix/A7_OtherProperties.v:748), a33 (Lemma, Appendix/A7_OtherProperties.v:1026)]
- matched_rocq_helper_declarations: [diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46), other_unitary_decomp (Lemma, Helpers/UnitaryHelpers.v:7), qubit0_qubit (Lemma, Helpers/QubitHelpers.v:83), qubit1_qubit (Lemma, Helpers/QubitHelpers.v:93), Mmult_qubit (Lemma, Helpers/QubitHelpers.v:794), kron_qubit (Lemma, Helpers/QubitHelpers.v:805), inner_product_kron (Lemma, Helpers/QubitHelpers.v:889), acgate_adjoint (Lemma, Helpers/GateHelpers.v:128), bcgate_adjoint (Lemma, Helpers/GateHelpers.v:66), cancel00 (Helpers/MatrixHelpers.v), cancel01 (Helpers/MatrixHelpers.v), cancel10 (Helpers/MatrixHelpers.v), cancel11 (Helpers/MatrixHelpers.v), swap_2gate (Lemma, Helpers/SwapHelpers.v:94)]
- matched_rocq_definitions_used: [acgate (Helpers/GateHelpers.v:11), bcgate (Helpers/GateHelpers.v:10), abgate (Helpers/GateHelpers.v:9), ccu (Helpers/GateHelpers.v:12), swapbc (Helpers/SwapHelpers.v:7), diag2 (Helpers/MatrixHelpers.v:41), WF_Qubit (Helpers/WFHelpers.v:6)]
- reconciliation_notes: Exact match. The paper's Lemma 6.4 maps directly to Rocq's m6_4. Statement is identical: an iff characterizing when an AC-BC-AC-BC product of 2-qubit unitaries equals CC(Diag(u0, u1)). The forward proof follows the same structure: normalize via Lemma A.32 (a32), derive the key identity via Lemma A.28 (a28), three-case analysis on V2 via Lemma 6.1 (m6_1). Cases 1 (entangled) and 2 (ψ⊗z) use Lemma A.19/A.33 then Lemma 4.3; case 3 (z⊗ψ) uses Lemma 6.3 then Lemma 4.2. The reverse direction reuses Lemma 4.3's reverse direction. Note: the Rocq case ordering from m6_1 (entangled / z⊗ψ / ψ⊗z) differs from the paper's case ordering (entangled / ψ⊗z / z⊗ψ) — paper's case 2 corresponds to Rocq's case C, and paper's case 3 corresponds to Rocq's case B. This is a presentational difference only; the proof content is identical.
- dependency_divergence_notes: none — all eight paper-cited dependencies (A.32, A.28, 6.1, A.19, 4.3, A.33, 6.3, 4.2) have exact Rocq counterparts (a32, a28, m6_1, a19, m4_3, a33, m6_3, m4_2).
- reconciliation_confidence: high
- ambiguities: The Rocq proof's case B/C ordering is swapped relative to the paper's case 2/3 ordering due to the order of disjuncts in m6_1. This is purely presentational and does not affect correctness or dependencies.

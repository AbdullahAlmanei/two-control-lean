# Section 5 — Rocq Packet

## Lemma 5.1

- paper_id_or_best_match: Lemma 5.1
- rocq_primary_declaration: m5_1 (Lemma, Main.v:1923)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Helpers/GateHelpers.v, Helpers/MatrixHelpers.v, Helpers/UnitaryHelpers.v, Helpers/DiagonalHelpers.v, Helpers/SwapHelpers.v, Appendix/A6_TensorProducts.v]
- rocq_direct_dependencies: [m3_1 (Lemma, Main.v:24), m4_1 (Lemma, Main.v:1008), a24 (Lemma, Appendix/A6_TensorProducts.v:1045)]
- rocq_helper_declarations: [bcgate_unitary (Lemma, Helpers/GateHelpers.v:48), id_tens_equiv_block_diag (Lemma, Helpers/MatrixHelpers.v:2014), block_decomp (Lemma, Helpers/MatrixHelpers.v:900), block_multiply (Lemma, Helpers/MatrixHelpers.v:349), block_equalities (Lemma, Helpers/MatrixHelpers.v:377), control_direct_sum (Lemma, Helpers/MatrixHelpers.v:2023), direct_sum_simplify (Lemma, Helpers/MatrixHelpers.v:2086), notc_notc (Lemma, Helpers/MatrixHelpers.v:2168), diag_commute (Lemma, Helpers/DiagonalHelpers.v:148), ccu_diag (Lemma, Helpers/DiagonalHelpers.v:105), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46), swap_2gate (Lemma, Helpers/SwapHelpers.v:94)]
- rocq_definitions_used: [bcgate (Helpers/GateHelpers.v:10), acgate (Helpers/GateHelpers.v:11), abgate (Helpers/GateHelpers.v:9), ccu (Helpers/GateHelpers.v:12), swapbc (Helpers/SwapHelpers.v:7), diag2 (Helpers/MatrixHelpers.v:41), diag4 (Helpers/MatrixHelpers.v:49), control (QuantumLib), notc (QuantumLib)]
- rocq_external_library_items: [QuantumLib.Quantum (notc, notc_unitary, swap, control, control_unitary), QuantumLib.Matrix (Mmult, kron, Mplus, adjoint, WF_Unitary, I, id_kron, Mscale, Mscale_mult_dist_l, Mscale_mult_dist_r, kron_mixed_product, kron_plus_distr_l, kron_plus_distr_r, kron_assoc, Mmult_plus_distr_l, Mmult_plus_distr_r), QuantumLib.Complex (Ceq_dec, Cmod, C1), QuantumLib.Eigenvectors (WF_Diagonal, diag_kron, diag_I)]
- rocq_proof_strategy_summary: Forward (left-to-right, ~180 lines): isolate U2_ac × U3_ab = (bcgate U1)† × ccu(diag2 u0 u1) × (bcgate U4)† by multiplying both sides by the appropriate adjoints. Establish commutativity of each factor (bcgate U1)†, ccu(diag2 u0 u1), and (bcgate U4)† with diag2(u0,u1)⊗I₄ — the bcgate factors commute because bcgate U = I₂⊗U and I₂ commutes with diag2, while ccu commutes because both are diagonal (via ccu_diag and diag_commute). Propagate commutativity to the product to show (U2_ac × U3_ab) commutes with diag2(u0,u1)⊗I₂⊗I₂. Apply m3_1 to get either u0=u1 (done) or U2_ac × U3_ab = |0⟩⟨0|⊗V0 .+ |1⟩⟨1|⊗V1. Apply a24 (Lemma A.24) to refine into tensor-product form |0⟩⟨0|⊗P0⊗Q0 .+ |1⟩⟨1|⊗P1⊗Q1. Substitute back into the original equation, expand bcgate via id_tens_equiv_block_diag, simplify using kron_mixed_product to obtain ccu(diag2 u0 u1) = |0⟩⟨0|⊗(U1×(P0⊗Q0)×U4) .+ |1⟩⟨1|⊗(U1×(P1⊗Q1)×U4). Apply m4_1 to conclude u0=u1 ∨ u0·u1=1. Reverse case u0=u1 (~40 lines): witnesses U1=I₄, U2=I₄, U3=control(diag2 1 u1), U4=I₄. Verify bcgate(I₄)=I₈ and acgate(I₄)=I₈ (the latter by expanding through swapbc definition and showing swap×swap=I). Verify abgate(control(diag2 1 u1)) = ccu(diag2 u1 u1) by direct matrix computation at specific indices. Reverse case u0·u1=1 (~90 lines): witnesses U1=notc, U2=|0⟩⟨0|⊗I₂ .+ |1⟩⟨1|⊗diag2(1,u1), U3=|0⟩⟨0|⊗I₂ .+ |1⟩⟨1|⊗diag2(1,u0), U4=notc. Verify unitarity of U2 and U3 by adjoint computation and outer-product cancellation. Compute acgate(U2) × abgate(U3) using acgate expansion through swapbc, kron_mixed_product, swap_2gate, and direct_sum_decomp to get |0⟩⟨0|⊗I₄ .+ |1⟩⟨1|⊗diag4(1, u1, u0, u0·u1). Apply u0·u1=1 to simplify diag4. Conjugate by bcgate(notc) on both sides, using notc to permute diagonal entries, arriving at |0⟩⟨0|⊗diag4(1,1,1,1) .+ |1⟩⟨1|⊗diag4(1,1,u0,u1) = ccu(diag2 u0 u1) verified via control_direct_sum and direct_sum_simplify.
- rocq_match_confidence: exact
- ambiguities: none

---

## Rocq-only helper notes

### Diagonal commutativity infrastructure
The forward direction relies on showing that each of the three factors (bcgate U1)†, ccu(diag2 u0 u1), (bcgate U4)† commutes with Diag(u0,u1)⊗I₄. The bcgate factors commute trivially (bcgate U = I₂⊗U, and I₂ trivially commutes with any 2×2 matrix under kron). For ccu(diag2 u0 u1), the proof constructs WF_Diagonal proofs for diag2 u0 u1 (by case analysis on indices), applies ccu_diag (Helpers/DiagonalHelpers.v:105) to get WF_Diagonal for the ccu, then uses diag_commute (Helpers/DiagonalHelpers.v:148). The intermediate diag_kron and diag_I are from QuantumLib.Eigenvectors.

### Block decomposition pattern
The forward direction also uses the block_decomp / block_multiply / block_equalities trio from Helpers/MatrixHelpers.v. These decompose an 8×8 unitary into 2×2 blocks of 4×4 matrices (|0⟩⟨0|⊗V00 + |0⟩⟨1|⊗V01 + |1⟩⟨0|⊗V10 + |1⟩⟨1|⊗V11), multiply in that form, and extract per-block equalities. A scalar cancellation argument (if a·M = b·M and a≠b then M=Zero) eliminates the off-diagonal blocks V01 and V10, then unitarity of U forces V00, V11 to be unitary. This pattern also appears in m3_1 (Section 3).

### notc as explicit witness
The reverse case u0·u1=1 uses notc (the CNOT gate from QuantumLib) as the bcgate witness. The critical property is notc_notc (notc × notc = I₄), which allows the conjugation bcgate(notc) × ··· × bcgate(notc) to permute diagonal entries of the inner block.

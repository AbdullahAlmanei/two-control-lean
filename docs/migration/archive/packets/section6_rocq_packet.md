# Section 6 — Rocq Packet

## Lemma 6.1

- paper_id_or_best_match: Lemma 6.1
- rocq_primary_declaration: m6_1 (Lemma, Main.v:2274)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Appendix/A6_TensorProducts.v, Helpers/QubitHelpers.v, Helpers/WFHelpers.v]
- rocq_direct_dependencies: [a23 (Lemma, Appendix/A6_TensorProducts.v:718)]
- rocq_helper_declarations: [qubit0_qubit (Lemma, Helpers/QubitHelpers.v:83), Mmult_qubit (Lemma, Helpers/QubitHelpers.v:794), kron_qubit (Lemma, Helpers/QubitHelpers.v:805), tensor_prod_of_qubit (Lemma, Helpers/QubitHelpers.v:561)]
- rocq_definitions_used: [Entangled (Helpers/MatrixHelpers.v:581), WF_Qubit (Helpers/WFHelpers.v:6)]
- rocq_external_library_items: [QuantumLib.Matrix (WF_Unitary, Mmult, kron), QuantumLib.Complex (NNPP via classical logic)]
- rocq_proof_strategy_summary: Classical case split on whether ∃x such that V(x⊗|0⟩) is entangled. If yes, left disjunct holds directly. If no, push the negation inward (¬∃ to ∀¬, then not_and_or, NNPP) to obtain that ∀x, V(x⊗|0⟩) is a tensor product; apply a23 (Lemma A.23) to distinguish the two tensor-product orientations (z⊗ψ vs ψ⊗z). Proof is ~45 lines.
- rocq_match_confidence: exact
- ambiguities: none

## Lemma 6.2

- paper_id_or_best_match: Lemma 6.2
- rocq_primary_declaration: m6_2 (Lemma, Main.v:2321)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Appendix/A3_Swaps.v, Appendix/A5_ControlledUnitaries.v, Appendix/A6_TensorProducts.v, Appendix/A7_OtherProperties.v, Helpers/GateHelpers.v, Helpers/SwapHelpers.v, Helpers/QubitHelpers.v, Helpers/UnitaryHelpers.v]
- rocq_direct_dependencies: [m6_1 (Lemma, Main.v:2274), m4_4 (Lemma, Main.v:1762), a10 (Lemma, Appendix/A3_Swaps.v:7), a12 (Lemma, Appendix/A3_Swaps.v:21), a17 (Lemma, Appendix/A5_ControlledUnitaries.v:13), a19 (Lemma, Appendix/A5_ControlledUnitaries.v:294), a22 (Lemma, Appendix/A6_TensorProducts.v:597), a25 (Lemma, Appendix/A6_TensorProducts.v:1298), a31 (Lemma, Appendix/A7_OtherProperties.v:664)]
- rocq_helper_declarations: [swapab_inverse (Lemma, Helpers/SwapHelpers.v:46), other_unitary_decomp (Lemma, Helpers/UnitaryHelpers.v:7), qubit0_qubit (Lemma, Helpers/QubitHelpers.v:83), qubit1_qubit (Lemma, Helpers/QubitHelpers.v:93), Mmult_qubit (Lemma, Helpers/QubitHelpers.v:794), kron_qubit (Lemma, Helpers/QubitHelpers.v:805), inner_product_kron (Lemma, Helpers/QubitHelpers.v:889), acgate_adjoint (Lemma, Helpers/GateHelpers.v:128), bcgate_adjoint (Lemma, Helpers/GateHelpers.v:66)]
- rocq_definitions_used: [acgate (Helpers/GateHelpers.v:11), bcgate (Helpers/GateHelpers.v:10), abgate (Helpers/GateHelpers.v:9), ccu (Helpers/GateHelpers.v:12), swapab (Helpers/SwapHelpers.v:6), swapbc (Helpers/SwapHelpers.v:7), diag2 (Helpers/MatrixHelpers.v:41), Entangled (Helpers/MatrixHelpers.v:581), WF_Qubit (Helpers/WFHelpers.v:6)]
- rocq_external_library_items: [QuantumLib.Matrix (WF_Unitary, Mmult, kron, Mplus, adjoint, I, Mmult_assoc, kron_mixed_product, kron_assoc, Mmult_1_l, Mplus_adjoint, kron_adjoint), QuantumLib.Quantum (swap, inner_product_adjoint_r, inner_product_adjoint_l, adjoint_involutive, adjoint00, adjoint11)]
- rocq_proof_strategy_summary: Three-case analysis via m6_1 applied to V3†. Case A (entangled): rewrite the hypothesis using swapab conjugation (swapab_inverse, a12, a10) to convert the AC-gate identity into a BC-gate identity, then apply a19 to obtain U4† = |0⟩⟨0|⊗Q0 .+ |1⟩⟨1|⊗Q1, take the adjoint to get U4, and conclude via m4_4. Case B (V3†(x⊗|0⟩) = z⊗ψ): apply a31 directly to get the existential witnesses W1, W3, W4, P3. Case C (V3†(x⊗|0⟩) = ψ⊗(P0·x)): use a25 to extract P0, derive ∀x: U4†(|0⟩⊗(P0·x)) = |0⟩⊗w via a22, then apply a17 with the two orthogonal images P0|0⟩ and P0|1⟩ to get U4† = |0⟩⟨0|⊗Q0 .+ |1⟩⟨1|⊗Q1, take the adjoint, and conclude via m4_4. Proof is ~210 lines.
- rocq_match_confidence: exact
- ambiguities: none

## Lemma 6.3

- paper_id_or_best_match: Lemma 6.3
- rocq_primary_declaration: m6_3 (Lemma, Main.v:2532)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Appendix/A5_ControlledUnitaries.v, Appendix/A6_TensorProducts.v, Appendix/A7_OtherProperties.v, Helpers/GateHelpers.v, Helpers/SwapHelpers.v, Helpers/QubitHelpers.v, Helpers/MatrixHelpers.v, Helpers/UnitaryHelpers.v]
- rocq_direct_dependencies: [m6_2 (Lemma, Main.v:2321), a18 (Lemma, Appendix/A5_ControlledUnitaries.v:212), a22 (Lemma, Appendix/A6_TensorProducts.v:597), a26 (Lemma, Appendix/A6_TensorProducts.v:1361), a28 (Lemma, Appendix/A7_OtherProperties.v:254), a29 (Lemma, Appendix/A7_OtherProperties.v:321), a30 (Lemma, Appendix/A7_OtherProperties.v:416)]
- rocq_helper_declarations: [acgate_adjoint (Lemma, Helpers/GateHelpers.v:128), bcgate_adjoint (Lemma, Helpers/GateHelpers.v:66), other_unitary_decomp (Lemma, Helpers/UnitaryHelpers.v:7), qubit0_qubit (Lemma, Helpers/QubitHelpers.v:83), qubit1_qubit (Lemma, Helpers/QubitHelpers.v:93), Mmult_qubit (Lemma, Helpers/QubitHelpers.v:794), kron_qubit (Lemma, Helpers/QubitHelpers.v:805), nonzero_qubit0 (Lemma, Helpers/MatrixHelpers.v:291), kron_cancel_r (Lemma, Helpers/MatrixHelpers.v:223), a11 (Lemma, Appendix/A3_Swaps.v:14), swap_2gate (Lemma, Helpers/SwapHelpers.v:94)]
- rocq_definitions_used: [acgate (Helpers/GateHelpers.v:11), bcgate (Helpers/GateHelpers.v:10), abgate (Helpers/GateHelpers.v:9), ccu (Helpers/GateHelpers.v:12), swapbc (Helpers/SwapHelpers.v:7), diag2 (Helpers/MatrixHelpers.v:41), WF_Qubit (Helpers/WFHelpers.v:6)]
- rocq_external_library_items: [QuantumLib.Matrix (WF_Unitary, Mmult, kron, Mplus, adjoint, I, Zero, Mmult_assoc, kron_mixed_product, kron_assoc, kron_plus_distr_l, kron_plus_distr_r, Mmult_plus_distr_l, Mmult_plus_distr_r, Mmult_1_l, Mmult_1_r, Mplus_0_r, id_adjoint_eq, id_kron, kron_adjoint, Mplus_adjoint), QuantumLib.Quantum (swap, adjoint_involutive, adjoint00, adjoint11)]
- rocq_proof_strategy_summary: Use a30 on the V2 assumption to rewrite the product as U1^AC × W2^BC × V3^AC × U4^BC with W2 = I⊗|0⟩⟨0| .+ P2⊗|1⟩⟨1|. Derive the key identity ∀x: U1^AC(x⊗|0⟩⊗|0⟩) = (bcgate U4)† × (acgate V3)†(x⊗|0⟩⊗|0⟩) via a29 (using W2(|0⟩⊗|0⟩) = |0⟩⊗|0⟩). Apply m6_2 to get a three-way disjunction. In the third case: use a28 + W2 structure to derive ∀z: W1^AC × W2^BC(|0⟩⊗z⊗|0⟩) = (bcgate W4)†(|0⟩⊗z⊗|0⟩), simplify using W2's block structure to get ∀z: W1^AC(|0⟩⊗z⊗|0⟩) = (bcgate W4)†(|0⟩⊗z⊗|0⟩), apply a22 to get ∀z: ∃w: W4†(z⊗|0⟩) = z⊗w, apply a26 to get a fixed β with W4†(z⊗|0⟩) = z⊗β. Define Q = β⟨0| .+ β_perp⟨1| (explicitly constructing β_perp as the orthogonal complement), prove Q unitary by explicit inner-product calculation. Show W4×(I⊗Q)×(z⊗|0⟩) = z⊗|0⟩, apply a18 to get W4×(I⊗Q) = I⊗|0⟩⟨0| .+ P4⊗|1⟩⟨1|, derive W4 = I⊗(|0⟩⟨0|×Q†) .+ P4⊗(|1⟩⟨1|×Q†). Similarly derive W1 = I⊗(Q×|0⟩⟨0|) .+ P1⊗(Q×|1⟩⟨1|) by showing (I⊗Q†)×W1 maps x⊗|0⟩↦x⊗|0⟩ using a29 and the W3 structure, then applying a18. Proof is ~360 lines (the longest in section 6).
- rocq_match_confidence: exact
- ambiguities: none

## Lemma 6.4

- paper_id_or_best_match: Lemma 6.4
- rocq_primary_declaration: m6_4 (Lemma, Main.v:2894)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Appendix/A5_ControlledUnitaries.v, Appendix/A6_TensorProducts.v, Appendix/A7_OtherProperties.v, Helpers/GateHelpers.v, Helpers/MatrixHelpers.v, Helpers/QubitHelpers.v, Helpers/DiagonalHelpers.v, Helpers/UnitaryHelpers.v, Helpers/SwapHelpers.v]
- rocq_direct_dependencies: [m6_1 (Lemma, Main.v:2274), m6_3 (Lemma, Main.v:2532), m4_2 (Lemma, Main.v:1097), m4_3 (Lemma, Main.v:1398), a19 (Lemma, Appendix/A5_ControlledUnitaries.v:294), a28 (Lemma, Appendix/A7_OtherProperties.v:254), a32 (Lemma, Appendix/A7_OtherProperties.v:748), a33 (Lemma, Appendix/A7_OtherProperties.v:1026)]
- rocq_helper_declarations: [diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46), other_unitary_decomp (Lemma, Helpers/UnitaryHelpers.v:7), qubit0_qubit (Lemma, Helpers/QubitHelpers.v:83), qubit1_qubit (Lemma, Helpers/QubitHelpers.v:93), Mmult_qubit (Lemma, Helpers/QubitHelpers.v:794), kron_qubit (Lemma, Helpers/QubitHelpers.v:805), inner_product_kron (Lemma, Helpers/QubitHelpers.v:889), acgate_adjoint (Lemma, Helpers/GateHelpers.v:128), bcgate_adjoint (Lemma, Helpers/GateHelpers.v:66), cancel00 (Helpers/MatrixHelpers.v), cancel01 (Helpers/MatrixHelpers.v), cancel10 (Helpers/MatrixHelpers.v), cancel11 (Helpers/MatrixHelpers.v), swap_2gate (Lemma, Helpers/SwapHelpers.v:94)]
- rocq_definitions_used: [acgate (Helpers/GateHelpers.v:11), bcgate (Helpers/GateHelpers.v:10), abgate (Helpers/GateHelpers.v:9), ccu (Helpers/GateHelpers.v:12), swapbc (Helpers/SwapHelpers.v:7), diag2 (Helpers/MatrixHelpers.v:41), WF_Qubit (Helpers/WFHelpers.v:6)]
- rocq_external_library_items: [QuantumLib.Matrix (WF_Unitary, Mmult, kron, Mplus, adjoint, I, Zero, Mmult_assoc, kron_mixed_product, kron_assoc, kron_plus_distr_l, kron_plus_distr_r, Mmult_plus_distr_l, Mmult_plus_distr_r, Mmult_1_l, Mmult_adjoint, kron_adjoint, id_adjoint_eq, Mplus_adjoint), QuantumLib.Quantum (swap, adjoint_involutive, adjoint00, adjoint11, inner_product_adjoint_l, inner_product_adjoint_r)]
- rocq_proof_strategy_summary: Stated as an iff. Forward direction (~200 lines): use a32 to normalize to V1, V2, V3, V4 with V3(|0⟩⊗|0⟩) = |0⟩⊗|0⟩. Apply a28 to derive ∀x: V1^AC × V2^BC(|0⟩⊗x⊗|0⟩) = (bcgate V4)†(|0⟩⊗x⊗|0⟩). Three-case analysis on V2 via m6_1. Case A (entangled): derive V1 = |0⟩⟨0|⊗P0 .+ |1⟩⟨1|⊗P1 via a19 (using inner_product_kron and adjoint manipulation to verify the inner-product hypotheses), then conclude via m4_3. Case B (V2(x⊗|0⟩) = z⊗ψ, i.e. second-qubit-fixed case from paper's Lemma 6.1): this is the paper's third case reordered; apply a33 to get V1 = |0⟩⟨0|⊗P0 .+ |1⟩⟨1|⊗P1, then conclude via m4_3. Case C (V2(x⊗|0⟩) = z⊗ψ, i.e. first-qubit-fixed case): this is the paper's second case where the second qubit is free => corresponds to the ∃ψ:∀x:∃z: V2(x⊗|0⟩) = z⊗ψ assumption needed by m6_3. Apply m6_3 to get a three-way disjunction. In the third sub-case: compute ccu(diag2 u0 u1) = I⊗I⊗(Q×|0⟩⟨0|×Q†) .+ (P1×P3)⊗(P2×P4)⊗(Q×|1⟩⟨1|×Q†) by substituting the W1..W4 decompositions and simplifying using cancel00/01/10/11 and kron_mixed_product. Apply m4_2 to conclude u0=u1. Reverse direction (~15 lines): directly reuse the reverse direction of m4_3, which provides witnesses V1..V4 with an AC-BC-AC-BC product pattern containing the original equation as a consequence.
- rocq_match_confidence: exact
- ambiguities: none

---

## Rocq-only helper notes

### β_perp construction in m6_3
The proof of m6_3 explicitly constructs β_perp as a function (λ x y ⇒ match x, y with 0,0 ⇒ -(β 1 0)*, 1,0 ⇒ (β 0 0)*, _ ⇒ C0) and verifies β†×β = I₁, β_perp†×β_perp = I₁, and β_perp†×β = 0 by direct computation using the qubit unit-norm property. The unitary Q = β×⟨0| .+ β_perp×⟨1| is then verified unitary by expanding Q†×Q using these orthogonality facts plus Mplus01. This concrete construction pattern will need to be adapted for Lean.

### Case numbering differs between paper and Rocq in m6_4
In m6_4, the Rocq proof's case_B corresponds to V2(x⊗|0⟩) = z⊗ψ (the paper's case 2 is V2(x⊗|0⟩) = ψ⊗z), so the Rocq case B uses a33 (paper's Lemma A.33, which handles the ψ⊗z orientation) while the Rocq case C uses m6_3 (which requires the z⊗ψ orientation). The paper's case ordering is: case 1 = entangled, case 2 = ψ⊗z, case 3 = z⊗ψ. The Rocq ordering from m6_1's disjunction is: case A = entangled, case B = z⊗ψ, case C = ψ⊗z. Be aware of this permutation when reconciling.

### swapab conjugation pattern in m6_2 case A
The proof of m6_2 (case A, entangled) uses the identity swapab × acgate U × swapab = bcgate U (via a12) to convert an AC-gate equation into a BC-gate form. This allows applying a19 which expects a BC-gate structure. The swap manipulation uses swapab_inverse (swap²=I), a12, and a10 (swap×(a⊗b) = b⊗a).

### Reverse direction of m6_4
The reverse direction is extremely short (~15 lines): it simply unfolds the reverse direction of m4_3 (Lemma 4.3) which already provides witnesses for either the u0=u1 or u0·u1=1 case in an AC-BC-AC-BC gate pattern, and strips down the existential to match m6_4's conclusion.

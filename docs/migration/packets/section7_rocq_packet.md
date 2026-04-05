# Section 7 — Rocq Packet

## Lemma 7.1

- paper_id_or_best_match: Lemma 7.1
- rocq_primary_declaration: m7_1 (Lemma, Main.v:3099)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Helpers/DiagonalHelpers.v, Helpers/GateHelpers.v, Helpers/UnitaryHelpers.v]
- rocq_direct_dependencies: none
- rocq_helper_declarations: [ccu_diag (Lemma, Helpers/DiagonalHelpers.v:105), diag_control (Lemma, Helpers/DiagonalHelpers.v:91), Diag_diag2 (Lemma, Helpers/DiagonalHelpers.v:5), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46)]
- rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (Helpers/MatrixHelpers.v:41), control (QuantumLib), abgate (Helpers/GateHelpers.v:9)]
- rocq_external_library_items: [QuantumLib.Matrix, QuantumLib.Quantum]
- rocq_proof_strategy_summary: Witness V = control(diag2 1 u0*) × W. Split into unitarity and equality goals. For equality, unfold abgate, rewrite via kron_mixed_product, and associativity to reach (control(diag2 1 u0*) ⊗ I 2) × ccu(diag2 u0 u1). Rather than invoking lma' directly, show both sides are diagonal (via ccu_diag, diag_control, Diag_diag2, diag_kron, diag_mult), then compare entry-by-entry using prep_matrix_equality, destructing on x and solving each of 8 diagonal entries by unfolding ccu/control/diag2/I/kron/Mmult and lca. The key diagonal entry at position 6 uses Cmod_sqr and the unit-modulus hypothesis to simplify u0* × u0 = 1. ~80 lines.
- rocq_match_confidence: high
- ambiguities: none

---

## Lemma 7.2

- paper_id_or_best_match: Lemma 7.2
- rocq_primary_declaration: m7_2 (Lemma, Main.v:3178)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Helpers/GateHelpers.v, Helpers/SwapHelpers.v, Helpers/DiagonalHelpers.v, Helpers/UnitaryHelpers.v, Appendix/A3_Swaps.v]
- rocq_direct_dependencies: [m7_1 (Lemma, Main.v:3099)]
- rocq_helper_declarations: [a13_1 (Lemma, Appendix/A3_Swaps.v:28), a13_2 (Lemma, Appendix/A3_Swaps.v:35), a13_3 (Lemma, Appendix/A3_Swaps.v:52), swapac_twoqubitgate (Lemma, Helpers/GateHelpers.v:1452), swapab_twoqubitgate (Lemma, Helpers/GateHelpers.v:1421), swapbc_conj_ab (Lemma, Helpers/GateHelpers.v:1363), swapac_conj_ab (Lemma, Helpers/GateHelpers.v:1382), swapbc_conj_ac (Lemma, Helpers/GateHelpers.v:1370), swapab_conj_ac (Lemma, Helpers/GateHelpers.v:1337), swapab_conj_bc (Lemma, Helpers/GateHelpers.v:1351), abgate_mult (Lemma, Helpers/GateHelpers.v:1293), bcgate_mult (Lemma, Helpers/GateHelpers.v:1301), acgate_mult (Lemma, Helpers/GateHelpers.v:1309), abgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1266), acgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1275), bcgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1284), swapab_inverse (Lemma, Helpers/SwapHelpers.v:46), swapbc_inverse (Lemma, Helpers/SwapHelpers.v:56), swapac_inverse (Lemma, Helpers/SwapHelpers.v:66), ccu_diag (Lemma, Helpers/DiagonalHelpers.v:105), Diag_diag2 (Lemma, Helpers/DiagonalHelpers.v:5), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46)]
- rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (Helpers/MatrixHelpers.v:41), control (QuantumLib), abgate (Helpers/GateHelpers.v:9), bcgate (Helpers/GateHelpers.v:10), acgate (Helpers/GateHelpers.v:11), TwoQubitGate (Helpers/GateHelpers.v:1264), swapab (Helpers/SwapHelpers.v:6), swapbc (Helpers/SwapHelpers.v:7), swapac (Helpers/SwapHelpers.v:8), swap (QuantumLib)]
- rocq_external_library_items: [QuantumLib.Matrix, QuantumLib.Quantum]
- rocq_proof_strategy_summary: The statement is rephrased: the hypothesis is a product of exactly four TwoQubitGate factors (not "at most four elements of G₂ \ G₁ and any number of G₁"), so the paper's Steps 1 and 2 (absorbing G₁ and forming a canonical product) are bypassed. Step 3 (ensure last factor is bcgate): an auxiliary assertion proves ccu(diag2 u0 u1) × (control(diag2 1 u0*) ⊗ I 2) = ccu(diag2 1 (u0* × u1)) by diagonal comparison (same technique as m7_1). Then destruct V4_gate into three cases (ab/ac/bc). For ab: apply the auxiliary, then conjugate entire product by swapac using a13_3, rewriting each factor via swapac_conj_ab; yields a product ending with bcgate and (u2,u3) = (1, u0* × u1). For ac: conjugate by swapab using a13_1 and swapab_conj_ac; yields bcgate last factor with (u2,u3) = (u0,u1). For bc: product already ends with bcgate. Step 4 (reduce to two canonical forms): destruct W1/W2/W3 gates into ab/ac/bc, giving 27 subcases. In each subcase: apply m7_1 (if first factor is abgate) to change diagonal (u6,u7) to (1, u6* × u7), then conjugate by swapbc (via a13_2) and/or swapac to rearrange into one of the two target forms bcgate × acgate × abgate × bcgate or acgate × bcgate × acgate × bcgate. Uses gate multiplication lemmas (abgate_mult, bcgate_mult, acgate_mult) to combine adjacent same-type gates, and swap conjugation lemmas (swapbc_conj_ab, swapbc_conj_ac, swapac_conj_ab, swapab_conj_ac, swapab_conj_bc) to relabel qubit pairs. ~1000 lines of highly repetitive case analysis.
- rocq_match_confidence: high
- ambiguities: The Rocq statement takes exactly four TwoQubitGate factors rather than the paper's "at most four elements of G₂ \ G₁ and any number of elements of G₁." The paper's R(u₀, u₁) = {(u₀, u₁), (1, u₀*u₁)} is encoded as (u2, u3) = (u0, u1) \/ (u2, u3) = (C1, u0^* * u1). The paper's Steps 1–2 (absorbing G₁ factors and forming a canonical four-element product) are implicitly handled by the stronger hypothesis.

---

## Lemma 7.3

- paper_id_or_best_match: Lemma 7.3
- rocq_primary_declaration: m7_3 (Lemma, Main.v:4173)
- rocq_primary_file: Main.v
- rocq_supporting_files: none
- rocq_direct_dependencies: none
- rocq_helper_declarations: none
- rocq_definitions_used: [pair_equal_spec (Coq stdlib)]
- rocq_external_library_items: [QuantumLib.Complex]
- rocq_proof_strategy_summary: Destruct the two hypotheses: (u2,u3) = (u0,u1) or (u2,u3) = (1, u0*×u1), and u2 = u3 or u2×u3 = 1. Four subcases. In the first two ((u2,u3) = (u0,u1)): pair_equal_spec gives u2 = u0, u3 = u1, then substitute to get u0 = u1 or u0×u1 = 1 directly. In the last two ((u2,u3) = (1, u0*×u1)): pair_equal_spec gives u2 = 1, u3 = u0*×u1. If u2 = u3 then 1 = u0*×u1, multiply both sides by u0, use Cmod_sqr and unit-modulus to simplify u0×u0* = 1, concluding u0 = u1. If u2×u3 = 1 then u0*×u1 = 1, same algebraic argument yields u0 = u1. ~50 lines.
- rocq_match_confidence: high
- ambiguities: none

---

## Theorem 7.4

- paper_id_or_best_match: Theorem 7.4
- rocq_primary_declaration: m7_4 (Theorem, Main.v:4223)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Helpers/GateHelpers.v, Helpers/UnitaryHelpers.v]
- rocq_direct_dependencies: [m7_2 (Lemma, Main.v:3178), m7_3 (Lemma, Main.v:4173), m5_1 (Lemma, Main.v:1923), m6_4 (Lemma, Main.v:2894)]
- rocq_helper_declarations: [abgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1266), acgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1275), bcgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1284)]
- rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (Helpers/MatrixHelpers.v:41), abgate (Helpers/GateHelpers.v:9), bcgate (Helpers/GateHelpers.v:10), acgate (Helpers/GateHelpers.v:11), TwoQubitGate (Helpers/GateHelpers.v:1264)]
- rocq_external_library_items: [QuantumLib.Matrix, QuantumLib.Complex]
- rocq_proof_strategy_summary: Biconditional split. Forward (→): Apply m7_2 to obtain two cases. In each case, verify unit-modulus of u2, u3 by destructing the R-pair hypothesis (pair_equal_spec); if (u2,u3) = (u0,u1) inherit hypotheses, if (u2,u3) = (1, u0*×u1) compute Cmod via Cmod_1 and Cmod_mult/Cmod_Cconj. Apply m5_1 to the first canonical form (bcgate × acgate × abgate × bcgate) and m6_4 to the second (acgate × bcgate × acgate × bcgate) to get u2 = u3 ∨ u2×u3 = 1. Then apply m7_3 to lift to u0 = u1 ∨ u0×u1 = 1. Backward (←): Rewrite the goal using m5_1 (reverse direction) which provides four 4×4 unitaries in bcgate × acgate × abgate × bcgate form; wrap them in TwoQubitGate via abgate/acgate/bcgate_twoqubitgate. ~120 lines.
- rocq_match_confidence: high
- ambiguities: none

---

## Corollary 7.5

- paper_id_or_best_match: Corollary 7.5
- rocq_primary_declaration: m7_5 (Corollary, Main.v:4345)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Appendix/A2_UnitaryMatrices.v, Helpers/GateHelpers.v, Helpers/SwapHelpers.v, Helpers/UnitaryHelpers.v, Helpers/MatrixHelpers.v]
- rocq_direct_dependencies: [m7_4 (Theorem, Main.v:4223)]
- rocq_helper_declarations: [a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10), other_unitary_decomp (Lemma, Helpers/UnitaryHelpers.v:7), abgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1266), acgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1275), bcgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1284), control_decomp (Lemma, Helpers/MatrixHelpers.v:2078), swapbc_3gate (Lemma, Helpers/SwapHelpers.v:137), swapbc_inverse (Lemma, Helpers/SwapHelpers.v:56)]
- rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (Helpers/MatrixHelpers.v:41), control (QuantumLib), abgate (Helpers/GateHelpers.v:9), bcgate (Helpers/GateHelpers.v:10), acgate (Helpers/GateHelpers.v:11), TwoQubitGate (Helpers/GateHelpers.v:1264), swapbc (Helpers/SwapHelpers.v:7), Determinant (QuantumLib)]
- rocq_external_library_items: [QuantumLib.Matrix, QuantumLib.Quantum, QuantumLib.Eigenvectors]
- rocq_proof_strategy_summary: The Rocq statement differs from the paper: instead of "eigenvalues equal or det(U)=1", it states the biconditional in terms of ∃ V D, WF_Unitary V ∧ WF_Diagonal D ∧ U = V×D×V† ∧ (D(0,0) = D(1,1) ∨ Determinant U = 1). The proof establishes three large auxiliary assertions inline. (1) absorption_helper: shows that for any unitary V, conjugating a product of four TwoQubitGates by (I⊗I⊗V†) on the left and (I⊗I⊗V) on the right still yields a product of four TwoQubitGates. This is proved by exhaustive case analysis on all 81 combinations (3⁴) of gate types (ab/ac/bc) for V1–V4, using that abgate commutes with I⊗I⊗V while acgate and bcgate absorb I⊗I⊗V into the inner 4×4 unitary. ~700 lines. (2) ccu_conjugation: shows ccu(V×D×V†) = (I⊗I⊗V) × ccu(D) × (I⊗I⊗V†) via control_decomp, kron manipulations, and other_unitary_decomp. (3) det_equivalence: shows D(0,0)×D(1,1) = 1 ↔ Determinant(U) = 1 via Determinant_multiplicative, other_unitary_decomp (Det(V×V†)=1), and diagonal determinant expansion. Forward direction: spectral-decompose U via a3, rewrite ccu(U) as conjugated ccu(diag2 u0 u1), use absorption_helper to show the conjugated decomposition still uses four TwoQubitGates, then apply m7_4. Backward direction: given the diagonalisation and the eigenvalue/determinant condition, apply m7_4 backward to get a decomposition of ccu(diag2 u0 u1), then use absorption_helper (with V†) to lift back to ccu(U). ~750 lines total.
- rocq_match_confidence: high
- ambiguities: The Rocq statement packages the spectral decomposition into the biconditional itself (∃ V D with U = V×D×V† and conditions on D), rather than stating it purely in terms of eigenvalues and det(U) as the paper does. The equivalence is established internally. The paper's invocation of "Eigenvalues(U) = [u₀, u₁]" and "det(U) = u₀u₁" is replaced by the explicit diagonalisation witness.

---

## Rocq-only helper notes

### Gate algebra infrastructure (Helpers/GateHelpers.v)
- TwoQubitGate (Definition, line 1264): A predicate classifying an 8×8 matrix as abgate V, acgate V, or bcgate V for some 4×4 unitary V. Central to how Sections 7.2–7.5 express "product of elements of G₂."
- abgate, bcgate, acgate (Definitions, lines 9–11): Embed a 4×4 unitary into the 8×8 space on qubits AB, BC, or AC respectively. acgate is defined as swapbc × abgate(U) × swapbc.
- abgate_mult, bcgate_mult, acgate_mult (Lemmas, lines 1293–1309): Closure under multiplication for same-type gates. Heavily used in m7_2 to combine adjacent factors.
- swapbc_conj_ab, swapbc_conj_ac, swapac_conj_ab, swapab_conj_ac, swapab_conj_bc (Lemmas, lines 1337–1393): Conjugation by swap permutations relabels gate types. Core mechanism of the qubit-swap reasoning in m7_2 Step 3 and Step 4.
- abgate_twoqubitgate, acgate_twoqubitgate, bcgate_twoqubitgate (Lemmas, lines 1266–1284): Wrapping lemmas to prove TwoQubitGate for each gate type.
- swapab_twoqubitgate, swapac_twoqubitgate (Lemmas, lines 1421, 1452): Conjugating a TwoQubitGate by swapab or swapac yields a TwoQubitGate. Used in m7_2 Step 3.

### Swap infrastructure (Helpers/SwapHelpers.v)
- swapab, swapbc, swapac (Definitions, lines 6–8): 8×8 qubit-swap matrices. swapac = swapab × swapbc × swapab.
- swapab_inverse, swapbc_inverse, swapac_inverse (Lemmas, lines 46, 56, 66): Each swap is self-inverse.
- swapbc_3gate (Lemma, line 137): Rewrites swapbc × (A ⊗ B ⊗ C) × swapbc = A ⊗ C ⊗ B. Used in m7_5 absorption_helper.

### Appendix declarations used in Section 7
- a13_1 (Lemma, Appendix/A3_Swaps.v:28): swapab × ccu(D) × swapab = ccu(D) for diagonal D. Used in m7_2 Step 3 (ac case).
- a13_2 (Lemma, Appendix/A3_Swaps.v:35): swapbc × ccu(diag2 1 c1) × swapbc = ccu(diag2 1 c1). Used in m7_2 Step 4 (multiple subcases).
- a13_3 (Lemma, Appendix/A3_Swaps.v:52): swapac × ccu(diag2 u0 u1) × swapac = ccu(diag2 u0 u1). Used in m7_2 Step 3 (ab case).
- a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10): Spectral theorem. Used by m7_5 to diagonalise U.

### Diagonal and unitary helpers
- ccu_diag (Lemma, Helpers/DiagonalHelpers.v:105): ccu of a diagonal is diagonal. Used in m7_1 and the auxiliary assertion in m7_2.
- Diag_diag2 (Lemma, Helpers/DiagonalHelpers.v:5): diag2 c1 c2 is WF_Diagonal.
- diag_control (Lemma, Helpers/DiagonalHelpers.v:91): control of a diagonal is diagonal.
- diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46): diag2 is unitary when both entries have modulus 1.
- other_unitary_decomp (Lemma, Helpers/UnitaryHelpers.v:7): V × V† = I for unitary V. Used in m7_5.
- control_decomp (Lemma, Helpers/MatrixHelpers.v:2078): Decomposes control(A) into |0⟩⟨0|⊗I .+ |1⟩⟨1|⊗A. Used in m7_5 ccu_conjugation assertion.

### QuantumLib items (not locally defined)
- Determinant, Determinant_multiplicative, Det_I, get_minor: Determinant machinery. Used by m7_5 det_equivalence assertion.
- Cmod, Cmod_sqr, Cmod_Cconj, Cmod_mult, Cmod_1: Complex modulus lemmas. Used across m7_1–m7_4.
- pair_equal_spec: Injection for pair equality. Used in m7_3 and m7_4.
- diag_mult, diag_kron, diag_I: Diagonal matrix closure properties. Used in m7_1 and m7_2 auxiliary.

# Section 7 — Reconciled Packet

Merged from:
- section7_paper_packet.md
- section7_rocq_packet.md

## Lemma 7.1

- paper_id: Lemma 7.1
- object_type: lemma
- section: 7
- source_pages: [230]
- paper_statement_summary: (Change a diagonal element to one.) Suppose u₀, u₁ are complex numbers such that |u₀| = |u₁| = 1. For a 2-qubit unitary W and a 3-qubit unitary U, if CC(Diag(u₀, u₁)) = W_AB · U, then there exists a 2-qubit unitary V such that CC(Diag(1, u₀*u₁)) = V_AB · U.
- paper_dependencies_explicit: none
- paper_dependencies_implicit: none
- matched_rocq_primary_declaration: m7_1 (Lemma, Main.v:3099)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: none
- matched_rocq_helper_declarations: [ccu_diag (Lemma, Helpers/DiagonalHelpers.v:105), diag_control (Lemma, Helpers/DiagonalHelpers.v:91), Diag_diag2 (Lemma, Helpers/DiagonalHelpers.v:5), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46)]
- matched_rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (Helpers/MatrixHelpers.v:41), control (QuantumLib), abgate (Helpers/GateHelpers.v:9)]
- reconciliation_notes: Paper and Rocq match exactly. The paper's CC(Diag(u₀, u₁)) maps to ccu(diag2 u0 u1), W_AB maps to abgate W, and V = C(Diag(1, u₀*)) · W maps to control(diag2 1 u0*) × W. The proof strategy is identical: construct V explicitly, expand the product, and verify the resulting diagonal matrix entry-by-entry. Rocq uses diagonality to avoid a full lma' computation, comparing entries individually via ccu_diag and diag_mult.
- dependency_divergence_notes: none
- reconciliation_confidence: high
- ambiguities: none

## Lemma 7.2

- paper_id: Lemma 7.2
- object_type: lemma
- section: 7
- source_pages: [230, 231, 232, 233, 234, 235]
- paper_statement_summary: (Reduction.) Suppose u₀, u₁ are complex numbers such that |u₀| = |u₁| = 1. If there exists a product of at most four elements of G₂ \ G₁ and any number of elements of G₁ that is equal to CC(Diag(u₀, u₁)), then either (1) there exist 2-qubit unitaries U₁, U₂, U₃, U₄ and complex numbers u₂, u₃ such that (u₂, u₃) ∈ R(u₀, u₁) and U₁_BC · U₂_AC · U₃_AB · U₄_BC = CC(Diag(u₂, u₃)), or (2) there exist 2-qubit unitaries U₁, U₂, U₃, U₄ and complex numbers u₂, u₃ such that (u₂, u₃) ∈ R(u₀, u₁) and U₁_AC · U₂_BC · U₃_AC · U₄_BC = CC(Diag(u₂, u₃)).
- paper_dependencies_explicit: [Lemma 7.1, Lemma A.12, Lemma A.13]
- paper_dependencies_implicit: none
- matched_rocq_primary_declaration: m7_2 (Lemma, Main.v:3178)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: [m7_1 (Lemma, Main.v:3099)]
- matched_rocq_helper_declarations: [a13_1 (Lemma, Appendix/A3_Swaps.v:28), a13_2 (Lemma, Appendix/A3_Swaps.v:35), a13_3 (Lemma, Appendix/A3_Swaps.v:52), swapac_twoqubitgate (Lemma, Helpers/GateHelpers.v:1452), swapab_twoqubitgate (Lemma, Helpers/GateHelpers.v:1421), swapbc_conj_ab (Lemma, Helpers/GateHelpers.v:1363), swapac_conj_ab (Lemma, Helpers/GateHelpers.v:1382), swapbc_conj_ac (Lemma, Helpers/GateHelpers.v:1370), swapab_conj_ac (Lemma, Helpers/GateHelpers.v:1337), swapab_conj_bc (Lemma, Helpers/GateHelpers.v:1351), abgate_mult (Lemma, Helpers/GateHelpers.v:1293), bcgate_mult (Lemma, Helpers/GateHelpers.v:1301), acgate_mult (Lemma, Helpers/GateHelpers.v:1309), abgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1266), acgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1275), bcgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1284), swapab_inverse (Lemma, Helpers/SwapHelpers.v:46), swapbc_inverse (Lemma, Helpers/SwapHelpers.v:56), swapac_inverse (Lemma, Helpers/SwapHelpers.v:66), ccu_diag (Lemma, Helpers/DiagonalHelpers.v:105), Diag_diag2 (Lemma, Helpers/DiagonalHelpers.v:5), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46)]
- matched_rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (Helpers/MatrixHelpers.v:41), control (QuantumLib), abgate (Helpers/GateHelpers.v:9), bcgate (Helpers/GateHelpers.v:10), acgate (Helpers/GateHelpers.v:11), TwoQubitGate (Helpers/GateHelpers.v:1264), swapab (Helpers/SwapHelpers.v:6), swapbc (Helpers/SwapHelpers.v:7), swapac (Helpers/SwapHelpers.v:8), swap (QuantumLib)]
- reconciliation_notes: The Rocq hypothesis is stronger than the paper's: m7_2 takes exactly four TwoQubitGate factors (a product V1 × V2 × V3 × V4 where each Vi is abgate/acgate/bcgate of some 4×4 unitary), whereas the paper allows "at most four elements of G₂ \ G₁ and any number of elements of G₁." Consequently, the paper's Steps 1–2 (absorbing G₁ factors into G₂ factors and padding to exactly four canonical factors) are unnecessary in the Rocq proof and are bypassed entirely. The Rocq proof begins at the paper's Step 3. The paper's R(u₀, u₁) = {(u₀, u₁), (1, u₀*u₁)} is encoded as a disjunction (u2, u3) = (u0, u1) ∨ (u2, u3) = (C1, u0^* * u1). Paper's Lemma A.12 maps to the swap conjugation lemmas (swapab_conj_ac, swapab_conj_bc, etc.) and paper's Lemma A.13 maps to a13_1/a13_2/a13_3. The paper's eight subcases in Step 4 expand to 27 subcases in Rocq (3³ choices for three gate types ab/ac/bc), though many collapse quickly.
- dependency_divergence_notes: Paper cites Lemma A.12 and Lemma A.13 as single lemmas. In Rocq, A.12 is decomposed into multiple swap conjugation lemmas (swapab_conj_ac, swapab_conj_bc, swapbc_conj_ab, swapbc_conj_ac, swapac_conj_ab) and A.13 is split into three variants (a13_1, a13_2, a13_3) depending on which swap is used and the diagonal form. The paper's direct dependency on Lemma 7.1 is preserved as m7_1 in Rocq.
- reconciliation_confidence: high
- ambiguities: The paper introduces two unnumbered inline definitions at the start of Section 7 — the notion of a "canonical" product and the set R(u₀, u₁) — that are used throughout Lemma 7.2 and later objects. These have no formal paper-numbered labels. In Rocq, "canonical" is implicit in the TwoQubitGate hypothesis and R(u₀, u₁) is the explicit disjunction.

## Lemma 7.3

- paper_id: Lemma 7.3
- object_type: lemma
- section: 7
- source_pages: [235, 236]
- paper_statement_summary: Suppose u₀, u₁ are complex numbers such that |u₀| = |u₁| = 1. Suppose also that (u₂, u₃) ∈ R(u₀, u₁). If (u₂ = u₃ or u₂u₃ = 1), then (u₀ = u₁ or u₀u₁ = 1).
- paper_dependencies_explicit: none
- paper_dependencies_implicit: none
- matched_rocq_primary_declaration: m7_3 (Lemma, Main.v:4173)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: none
- matched_rocq_helper_declarations: none
- matched_rocq_definitions_used: [pair_equal_spec (Coq stdlib)]
- reconciliation_notes: Paper and Rocq match exactly. Both perform four-subcase analysis on which member of R(u₀, u₁) equals (u₂, u₃) crossed with which disjunct (u₂ = u₃ or u₂u₃ = 1) holds. The paper presents this as a table; Rocq destructs on the two disjunctions. In the (1, u₀*u₁) subcases, Rocq uses Cmod_sqr and the unit-modulus hypothesis to simplify u₀ × u₀* = 1, matching the paper's algebraic manipulation. This is a short, self-contained proof (~50 lines) with no dependencies on other main lemmas.
- dependency_divergence_notes: none
- reconciliation_confidence: high
- ambiguities: none

## Theorem 7.4

- paper_id: Theorem 7.4
- object_type: theorem
- section: 7
- source_pages: [236]
- paper_statement_summary: (Main result for a diagonal matrix.) Suppose u₀, u₁ are complex numbers such that |u₀| = |u₁| = 1. There exists a product of at most four elements of G₂ \ G₁ and any number of elements of G₁ that is equal to CC(Diag(u₀, u₁)) if and only if either u₀ = u₁ or u₀u₁ = 1.
- paper_dependencies_explicit: [Lemma 7.2, Lemma 5.1, Lemma 6.4, Lemma 7.3]
- paper_dependencies_implicit: none
- matched_rocq_primary_declaration: m7_4 (Theorem, Main.v:4223)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: [m7_2 (Lemma, Main.v:3178), m7_3 (Lemma, Main.v:4173), m5_1 (Lemma, Main.v:1923), m6_4 (Lemma, Main.v:2894)]
- matched_rocq_helper_declarations: [abgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1266), acgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1275), bcgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1284)]
- matched_rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (Helpers/MatrixHelpers.v:41), abgate (Helpers/GateHelpers.v:9), bcgate (Helpers/GateHelpers.v:10), acgate (Helpers/GateHelpers.v:11), TwoQubitGate (Helpers/GateHelpers.v:1264)]
- reconciliation_notes: Paper and Rocq match on mathematical content. The Rocq statement uses exactly four TwoQubitGate factors (matching the reformulation in m7_2) rather than "at most four elements of G₂ \ G₁ and any number of G₁." Forward direction: m7_2 reduces to two canonical forms, m5_1 handles the first form (bcgate × acgate × abgate × bcgate), m6_4 handles the second (acgate × bcgate × acgate × bcgate), and m7_3 lifts the result from (u₂, u₃) back to (u₀, u₁). Backward direction: m5_1 (reverse) provides a decomposition directly, wrapped in TwoQubitGate. All four paper dependencies are preserved exactly as direct Rocq dependencies.
- dependency_divergence_notes: The Rocq statement quantifies over four TwoQubitGate factors instead of the paper's "at most four of G₂ \ G₁ and any number of G₁." This is a hypothesis-strengthening relative to the paper. The equivalence between these formulations (absorbing G₁ factors) is handled implicitly; the Rocq proof never needs to perform this absorption because it assumes the stronger statement. This divergence propagates from m7_2.
- reconciliation_confidence: high
- ambiguities: none

## Corollary 7.5

- paper_id: Corollary 7.5
- object_type: corollary
- section: 7
- source_pages: [236, 237]
- paper_statement_summary: (Main result for a gate with two controls.) For a 1-qubit unitary U, there exists a product of at most four elements of G₂ \ G₁ and any number of elements of G₁ that is equal to CC(U) if and only if either the eigenvalues of U are equal or det(U) = 1.
- paper_dependencies_explicit: [Theorem 7.4, Theorem A.3]
- paper_dependencies_implicit: none
- matched_rocq_primary_declaration: m7_5 (Corollary, Main.v:4345)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: [m7_4 (Theorem, Main.v:4223)]
- matched_rocq_helper_declarations: [a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10), other_unitary_decomp (Lemma, Helpers/UnitaryHelpers.v:7), abgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1266), acgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1275), bcgate_twoqubitgate (Lemma, Helpers/GateHelpers.v:1284), control_decomp (Lemma, Helpers/MatrixHelpers.v:2078), swapbc_3gate (Lemma, Helpers/SwapHelpers.v:137), swapbc_inverse (Lemma, Helpers/SwapHelpers.v:56)]
- matched_rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (Helpers/MatrixHelpers.v:41), control (QuantumLib), abgate (Helpers/GateHelpers.v:9), bcgate (Helpers/GateHelpers.v:10), acgate (Helpers/GateHelpers.v:11), TwoQubitGate (Helpers/GateHelpers.v:1264), swapbc (Helpers/SwapHelpers.v:7), Determinant (QuantumLib)]
- reconciliation_notes: The Rocq statement differs structurally from the paper. The paper states the biconditional in terms of eigenvalues and det(U). The Rocq statement packages the spectral decomposition into the right-hand side of the biconditional as ∃ V D, WF_Unitary V ∧ WF_Diagonal D ∧ U = V × D × V† ∧ (D(0,0) = D(1,1) ∨ Determinant U = 1), internalising the spectral theorem invocation. The Rocq proof includes a massive inline auxiliary (absorption_helper, ~700 lines) that shows conjugating a product of four TwoQubitGates by (I⊗I⊗V†) and (I⊗I⊗V) still yields four TwoQubitGates, by exhaustive 81-case analysis (3⁴ gate-type combinations). The paper handles this as the simple observation that I⊗I⊗V is an element of G₁ and can be absorbed. Paper's Theorem A.3 maps to a3 in Rocq; the Determinant equivalence is established via inline assertions using Determinant_multiplicative, Det_I, and other_unitary_decomp.
- dependency_divergence_notes: Paper cites Theorem A.3 (spectral theorem) as an explicit dependency. In Rocq, a3 is used in the forward direction to obtain the diagonalisation, but the spectral decomposition is also baked into the statement itself. The paper's simple argument "I⊗I⊗V ∈ G₁ so it can be absorbed" becomes the 700-line absorption_helper in Rocq because Rocq must explicitly verify TwoQubitGate preservation through all gate-type combinations. This is a significant structural divergence in proof effort, though mathematically equivalent.
- reconciliation_confidence: high
- ambiguities: The Rocq statement form (∃ V D with conditions) is not literally the same as the paper's "eigenvalues equal or det(U) = 1." The equivalence between these formulations is established within the Rocq proof itself. A future Lean formalisation could choose either statement form.

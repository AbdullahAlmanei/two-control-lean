# Section 4 — Reconciled Packet

Merged from:
- section4_paper_packet.md
- section4_rocq_packet.md

---

## Lemma 4.1

- paper_id: Lemma 4.1
- object_type: lemma
- section: 4
- source_pages: [216, 217]
- paper_statement_summary: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. There exist 2-qubit unitaries U, V and 1-qubit unitaries P0, P1, Q0, Q1 such that |0⟩⟨0| ⊗ U(P0 ⊗ Q0)V + |1⟩⟨1| ⊗ U(P1 ⊗ Q1)V = CC(Diag(u0, u1)) if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies_explicit: [Lemma 3.2]
- paper_dependencies_implicit: [Lemma A.4]
- matched_rocq_primary_declaration: m4_1 (Lemma, Main.v:1008)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: [m3_2 (Lemma, Main.v:272)]
- matched_rocq_helper_declarations: [direct_sum_simplify (Lemma, Helpers/MatrixHelpers.v:2086), control_direct_sum (Lemma, Helpers/MatrixHelpers.v:2023), other_unitary_decomp (Lemma, Helpers/UnitaryHelpers.v:7), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46)]
- matched_rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (QuantumLib), diag4 (Helpers/MatrixHelpers.v:49), control (QuantumLib), notc (QuantumLib)]
- reconciliation_notes: Exact match. Paper says "Lemma A.4" is implicitly used; Rocq proof does not call a4 directly — the underlying content (eigenvector manipulation under unitary similarity) is absorbed into the direct_sum_simplify + other_unitary_decomp steps. Paper's forward-direction argument and Rocq's proof strategy agree structurally: decompose via direct sum, extract block equalities, combine to get a similarity relation on a tensor product, invoke Lemma 3.2. Reverse constructions also agree — paper says "CNOT-based witnesses", Rocq uses notc (which is CNOT). The Rocq iff is u0 * u1 = 1 (literal C1), matching the paper's u0 u1 = 1.
- dependency_divergence_notes: Paper lists "Lemma A.4" as an implicit dependency. Rocq proof does not invoke a4 (from A2_UnitaryMatrices.v:43) but achieves the same effect through algebraic manipulation. No missing Rocq dependencies beyond this.
- reconciliation_confidence: high
- ambiguities: none

---

## Lemma 4.2

- paper_id: Lemma 4.2
- object_type: lemma
- section: 4
- source_pages: [217, 218]
- paper_statement_summary: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. Suppose Q is a 1-qubit unitary and let |β⟩ = Q|0⟩ and |β⊥⟩ = Q|1⟩. There exist 1-qubit unitaries P0, P1 such that I ⊗ I ⊗ |β⟩⟨β| + P0 ⊗ P1 ⊗ |β⊥⟩⟨β⊥| = CC(Diag(u0, u1)) if and only if u0 = 1 and u1 = 1.
- paper_dependencies_explicit: [Lemma 3.2]
- paper_dependencies_implicit: [Lemma A.8]
- matched_rocq_primary_declaration: m4_2 (Lemma, Main.v:1097)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: []
- matched_rocq_helper_declarations: [a8 (Lemma, Appendix/A2_UnitaryMatrices.v:213), kron_cancel_l (Lemma, Helpers/MatrixHelpers.v:186)]
- matched_rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (QuantumLib), control (QuantumLib)]
- reconciliation_notes: Exact match on statement and conclusion (u0 = 1 ∧ u1 = 1). Both paper and Rocq use Lemma A.8 (a8 in Rocq). The paper's forward-direction proof sketch matches Rocq: case-split on components of β, use orthogonality to eliminate the β⊥ term, extract u0 = 1 and u1 = 1 by cancellation. The Rocq proof performs a three-way Ceq_dec split (a=0, b=0, both nonzero) where the paper is somewhat implicit about cases. Both reverse directions use P0 = P1 = I and a8.
- dependency_divergence_notes: Paper lists "Lemma 3.2" as an explicit dependency but the Rocq proof m4_2 does not invoke m3_2. The paper may cite Lemma 3.2 as context for the section rather than as a direct proof dependency. Paper lists "Lemma A.8" as implicit; Rocq uses it explicitly (a8). No dependency is missing in Rocq but the claimed paper dependency on Lemma 3.2 does not appear in the Rocq proof.
- reconciliation_confidence: high
- ambiguities: Paper claims explicit dependency on Lemma 3.2 but Rocq proof does not use m3_2. This may be a paper-level citation for motivation rather than a formal proof dependency.

---

## Lemma 4.3

- paper_id: Lemma 4.3
- object_type: lemma
- section: 4
- source_pages: [219, 220, 221]
- paper_statement_summary: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. There exist 2-qubit unitaries V1, V2, V3, V4 and 1-qubit unitaries P0, P1, where V1 = |0⟩⟨0| ⊗ P0 + |1⟩⟨1| ⊗ P1, such that V1_AC · V2_BC · V3_AC · V4_BC = CC(Diag(u0, u1)) if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies_explicit: [Lemma A.27, Theorem A.3, Lemma 3.3]
- paper_dependencies_implicit: [Lemma A.4, Lemma A.11]
- matched_rocq_primary_declaration: m4_3 (Lemma, Main.v:1398)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: [m3_3 (Lemma, Main.v:504)]
- matched_rocq_helper_declarations: [a27 (Lemma, Appendix/A7_OtherProperties.v:11), a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10), a11 (Lemma, Appendix/A3_Swaps.v:14), control_decomp (Lemma, Helpers/MatrixHelpers.v:2078), direct_sum_simplify (Lemma, Helpers/MatrixHelpers.v:2086), control_direct_sum (Lemma, Helpers/MatrixHelpers.v:2023), other_unitary_decomp (Lemma, Helpers/UnitaryHelpers.v:7), bcgate_unitary (Lemma, Helpers/GateHelpers.v:48), swap_2gate (Lemma, Helpers/SwapHelpers.v:94), Cexp_Cmod (Lemma, Helpers/AlgebraHelpers.v:813), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46)]
- matched_rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (QuantumLib), diag4 (Helpers/MatrixHelpers.v:49), control (QuantumLib), acgate (Helpers/GateHelpers.v:11), bcgate (Helpers/GateHelpers.v:10), abgate (Helpers/GateHelpers.v:9), swapbc (Helpers/SwapHelpers.v:7), σx (QuantumLib), swap (QuantumLib)]
- reconciliation_notes: Exact match. All three explicit paper dependencies are present in Rocq: Lemma A.27 → a27, Theorem A.3 → a3, Lemma 3.3 → m3_3. Paper's implicit dependency Lemma A.11 maps to a11 in Rocq, also used. Paper's implicit dependency Lemma A.4 is not directly invoked in the Rocq proof (same pattern as Lemma 4.1). The proof structure aligns: forward direction uses a27 for the controlled decomposition, spectral theorem a3 for diagonalisation, and m3_3 for the eigenvalue condition. Reverse direction matches: u0=u1 case uses swap, u0·u1=1 case parameterises via Cexp and constructs controlled-P witnesses. This is the longest proof in Section 4 (~360 Rocq lines, spanning pages 219–221 in the paper).
- dependency_divergence_notes: Paper's implicit "Lemma A.4" not directly invoked in Rocq proof (absorbed into algebraic steps), same pattern observed in Lemma 4.1.
- reconciliation_confidence: high
- ambiguities: none

---

## Lemma 4.4

- paper_id: Lemma 4.4
- object_type: lemma
- section: 4
- source_pages: [222]
- paper_statement_summary: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. There exist 2-qubit unitaries V1, V2, V3, V4 and 1-qubit unitaries P0, P1, where V4 = |0⟩⟨0| ⊗ P0 + |1⟩⟨1| ⊗ P1, such that V1_AC · V2_BC · V3_AC · V4_BC = CC(Diag(u0, u1)) if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies_explicit: [Lemma 4.3]
- paper_dependencies_implicit: []
- matched_rocq_primary_declaration: m4_4 (Lemma, Main.v:1762)
- matched_rocq_primary_file: Main.v
- matched_rocq_direct_dependencies: [m4_3 (Lemma, Main.v:1398)]
- matched_rocq_helper_declarations: [a13_1 (Lemma, Appendix/A3_Swaps.v:28), a12 (Lemma, Appendix/A3_Swaps.v:21), acgate_adjoint (Lemma, Helpers/GateHelpers.v:128), swapab_hermitian (Lemma, Helpers/SwapHelpers.v:78), swapab_inverse (Lemma, Helpers/SwapHelpers.v:46)]
- matched_rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (QuantumLib), control (QuantumLib), acgate (Helpers/GateHelpers.v:11), bcgate (Helpers/GateHelpers.v:10), swapab (Helpers/SwapHelpers.v:6), swapbc (Helpers/SwapHelpers.v:7)]
- reconciliation_notes: Exact match. Paper says "follows easily from Lemma 4.3 by exchanging the roles of A and B and considering the conjugate transpose." Rocq implements this precisely: take adjoints of all factors, reverse order, apply m4_3 to conjugate eigenvalues via Cmod_Cconj, then take adjoints back. The Rocq proof additionally uses a13_1 (ccu adjoint), a12 (swapab exchanges ac/bc gates), acgate_adjoint, swapab_hermitian, and swapab_inverse — these are the mechanical steps needed to formalise the paper's "exchange roles and take conjugate transpose" argument.
- dependency_divergence_notes: none
- reconciliation_confidence: high
- ambiguities: The paper gives no independent proof — it is a one-line reduction to Lemma 4.3. The Rocq proof is correspondingly short but non-trivial (~160 lines) due to the bookkeeping of adjoint/swap manipulations.
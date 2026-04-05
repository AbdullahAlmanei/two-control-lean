# Section 4 — Rocq Packet

## Lemma 4.1

- paper_id_or_best_match: Lemma 4.1
- rocq_primary_declaration: m4_1 (Lemma, Main.v:1008)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Helpers/GateHelpers.v, Helpers/MatrixHelpers.v, Helpers/UnitaryHelpers.v]
- rocq_direct_dependencies: [m3_2 (Lemma, Main.v:272)]
- rocq_helper_declarations: [direct_sum_simplify (Lemma, Helpers/MatrixHelpers.v:2086), control_direct_sum (Lemma, Helpers/MatrixHelpers.v:2023), other_unitary_decomp (Lemma, Helpers/UnitaryHelpers.v:7), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46)]
- rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (QuantumLib), diag4 (Helpers/MatrixHelpers.v:49), control (QuantumLib), notc (QuantumLib)]
- rocq_external_library_items: [QuantumLib.Quantum (notc, notc_unitary, notc_notc), QuantumLib.Matrix (Mmult, kron, Mplus, adjoint, WF_Unitary, I, id_unitary)]
- rocq_proof_strategy_summary: Forward: rewrite LHS via direct_sum_decomp into |0⟩⟨0|⊗block0 .+ |1⟩⟨1|⊗block1; rewrite ccu via control_direct_sum into |0⟩⟨0|⊗I₄ .+ |1⟩⟨1|⊗control(diag2 u0 u1). Apply direct_sum_simplify to extract U(P0⊗Q0)V = I₄ and U(P1⊗Q1)V = control(diag2 u0 u1). Rewrite control(diag2 u0 u1) as diag4 1 1 u0 u1. Combine the two equalities using other_unitary_decomp (V×V† = I) to get diag4 1 1 u0 u1 = U×((P1×P0†)⊗(Q1×Q0†))×U†. Apply m3_2 to conclude u0=u1 ∨ u0·u1=1. Reverse case u0=u1: witnesses U=V=I₄, P0=I, P1=diag2 1 u1, Q0=Q1=I. Reverse case u0·u1=1: witnesses U=V=notc, P0=I, P1=diag2 1 u0, Q0=I, Q1=diag2 1 u1; verified via notc_notc and direct computation.
- rocq_match_confidence: exact
- ambiguities: none

---

## Lemma 4.2

- paper_id_or_best_match: Lemma 4.2
- rocq_primary_declaration: m4_2 (Lemma, Main.v:1097)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Helpers/MatrixHelpers.v, Helpers/GateHelpers.v, Appendix/A2_UnitaryMatrices.v]
- rocq_direct_dependencies: []
- rocq_helper_declarations: [a8 (Lemma, Appendix/A2_UnitaryMatrices.v:213), kron_cancel_l (Lemma, Helpers/MatrixHelpers.v:186)]
- rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (QuantumLib), control (QuantumLib)]
- rocq_external_library_items: [QuantumLib.Matrix (Mmult, kron, Mplus, adjoint, WF_Unitary, I, id_unitary, qubit0, qubit1), QuantumLib.Complex (Ceq_dec, Cmult_cancel_r, C0, C1)]
- rocq_proof_strategy_summary: Forward: set a = β₀, b = β₁ (components of β = Q|0⟩). Three-way case split via Ceq_dec. Case a=0: show β×β† = |1⟩⟨1| and β⊥×β⊥† = |0⟩⟨0| (using a8); extract diagonal entries of the ccu equation at matrix indices (7,7), (0,0), (2,2), (4,4), (6,6) to force u0=1 and u1=1. Case b=0: symmetric — β×β† = |0⟩⟨0|, β⊥×β⊥† = |1⟩⟨1|; similar diagonal extraction. Case a≠0 ∧ b≠0: multiply both sides by |1⟩⊗|1⟩⊗β; the β⊥ term vanishes since β⊥†×β = 0 (orthogonality via a8); the β term reduces via β†×β = I₁; the ccu side decomposes via control_decomp to yield |1⟩⊗|1⟩⊗(diag2 u0 u1 × β) = |1⟩⊗|1⟩⊗β; apply kron_cancel_l then Cmult_cancel_r on each component to get u0=1, u1=1. Reverse: set P0=P1=I; use a8 to show Q|0⟩⟨0|Q† + Q|1⟩⟨1|Q† = I, then verify ccu(diag2 1 1) equals I⊗I⊗I via control_direct_sum.
- rocq_match_confidence: exact
- ambiguities: none

---

## Lemma 4.3

- paper_id_or_best_match: Lemma 4.3
- rocq_primary_declaration: m4_3 (Lemma, Main.v:1398)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Helpers/GateHelpers.v, Helpers/SwapHelpers.v, Helpers/MatrixHelpers.v, Helpers/UnitaryHelpers.v, Helpers/AlgebraHelpers.v, Helpers/DiagonalHelpers.v, Appendix/A2_UnitaryMatrices.v, Appendix/A3_Swaps.v, Appendix/A7_OtherProperties.v]
- rocq_direct_dependencies: [m3_3 (Lemma, Main.v:504)]
- rocq_helper_declarations: [a27 (Lemma, Appendix/A7_OtherProperties.v:11), a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10), a11 (Lemma, Appendix/A3_Swaps.v:14), control_decomp (Lemma, Helpers/MatrixHelpers.v:2078), direct_sum_simplify (Lemma, Helpers/MatrixHelpers.v:2086), control_direct_sum (Lemma, Helpers/MatrixHelpers.v:2023), other_unitary_decomp (Lemma, Helpers/UnitaryHelpers.v:7), bcgate_unitary (Lemma, Helpers/GateHelpers.v:48), swap_2gate (Lemma, Helpers/SwapHelpers.v:94), Cexp_Cmod (Lemma, Helpers/AlgebraHelpers.v:813), diag2_unitary (Lemma, Helpers/UnitaryHelpers.v:46)]
- rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (QuantumLib), diag4 (Helpers/MatrixHelpers.v:49), control (QuantumLib), acgate (Helpers/GateHelpers.v:11), bcgate (Helpers/GateHelpers.v:10), abgate (Helpers/GateHelpers.v:9), swapbc (Helpers/SwapHelpers.v:7), σx (QuantumLib), swap (QuantumLib)]
- rocq_external_library_items: [QuantumLib.Quantum (swap, swap_unitary, σx, σx_unitary, notc), QuantumLib.Matrix (Mmult, kron, Mplus, adjoint, WF_Unitary, I, control), QuantumLib.Complex (Cexp, Cexp_add, Cexp_neg, Cexp_nonzero, Cmod_Cexp, Cinv_l, Cinv_r, Cmod_inv, Cmod_gt_0)]
- rocq_proof_strategy_summary: Forward: decompose ccu(diag2 u0 u1) = |0⟩⟨0|⊗I₄ .+ |1⟩⟨1|⊗control(diag2 u0 u1) via control_decomp. Apply a27 to the alternating acgate/bcgate product with V1 = |0⟩⟨0|⊗P0 .+ |1⟩⟨1|⊗P1 to extract Q0, Q1 with V4 = |0⟩⟨0|⊗Q0 .+ |1⟩⟨1|⊗Q1. Compute acgate V1 × bcgate V2 × acgate V3 blockwise, expanding acgate definition and simplifying via swap_2gate and cancel lemmas. Eliminate V4 by multiplying with (bcgate V4)† and using other_unitary_decomp; apply direct_sum_simplify to get (I⊗P0)V2(I⊗Q0) = V4† and (I⊗P1)V2(I⊗Q1) = control(diag2 u0 u1)×V4†. Combine the two equalities to obtain control(diag2 u0 u1) = (I⊗(P0×P1†))×(similarity)×(I⊗(P0×P1†))†. Apply a3 (spectral theorem) to Q1×Q0† to get diagonal D, rewrite I⊗D = diag4(D₀₀, D₁₁, D₀₀, D₁₁), and invoke m3_3. Reverse case u0=u1: V1=I₄, V2=swap, V3=control(diag2 1 u1), V4=swap; verified via swap_swap, swap_2gate, and control_direct_sum. Reverse case u0·u1=1: use Cexp_Cmod to write u1=Cexp(θ), set u=Cexp(θ/2), P=diag2(u⁻¹, u). Construct V1=V3=control(P) on AC, V2=|0⟩⟨0|⊗σx + |1⟩⟨1|⊗I on BC, V4=V2†. Verify P×P = diag2 u0 u1 by Cexp_add/Cexp_neg, P×σx×P×σx = I by Cinv_l/Cinv_r, then expand the full product using extensive kron_mixed_product and cancel lemma rewrites, concluding via control_direct_sum and direct_sum_decomp. This is the longest Section 4 proof (~360 lines).
- rocq_match_confidence: exact
- ambiguities: none

---

## Lemma 4.4

- paper_id_or_best_match: Lemma 4.4
- rocq_primary_declaration: m4_4 (Lemma, Main.v:1762)
- rocq_primary_file: Main.v
- rocq_supporting_files: [Helpers/GateHelpers.v, Helpers/SwapHelpers.v, Appendix/A3_Swaps.v]
- rocq_direct_dependencies: [m4_3 (Lemma, Main.v:1398)]
- rocq_helper_declarations: [a13_1 (Lemma, Appendix/A3_Swaps.v:28), a12 (Lemma, Appendix/A3_Swaps.v:21), acgate_adjoint (Lemma, Helpers/GateHelpers.v:128), swapab_hermitian (Lemma, Helpers/SwapHelpers.v:78), swapab_inverse (Lemma, Helpers/SwapHelpers.v:46)]
- rocq_definitions_used: [ccu (Helpers/GateHelpers.v:12), diag2 (QuantumLib), control (QuantumLib), acgate (Helpers/GateHelpers.v:11), bcgate (Helpers/GateHelpers.v:10), swapab (Helpers/SwapHelpers.v:6), swapbc (Helpers/SwapHelpers.v:7)]
- rocq_external_library_items: [QuantumLib.Matrix (adjoint, Mmult, WF_Unitary, adjoint_involutive), QuantumLib.Complex (Cconj_involutive, Cmod_Cconj, Cconj_mult_distr), QuantumLib.Quantum (control_adjoint)]
- rocq_proof_strategy_summary: Forward: establish conj equivalence (u0*=u1* ∨ u0*·u1*=1 ↔ u0=u1 ∨ u0·u1=1) via Cconj_involutive and Cconj_mult_distr. Note diag2(u0*, u1*) = (diag2 u0 u1)†. Given witnesses V1,...,V4 with V4 controlled, take adjoints V4†,...,V1† in reversed order and apply m4_3 (which has V1 controlled) to diag2(u0*, u1*): the controlled structure on V4 migrates to position 1 via adjoint. Verify using a13_1 (ccu(D)† = ccu(D†)), a12 (swapab conjugation exchanges bcgate↔acgate), acgate_adjoint, swapab_hermitian, and swapab_inverse to rearrange the product of adjoints into the m4_3 form. Reverse: symmetric — from m4_3 applied to conjugates, take adjoints back to recover the V4-controlled form. Both directions reuse unit-modulus preservation Cmod_Cconj.
- rocq_match_confidence: exact
- ambiguities: none

---

## Rocq-only helper notes

### Gate infrastructure (Helpers/GateHelpers.v)
- ccu (Definition, line 12): ccu U = control (control U). The doubly-controlled gate used by all four lemmas.
- acgate (Definition, line 11): acgate U = swapbc × (abgate U) × swapbc. Acts U on qubits A,C. Used by m4_3 and m4_4.
- bcgate (Definition, line 10): bcgate U = I 2 ⊗ U. Acts U on qubits B,C. Used by m4_3 and m4_4.
- abgate (Definition, line 9): abgate U = U ⊗ I 2. Acts U on qubits A,B. Used by m4_3 internally.
- bcgate_unitary (Lemma, line 48): Unitarity of bcgate. Used in m4_3's forward direction.
- acgate_adjoint (Lemma, line 128): (acgate U)† = acgate (U†). Used by m4_4.

### Swap infrastructure (Helpers/SwapHelpers.v)
- swapbc (Definition, line 7): I 2 ⊗ swap. Used in acgate definition.
- swapab (Definition, line 6): swap ⊗ I 2. Used by m4_4 via a12.
- swap_2gate (Lemma, line 94): swap × (A ⊗ B) × swap = B ⊗ A. Used by m4_3 to simplify acgate expansions.
- swapab_hermitian (Lemma, line 78), swapab_inverse (Lemma, line 46): Self-adjointness and involutivity of swapab. Used by m4_4.

### Matrix helpers (Helpers/MatrixHelpers.v)
- direct_sum_simplify (Lemma, line 2086): If |0⟩⟨0|⊗A .+ |1⟩⟨1|⊗B = |0⟩⟨0|⊗C .+ |1⟩⟨1|⊗D then A=C ∧ B=D. Central to forward directions of m4_1 and m4_3.
- control_direct_sum (Lemma, line 2023): control A = I n .⊕ A. Used by m4_1 (forward and reverse), m4_3.
- control_decomp (Lemma, line 2078): control A = |0⟩⟨0|⊗I .+ |1⟩⟨1|⊗A. Used by m4_2 and m4_3.
- kron_cancel_l (Lemma, line 186): Cancellation of left Kronecker factor. Key step in m4_2's a≠0 ∧ b≠0 case.
- diag4 (Definition, line 49): Explicit 4×4 diagonal matrix. Used to express control(diag2 u0 u1) = diag4 1 1 u0 u1 in m4_1.

### Unitary helpers (Helpers/UnitaryHelpers.v)
- other_unitary_decomp (Lemma, line 7): U unitary implies U†×U = I. Used by m4_1 and m4_3 to eliminate sandwich products.
- diag2_unitary (Lemma, line 46): diag2 c1 c2 is unitary when both have unit modulus. Used by reverse directions.

### Algebra helpers (Helpers/AlgebraHelpers.v)
- Cexp_Cmod (Lemma, line 813): Every unit-modulus complex has exponential form Cexp θ. Used by m4_3 reverse direction to parameterise u1.

### Appendix declarations
- a27 (Lemma, Appendix/A7_OtherProperties.v:11): For an alternating acgate/bcgate four-factor product with V1 = |0⟩⟨0|⊗P0 .+ |1⟩⟨1|⊗P1 equalling |0⟩⟨0|⊗U0 .+ |1⟩⟨1|⊗U1, derives Q0, Q1 such that V4 = |0⟩⟨0|⊗Q0 .+ |1⟩⟨1|⊗Q1. Used by m4_3 forward.
- a3 (Theorem, Appendix/A2_UnitaryMatrices.v:10): Spectral theorem for unitaries. Used by m4_3 to diagonalise Q1×Q0†.
- a8 (Lemma, Appendix/A2_UnitaryMatrices.v:213): Q|0⟩⟨0|Q† + Q|1⟩⟨1|Q† = I for unitary Q. Used by m4_2.
- a11 (Lemma, Appendix/A3_Swaps.v:14): swap×(A⊗B)×swap = B⊗A for 2×2 matrices. Used by m4_3.
- a12 (Lemma, Appendix/A3_Swaps.v:21): swapab conjugation exchanges bcgate and acgate. Used by m4_4.
- a13_1 (Lemma, Appendix/A3_Swaps.v:28): (ccu D)† = ccu (D†). Used by m4_4.
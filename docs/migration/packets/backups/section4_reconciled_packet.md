# Section 4 — Reconciled Packet

Merged from: section4_paper_packet.md + section4_rocq_packet.md

---

## Lemma 4.1

- paper_id: Lemma 4.1
- object_type: lemma
- section: 4
- source_pages: [216, 217]
- paper_statement_summary: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. There exist 2-qubit unitaries U, V and 1-qubit unitaries P0, P1, Q0, Q1 such that |0⟩⟨0| ⊗ U_BC (P0 ⊗ Q0) V_BC + |1⟩⟨1| ⊗ U_BC (P1 ⊗ Q1) V_BC = CC(Diag(u0, u1)) if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies: [Lemma A.4, Lemma 3.2]
- rocq_files: [Main.v]
- rocq_declarations: [m4_1 (Main.v:1008)]
- rocq_helper_declarations:
    - m3_2 (Main.v:272) — used in forward direction via `apply m3_2`
    - ccu (Helpers/GateHelpers.v:12) — `Definition ccu (U : Square 2) := control (control U)`
    - diag2 — from QuantumLib
    - control — from QuantumLib
    - control_direct_sum (Helpers/MatrixHelpers.v:2023)
    - direct_sum_simplify (Helpers/MatrixHelpers.v:2086)
    - block_decomp (Helpers/MatrixHelpers.v:900)
    - block_multiply (Helpers/MatrixHelpers.v:349)
    - block_equalities (Helpers/MatrixHelpers.v:377)
    - other_unitary_decomp (Helpers/UnitaryHelpers.v:7)
    - diag2_unitary (Helpers/UnitaryHelpers.v:46)
    - notc, notc_unitary, notc_notc (Helpers/MatrixHelpers.v:2168 and QuantumLib) — used in backward direction (u0*u1=1 case)
    - a3 (Appendix/A2_UnitaryMatrices.v:10) — spectral theorem (Theorem A.3), used transitively through m3_2
    - a4 (Appendix/A2_UnitaryMatrices.v:43) — eigenpair conjugation (Lemma A.4), used transitively through m3_2
- rocq_notes: >
    The Rocq proof decomposes the 8×8 ccu matrix via `control_direct_sum` and
    `direct_sum_simplify` into block equations. The forward direction reduces to
    showing that the product P1×P0† ⊗ Q1×Q0† is conjugate to diag4(1,1,u0,u1),
    then appeals to m3_2. The backward direction constructs explicit witnesses:
    identity matrices for the u0=u1 case, and notc (CNOT) for the u0*u1=1 case.
- blueprint_label: lem:s4_1
- blueprint_uses: [lem:s3_2]
- lean_name: TwoControl.section4_lemma_4_1
- lean_file: TwoControl/Section4.lean
- statement_status: not_started
- proof_status: not_started
- extraction_confidence: high
- ambiguities: none

---

## Lemma 4.2

- paper_id: Lemma 4.2
- object_type: lemma
- section: 4
- source_pages: [217, 218]
- paper_statement_summary: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. Suppose Q is a 1-qubit unitary and let |β⟩ = Q|0⟩ and |β⊥⟩ = Q|1⟩. There exist 1-qubit unitaries P0, P1 such that I ⊗ I ⊗ |β⟩⟨β| + P0 ⊗ P1 ⊗ |β⊥⟩⟨β⊥| = CC(Diag(u0, u1)) if and only if u0 = 1 = u1.
- paper_dependencies: [Lemma A.8, Lemma 3.2]
- rocq_files: [Main.v]
- rocq_declarations: [m4_2 (Main.v:1097)]
- rocq_helper_declarations:
    - a8 (Appendix/A2_UnitaryMatrices.v:213) — Q|0⟩(Q|0⟩)† + Q|1⟩(Q|1⟩)† = I₂
    - ccu (Helpers/GateHelpers.v:12)
    - control_decomp (Helpers/MatrixHelpers.v:2078)
    - control_direct_sum (Helpers/MatrixHelpers.v:2023)
    - direct_sum_simplify (Helpers/MatrixHelpers.v:2086)
    - kron_cancel_l (Helpers/MatrixHelpers.v:186)
    - other_unitary_decomp (Helpers/UnitaryHelpers.v:7)
- rocq_notes: >
    The Rocq proof of m4_2 is substantially longer and more case-analytic than
    the paper suggests. It performs three cases:
    (1) a = 0 (top component of β is zero), proving β×β† = |1⟩⟨1| and
        β⊥×β⊥† = |0⟩⟨0|, then extracting u0=1, u1=1 by matrix entry comparison;
    (2) b = 0 (bottom component of β is zero), symmetric to case 1;
    (3) a ≠ 0 and b ≠ 0, where the proof multiplies both sides by
        |1⟩⊗|1⟩⊗β to annihilate the β⊥ term (using orthogonality β⊥†β = 0),
        then uses kron_cancel_l and entry-wise comparison.
    The backward direction is straightforward: set P0 = P1 = I₂ and use a8.
    No direct call to m3_2 appears in the Rocq proof, despite the paper listing
    Lemma 3.2 as a dependency. The Rocq proof is self-contained via entry-level
    matrix arithmetic.
- blueprint_label: lem:s4_2
- blueprint_uses: [lem:s3_2]
- lean_name: TwoControl.section4_lemma_4_2
- lean_file: TwoControl/Section4.lean
- statement_status: not_started
- proof_status: not_started
- extraction_confidence: high
- ambiguities: >
    Paper lists Lemma 3.2 as a dependency but the Rocq proof does not invoke m3_2.
    The Rocq proof uses direct matrix arithmetic instead. The blueprint_uses still
    lists lem:s3_2 to match the paper, but implementors should note the Rocq proof
    strategy diverges here.

---

## Lemma 4.3

- paper_id: Lemma 4.3
- object_type: lemma
- section: 4
- source_pages: [219, 220, 221]
- paper_statement_summary: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. There exist 2-qubit unitaries V1, V2, V3, V4 and 1-qubit unitaries P0, P1, where V1 = |0⟩⟨0| ⊗ P0 + |1⟩⟨1| ⊗ P1, such that V1_AC V2_BC V3_AC V4_BC = CC(Diag(u0, u1)) if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies: [Lemma A.27, Lemma A.4, Theorem A.3, Lemma 3.3, Lemma A.11]
- rocq_files: [Main.v]
- rocq_declarations: [m4_3 (Main.v:1398)]
- rocq_helper_declarations:
    - a27 (Appendix/A7_OtherProperties.v:11) — key structural lemma: if acgate V1 × bcgate V2 × acgate V3 × bcgate V4 = |0⟩⟨0|⊗U0 + |1⟩⟨1|⊗U1 and V1 = |0⟩⟨0|⊗P0 + |1⟩⟨1|⊗P1, then V3 also has that block form
    - a3 (Appendix/A2_UnitaryMatrices.v:10) — spectral theorem for unitaries
    - a11 (Appendix/A3_Swaps.v:14) — swap × (A ⊗ B) × swap = B ⊗ A
    - m3_3 (Main.v:504) — used in forward direction to conclude u0=u1 ∨ u0*u1=1
    - ccu (Helpers/GateHelpers.v:12)
    - acgate (Helpers/GateHelpers.v:11) — `Definition acgate (U : Square 4) := swapbc × (abgate U) × swapbc`
    - bcgate (Helpers/GateHelpers.v:10) — `Definition bcgate (U : Square 4) := I 2 ⊗ U`
    - abgate (Helpers/GateHelpers.v:9) — `Definition abgate (U : Square 4) := U ⊗ I 2`
    - swapbc (Helpers/SwapHelpers.v:7) — `Definition swapbc : Square 8 := I 2 ⊗ swap`
    - control_decomp (Helpers/MatrixHelpers.v:2078)
    - control_direct_sum (Helpers/MatrixHelpers.v:2023)
    - direct_sum_simplify (Helpers/MatrixHelpers.v:2086)
    - diag4 (Helpers/MatrixHelpers.v:49)
    - other_unitary_decomp (Helpers/UnitaryHelpers.v:7)
    - swap_swap — from QuantumLib (swap × swap = I₄)
    - swapbc_3gate (Helpers/SwapHelpers.v:137) — swapbc distributes over 3-qubit tensor
    - diag2_unitary (Helpers/UnitaryHelpers.v:46)
    - Cexp_Cmod (Helpers/AlgebraHelpers.v:813) — unit-modulus implies Cexp representation
    - bcgate_unitary (Helpers/GateHelpers.v:48)
    - σx (Pauli-X gate) — from QuantumLib
- rocq_notes: >
    This is the longest and most complex proof among the Section 4 lemmas (≈360 lines).
    Forward direction: Uses a27 to show V3 also block-decomposes as |0⟩⟨0|⊗Q0 + |1⟩⟨1|⊗Q1.
    Expands the full product, isolates blocking, computes the product
    (I₂⊗P0)×V2×(I₂⊗Q0) and its P1/Q1 counterpart, takes their ratio, applies
    spectral decomposition (a3) to Q1×Q0†, rewrites as I₂⊗D where D = diag4(d0,d1,d0,d1),
    then invokes m3_3 to conclude.
    Backward direction: Two explicit constructions:
    (1) u0=u1 case: V1=I₄, V2=swap, V3=control(diag2 1 u1), V4=swap;
    (2) u0*u1=1 case: introduces u=Cexp(θ/2), P=diag2(1/u, u),
        U=|0⟩⟨0|⊗σx + |1⟩⟨1|⊗I₂, V=control(P), and sets
        V1=V, V2=U, V3=V, V4=U†. Verifies P×P = diag2(u0,u1) and
        (I₂⊗P)×U×(I₂⊗P)×U† = control(P×P) by direct computation.
    Key Rocq-only decomposition: The product P×σx×P×σx = I₂ is an intermediate
    identity used in the backward construction (step4 in proof).
- blueprint_label: lem:s4_3
- blueprint_uses: [lem:s3_3]
- lean_name: TwoControl.section4_lemma_4_3
- lean_file: TwoControl/Section4.lean
- statement_status: not_started
- proof_status: not_started
- extraction_confidence: high
- ambiguities: none

---

## Lemma 4.4

- paper_id: Lemma 4.4
- object_type: lemma
- section: 4
- source_pages: [222]
- paper_statement_summary: Suppose u0, u1 are complex numbers with |u0| = |u1| = 1. There exist 2-qubit unitaries V1, V2, V3, V4 and 1-qubit unitaries P0, P1, where V4 = |0⟩⟨0| ⊗ P0 + |1⟩⟨1| ⊗ P1, such that V1_AC V2_BC V3_AC V4_BC = CC(Diag(u0, u1)) if and only if either u0 = u1 or u0 u1 = 1.
- paper_dependencies: [Lemma 4.3]
- rocq_files: [Main.v]
- rocq_declarations: [m4_4 (Main.v:1762)]
- rocq_helper_declarations:
    - m4_3 (Main.v:1398) — the main dependency; m4_4 reduces to m4_3 by adjoint/swap
    - a12 (Appendix/A3_Swaps.v:21) — swapab × acgate U × swapab = bcgate U
    - a13_1 (Appendix/A3_Swaps.v:28) — swapab × ccu D × swapab = ccu D
    - swapab (Helpers/SwapHelpers.v:6) — `Definition swapab : Square 8 := swap ⊗ I 2`
    - swapab_hermitian (Helpers/SwapHelpers.v:78) — swapab† = swapab
    - swapab_inverse (Helpers/SwapHelpers.v:46) — swapab × swapab = I₈
    - swapab_conj_ac (Helpers/GateHelpers.v:1337) — underlying proof for a12
    - swapab_ccu (Helpers/GateHelpers.v:86) — underlying proof for a13_1
    - acgate_adjoint (Helpers/GateHelpers.v:128) — (acgate U)† = acgate U†
    - Cmod_Cconj — from QuantumLib, Cmod(z*) = Cmod(z)
    - Cconj_mult_distr — from QuantumLib
    - control_adjoint — from QuantumLib
- rocq_notes: >
    The Rocq proof of m4_4 reduces both directions to m4_3 via conjugate-transpose
    and A-B swap. The key idea (matching the paper's remark) is:
    Take the adjoint of the product acgate V1 × bcgate V2 × acgate V3 × bcgate V4
    to get acgate V4† × bcgate V3† × acgate V2† × bcgate V1†, then conjugate by swapab
    using a12 (swapab × acgate U × swapab = bcgate U) and a13_1
    (swapab × ccu D × swapab = ccu D) to exchange AC ↔ BC gates. This
    transforms an m4_4-type decomposition (V4 has block form) into an
    m4_3-type decomposition (V1† has block form, playing the role of V1 in m4_3).
    The eigenvalue condition transfers via conjugation: u0*=u1* ∨ u0*u1*=1
    iff u0=u1 ∨ u0u1=1.
    Both forward and backward directions follow this same adjoint+swap strategy,
    each applying m4_3 on the conjugate-transposed diagonal diag2(u0*, u1*).
- blueprint_label: lem:s4_4
- blueprint_uses: [lem:s4_3]
- lean_name: TwoControl.section4_lemma_4_4
- lean_file: TwoControl/Section4.lean
- statement_status: not_started
- proof_status: not_started
- extraction_confidence: high
- ambiguities: >
    The paper states this "follows easily from Lemma 4.3 by exchanging the roles
    of A and B and considering the conjugate transpose of the product." The Rocq
    proof confirms this strategy exactly, using adjoint + swapab conjugation.

---

## Rocq-only helper notes

### Gate definitions (Helpers/GateHelpers.v)
- `abgate U := U ⊗ I 2` — gate on qubits A,B (line 9)
- `bcgate U := I 2 ⊗ U` — gate on qubits B,C (line 10)
- `acgate U := swapbc × (abgate U) × swapbc` — gate on qubits A,C (line 11)
- `ccu U := control (control U)` — doubly controlled unitary (line 12)

### Swap definitions (Helpers/SwapHelpers.v)
- `swapab := swap ⊗ I 2` — swaps qubits A and B (line 6)
- `swapbc := I 2 ⊗ swap` — swaps qubits B and C (line 7)

### Key structural helpers used across Section 4
- `block_decomp` (MatrixHelpers.v:900) — decomposes 2n×2n matrix into 4 blocks
- `block_multiply` (MatrixHelpers.v:349) — multiplies two block-decomposed matrices
- `block_equalities` (MatrixHelpers.v:377) — extracts block-wise equalities
- `direct_sum_simplify` (MatrixHelpers.v:2086) — A⊕B = C⊕D implies A=C ∧ B=D
- `control_direct_sum` (MatrixHelpers.v:2023) — control A = I⊕A
- `control_decomp` (MatrixHelpers.v:2078) — control A = |0⟩⟨0|⊗I + |1⟩⟨1|⊗A
- `other_unitary_decomp` (UnitaryHelpers.v:7) — U×U† = I for unitaries
- `diag2_unitary` (UnitaryHelpers.v:46) — diag2(c1,c2) is unitary if |c1|=|c2|=1
- `kron_cancel_l` (MatrixHelpers.v:186) — left cancellation in tensor products
- `Cexp_Cmod` (AlgebraHelpers.v:813) — |c|=1 implies c=Cexp(θ) for some θ

### Appendix lemmas used by Section 4
- `a3` (A2_UnitaryMatrices.v:10) — Spectral theorem: unitary U = V×D×V† with D diagonal
- `a4` (A2_UnitaryMatrices.v:43) — Eigenpair conjugation under unitary similarity
- `a8` (A2_UnitaryMatrices.v:213) — Q|0⟩(Q|0⟩)† + Q|1⟩(Q|1⟩)† = I₂ for unitary Q
- `a11` (A3_Swaps.v:14) — swap × (A⊗B) × swap = B⊗A for 2×2 matrices
- `a12` (A3_Swaps.v:21) — swapab × acgate U × swapab = bcgate U
- `a13_1` (A3_Swaps.v:28) — swapab × ccu D × swapab = ccu D
- `a27` (A7_OtherProperties.v:11) — If V1 has block form and acV1×bcV2×acV3×bcV4 = |0⟩⟨0|⊗U0 + |1⟩⟨1|⊗U1, then V3 also has block form

### Section 3 lemmas used by Section 4
- `m3_2` (Main.v:272) — used by m4_1, eigenvalue condition for P⊗Q ∼ diag4(1,1,u0,u1)
- `m3_3` (Main.v:504) — used by m4_3, eigenvalue condition for (I⊗P)×control(diag2) ∼ diag4(c,d,c,d)

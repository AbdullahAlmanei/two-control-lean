# Statement Symbol Inventory

## Symbols that must exist before theorem stubs compile

### UnitComplex

- kind: definition
- appears_in_sections: [3, 4, 5, 6, 7]
- appears_in_objects: [Lemma 3.1, Lemma 3.2, Lemma 3.3, Lemma 4.1, Lemma 4.2, Lemma 4.3, Lemma 4.4, Lemma 5.1, Lemma 6.1, Lemma 6.2, Lemma 6.3, Lemma 6.4, Lemma 7.1, Lemma 7.2, Lemma 7.3, Theorem 7.4, Corollary 7.5]
- planned_home: mathlib
- reason_needed: Every theorem statement begins with "Suppose u₀, u₁ are complex numbers with |u₀| = |u₁| = 1". This is the type of unit-norm complex numbers. Mathlib provides `Metric.sphere (0 : ℂ) 1` or `circle` (the unit circle as a subgroup of ℂˣ). A local abbreviation or notation wrapper may be convenient but is not strictly required.
- notes: Mathlib's `circle` lives in `Analysis.SpecialFunctions.Complex.Circle`. The hypothesis can also be expressed inline as `(hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)` without introducing a separate type.

### Matrix.unitaryGroup

- kind: existing_mathlib_symbol
- appears_in_sections: [3, 4, 5, 6, 7]
- appears_in_objects: [Lemma 3.1, Lemma 3.2, Lemma 3.3, Lemma 4.1, Lemma 4.2, Lemma 4.3, Lemma 4.4, Lemma 5.1, Lemma 6.1, Lemma 6.2, Lemma 6.3, Lemma 6.4, Lemma 7.1, Lemma 7.2, Theorem 7.4, Corollary 7.5]
- planned_home: mathlib
- reason_needed: All theorem statements quantify over unitary matrices of various sizes (2×2, 4×4, 8×8). Mathlib provides `Matrix.unitaryGroup (Fin n) ℂ` (notation `unitary (Matrix (Fin n) (Fin n) ℂ)`).
- notes: Alternatively, the statements can use `(U : Matrix (Fin n) (Fin n) ℂ)` with a hypothesis `U ∈ Matrix.unitaryGroup (Fin n) ℂ` or `U.IsUnitary`. The choice affects downstream ergonomics.

### diag2

- kind: definition
- appears_in_sections: [3, 4, 5, 6, 7]
- appears_in_objects: [Lemma 3.1, Lemma 3.2, Lemma 3.3, Lemma 4.1, Lemma 4.2, Lemma 4.3, Lemma 4.4, Lemma 5.1, Lemma 6.2, Lemma 6.3, Lemma 6.4, Lemma 7.1, Lemma 7.2, Lemma 7.3, Theorem 7.4, Corollary 7.5]
- planned_home: `TwoControl/Definitions.lean`
- reason_needed: Diag(u₀, u₁) is a 2×2 diagonal matrix with entries u₀, u₁. This appears in every CC(Diag(u₀, u₁)) expression. Mathlib's `Matrix.diagonal` takes a function `Fin n → ℂ`; a convenience wrapper `diag2 u₀ u₁` avoids repeated boilerplate for the 2×2 case.
- notes: Rocq uses `diag2` as a dedicated constructor. The Lean definition should satisfy `diag2 u₀ u₁ = Matrix.diagonal ![u₀, u₁]`.

### controlledGate (C)

- kind: definition
- appears_in_sections: [3, 4, 5, 6, 7]
- appears_in_objects: [Lemma 3.3, Lemma 4.1, Lemma 4.3, Lemma 6.2, Lemma 6.3, Lemma 7.1]
- planned_home: `TwoControl/Definitions.lean`
- reason_needed: C(Diag(u₀, u₁)) is the 4×4 controlled-U gate: the 2×2 block-diagonal matrix |0⟩⟨0| ⊗ I₂ + |1⟩⟨1| ⊗ U. Appears directly in several theorem statements and is a building block for CC.
- notes: Should be defined as `controlledGate (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ` using the block diagonal structure. Rocq calls this `control`.

### doublyControlledGate (CC)

- kind: definition
- appears_in_sections: [3, 4, 5, 6, 7]
- appears_in_objects: [Lemma 4.1, Lemma 4.2, Lemma 4.3, Lemma 4.4, Lemma 5.1, Lemma 6.2, Lemma 6.3, Lemma 6.4, Lemma 7.1, Lemma 7.2, Theorem 7.4, Corollary 7.5]
- planned_home: `TwoControl/Definitions.lean`
- reason_needed: CC(U) is the 8×8 doubly-controlled gate: |0⟩⟨0| ⊗ I₄ + |1⟩⟨1| ⊗ C(U). This is the central object of the entire paper — every main theorem is about when CC(Diag(u₀, u₁)) can be decomposed.
- notes: Rocq calls this `ccu`. Corollary 7.5 uses CC(U) for a general 2×2 unitary U (not just diagonal), so the definition must accept any 2×2 unitary.

### kroneckerProduct (⊗)

- kind: notation_wrapper
- appears_in_sections: [3, 4, 5, 6]
- appears_in_objects: [Lemma 3.1, Lemma 3.2, Lemma 3.3, Lemma 4.1, Lemma 4.2, Lemma 6.1, Lemma 6.2, Lemma 6.3]
- planned_home: mathlib
- reason_needed: The Kronecker (tensor) product of matrices appears in many statement-level expressions: Diag(u₀, u₁) ⊗ I₂ ⊗ I₂, P ⊗ Q, |0⟩⟨0| ⊗ V₀₀, I ⊗ I ⊗ |β⟩⟨β|, etc.
- notes: Mathlib provides `Matrix.kroneckerMap` and the notation `⊗ₖ` via `Matrix.instKron`. The `⊗` notation may need a local scoped notation or reliance on mathlib's `⊗ₖ`. Verify compatibility with matrix dimension inference for Fin types.

### ket0 / ket1

- kind: definition
- appears_in_sections: [4, 6]
- appears_in_objects: [Lemma 4.1, Lemma 4.2, Lemma 4.3, Lemma 4.4, Lemma 6.1, Lemma 6.2, Lemma 6.3, Lemma 6.4]
- planned_home: `TwoControl/Definitions.lean`
- reason_needed: The computational basis vectors |0⟩ and |1⟩ (as column vectors in ℂ²) appear in multiple theorem statements via outer products |0⟩⟨0|, |1⟩⟨1|, and in expressions like V(|x⟩ ⊗ |0⟩). Needed to express block structure and projector conditions.
- notes: Define as `ket0 : Fin 2 → ℂ := ![1, 0]` and `ket1 : Fin 2 → ℂ := ![0, 1]`. These are `Pi.single` / `stdBasisVec` in mathlib, but named definitions improve readability.

### ketbra (|i⟩⟨j| / outer product)

- kind: definition
- appears_in_sections: [3, 4, 5, 6]
- appears_in_objects: [Lemma 3.1, Lemma 4.1, Lemma 4.2, Lemma 4.3, Lemma 4.4, Lemma 5.1, Lemma 6.2, Lemma 6.3, Lemma 6.4]
- planned_home: `TwoControl/Definitions.lean`
- reason_needed: The outer product |v⟩⟨w| produces a matrix from two vectors. Expressions like |0⟩⟨0| ⊗ V₀₀ + |1⟩⟨1| ⊗ V₁₁ pervade the theorem statements. Needed for block-diagonal decomposition conditions and the controlled-gate structures in Lemmas 4.3, 4.4, 6.2, 6.3, 6.4.
- notes: Define as `ketbra (v w : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := vecMulVec v (star w)` or `Matrix.col v * Matrix.row (star w)`. Mathlib's `Matrix.stdBasisMatrix` covers the case of basis vectors but not general vectors.

### qubitPairEmbed (U^{AB}, U^{AC}, U^{BC})

- kind: definition
- appears_in_sections: [4, 5, 6, 7]
- appears_in_objects: [Lemma 4.3, Lemma 4.4, Lemma 5.1, Lemma 6.2, Lemma 6.3, Lemma 6.4, Lemma 7.1, Lemma 7.2, Theorem 7.4]
- planned_home: `TwoControl/Definitions.lean`
- reason_needed: The notation U^{XY} embeds a 4×4 (2-qubit) unitary into the 8×8 (3-qubit) space by acting on qubits X, Y and tensoring with identity on the third qubit. This appears in every statement from Section 4.3 onward. Three variants are needed: AB (qubits 0,1), AC (qubits 0,2), BC (qubits 1,2).
- notes: The embedding involves tensor products and possibly qubit permutations. For BC: U^{BC} = I₂ ⊗ U. For AC: requires a SWAP-based conjugation or direct permutation embedding. For AB: U^{AB} = U ⊗ I₂. Rocq implements these via kron and qubit-swap helpers. Consider defining three named functions `embedAB`, `embedBC`, `embedAC` or a single parametric `embedQubitPair`.

### IsEntangled

- kind: predicate
- appears_in_sections: [6]
- appears_in_objects: [Lemma 6.1, Lemma 6.2, Lemma 6.4]
- planned_home: `TwoControl/Definitions.lean`
- reason_needed: Lemma 6.1 states a three-way case analysis where the first case is "V(|x⟩ ⊗ |0⟩) is entangled", i.e., the resulting 4-dimensional vector cannot be written as a tensor product of two 2-dimensional vectors. This predicate appears in the statement of Lemma 6.1 and is implicitly used in Lemmas 6.2 and 6.4.
- notes: Define as the negation of being a product state: `IsEntangled (v : Fin 4 → ℂ) : Prop := ¬ ∃ (a b : Fin 2 → ℂ), v = kroneckerVec a b`. Alternatively, define `IsProductState` and negate it. Rocq does not appear to have a named predicate; it uses the structural negation inline.

### gateSetG1

- kind: definition
- appears_in_sections: [7]
- appears_in_objects: [Lemma 7.2, Theorem 7.4, Corollary 7.5]
- planned_home: `TwoControl/Definitions.lean`
- reason_needed: G₁ is the set of 3-qubit unitaries that act nontrivially on at most one qubit (i.e., are of the form U ⊗ I ⊗ I, I ⊗ U ⊗ I, or I ⊗ I ⊗ U for 2×2 unitaries U). Appears in the statements of the main theorem and its supporting lemma.
- notes: The Rocq formalization sidesteps G₁ by using a stronger hypothesis (exactly four TwoQubitGate factors). If the Lean formalization follows the paper, G₁ must be defined. If it follows Rocq, G₁ is not needed at the statement level. This decision is flagged as unresolved in the generation packets for Lemma 7.2 and Theorem 7.4.

### gateSetG2

- kind: definition
- appears_in_sections: [7]
- appears_in_objects: [Lemma 7.2, Theorem 7.4, Corollary 7.5]
- planned_home: `TwoControl/Definitions.lean`
- reason_needed: G₂ is the set of 3-qubit unitaries that act nontrivially on at most two qubits: any U^{AB}, U^{AC}, or U^{BC}, plus all of G₁. Appears in the main theorem statement. The set difference G₂ \ G₁ represents genuine 2-qubit interactions.
- notes: Same unresolved question as gateSetG1. If the Lean formalization uses TwoQubitGate factors (Rocq approach), a simpler type of "list of 2-qubit gates with qubit-pair labels" suffices, and G₂/G₁ as sets are not needed.

### TwoQubitGate (alternative to G₁/G₂)

- kind: definition
- appears_in_sections: [7]
- appears_in_objects: [Lemma 7.2, Theorem 7.4, Corollary 7.5]
- planned_home: `TwoControl/Definitions.lean`
- reason_needed: In the Rocq formalization, the hypothesis of Theorem 7.4 is stated in terms of a product of exactly four TwoQubitGate factors, each labelled with a qubit pair. If the Lean formalization follows the Rocq approach, this type/structure replaces G₁ and G₂.
- notes: This is mutually exclusive with gateSetG1/gateSetG2 at the statement level. One of the two formulations must be chosen. The generation packets flag this as an unresolved formalization question.

### canonicalPairSet (R(u₀, u₁))

- kind: definition
- appears_in_sections: [7]
- appears_in_objects: [Lemma 7.2, Lemma 7.3, Theorem 7.4]
- planned_home: `TwoControl/Definitions.lean`
- reason_needed: R(u₀, u₁) = {(u₀, u₁), (1, u₀*u₁)} is defined in the Section 7 preamble and appears in the statements of Lemmas 7.2 and 7.3. It captures the two possible parameter pairs arising from the swap reduction in Lemma 7.1.
- notes: Define as a `Set (ℂ × ℂ)` or as a `Finset (ℂ × ℂ)`, or simply inline the membership as a disjunction `(u₂, u₃) = (u₀, u₁) ∨ (u₂, u₃) = (1, star u₀ * u₁)`. The Blueprint uses inline set notation. The Lean definition should use `starRingEnd ℂ` for conjugation.

### Matrix.det

- kind: existing_mathlib_symbol
- appears_in_sections: [7]
- appears_in_objects: [Corollary 7.5]
- planned_home: mathlib
- reason_needed: Corollary 7.5 states the condition "det(U) = 1" for the eigenvalue product. Mathlib provides `Matrix.det`.
- notes: Available in `Mathlib.LinearAlgebra.Matrix.Determinant`.

### Matrix.eigenvalues / HasEigenvalue

- kind: existing_mathlib_symbol
- appears_in_sections: [3, 7]
- appears_in_objects: [Lemma 3.2, Lemma 3.3, Corollary 7.5]
- planned_home: mathlib
- reason_needed: Lemma 3.2 states "the eigenvalues of P ⊗ Q are {1, 1, u₀, u₁}". Lemma 3.3 states eigenvalues of a product are {c, c, d, d}. Corollary 7.5 says "eigenvalues of U are equal". Mathlib provides `Module.End.HasEigenvalue` and related API, but the Rocq approach avoids eigenvalue multisets by using explicit diagonalisation (∃ V D, M = V * D * V†).
- notes: If following the Rocq approach, the eigenvalue condition is replaced by an explicit diagonalisation hypothesis, and the mathlib eigenvalue API is not needed at statement level. If following the paper, a multiset-based eigenvalue characterisation is needed. The Rocq approach is simpler for formal proofs.

### Matrix.IsHermitian / star / adjoint

- kind: existing_mathlib_symbol
- appears_in_sections: [3, 4, 5, 6, 7]
- appears_in_objects: [Lemma 3.1, Lemma 5.1, Lemma 6.2, Lemma 6.3, Lemma 7.1, Corollary 7.5]
- planned_home: mathlib
- reason_needed: The conjugate transpose (†) of matrices appears implicitly in "unitary" conditions and explicitly in expressions like U†, V†, and P₀†. Mathlib provides `Matrix.conjTranspose` with notation `Aᴴ`.
- notes: Pervasive but standard. No project definition needed.

### identityMatrix (I_n)

- kind: existing_mathlib_symbol
- appears_in_sections: [3, 4, 5, 6]
- appears_in_objects: [Lemma 3.1, Lemma 3.3, Lemma 4.1, Lemma 4.2, Lemma 4.3, Lemma 4.4, Lemma 6.2, Lemma 6.3, Lemma 6.4]
- planned_home: mathlib
- reason_needed: The identity matrix I₂, I₄ appears in tensor products (Diag(u₀,u₁) ⊗ I₂ ⊗ I₂) and in controlled-gate definitions (|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U). Mathlib uses `(1 : Matrix (Fin n) (Fin n) ℂ)`.
- notes: Standard mathlib. No project definition needed. Dimension inference via `Fin n` should handle all cases.

### matMul (matrix multiplication)

- kind: existing_mathlib_symbol
- appears_in_sections: [3, 4, 5, 6, 7]
- appears_in_objects: [all]
- planned_home: mathlib
- reason_needed: Matrix multiplication (·) appears in every decomposition equation. Mathlib provides `Matrix.mul` with `*` notation via `instMul`.
- notes: Standard. No project definition needed.

### Commute

- kind: existing_mathlib_symbol
- appears_in_sections: [3]
- appears_in_objects: [Lemma 3.1]
- planned_home: mathlib
- reason_needed: Lemma 3.1 states that U "commutes with" a specific matrix. Mathlib provides `Commute` or this can be expressed as `A * B = B * A`.
- notes: Likely expressed inline as an equation rather than using the `Commute` predicate.

### mulVec (matrix-vector product)

- kind: existing_mathlib_symbol
- appears_in_sections: [4, 6]
- appears_in_objects: [Lemma 4.2, Lemma 6.1, Lemma 6.2, Lemma 6.3]
- planned_home: mathlib
- reason_needed: Expressions like V(|x⟩ ⊗ |0⟩) and Q|0⟩ apply a matrix to a vector. Mathlib provides `Matrix.mulVec`.
- notes: Standard. The notation `M *ᵥ v` is available.

### kroneckerVec (tensor product of vectors)

- kind: definition
- appears_in_sections: [4, 6]
- appears_in_objects: [Lemma 4.2, Lemma 6.1, Lemma 6.2, Lemma 6.3, Lemma 6.4]
- planned_home: `TwoControl/Definitions.lean`
- reason_needed: Expressions like |x⟩ ⊗ |0⟩ form the Kronecker product of two column vectors to produce a vector in the tensor product space. This appears in Lemma 6.1's entanglement condition and in Lemma 4.2. Distinct from the matrix Kronecker product.
- notes: Define as `kroneckerVec (v : Fin m → ℂ) (w : Fin n → ℂ) : Fin (m * n) → ℂ`. Mathlib may not have a direct vector Kronecker product; it would need to be defined or expressed through `TensorProduct` and basis identification.

## Symbols that appear only in proof sketches, not theorem statements

### SWAP

- notes: The swap gate (permutation matrix swapping two qubits) appears in proof constructions for Lemma 4.3 backward direction and as a tool in Lemma 7.2 proof steps 3–4 via swap conjugation identities (Lemma A.12). Not referenced in any theorem statement.

### pauliX (σ_x)

- notes: The Pauli X matrix appears only in the backward-direction proof of Lemma 4.3 as a component of the explicit witness construction (V₂ = |0⟩⟨0| ⊗ σ_x + |1⟩⟨1| ⊗ I). Not in any theorem statement.

### CNOT

- notes: The CNOT gate appears in the reverse direction proof of Lemma 4.1 as "CNOT-based witnesses" and in Section 5 reverse-direction proof notes. Not referenced in theorem statements.

### Cexp (complex exponential)

- notes: The complex exponential e^{iθ} appears in the backward-direction proof of Lemma 4.3 for constructing witnesses via u = e^{iθ/2}. Not in any theorem statement.

### spectralTheorem (Theorem A.3)

- notes: The spectral theorem for unitary matrices (diagonalization as U = V D V†) is used in proofs of Lemma 3.2, 3.3, 4.3, and Corollary 7.5. In Corollary 7.5 it appears at the boundary of statement vs. proof: the proof begins by diagonalising U, which could be considered a proof step rather than a statement ingredient. The eigenvalue condition in the statement of Corollary 7.5 can be expressed without invoking the spectral theorem directly.

### directSum (⊕)

- notes: The direct sum of matrices appears in proof decompositions (e.g., Lemma 4.1 proof: "decompose CC(Diag(u₀,u₁)) via direct sum"). Not in theorem statements.

### AppendixLemmas (A.10–A.33)

- notes: A large collection of Appendix helper lemmas (A.10, A.12, A.13, A.17, A.18, A.19, A.22, A.23, A.24, A.25, A.26, A.27, A.28, A.29, A.30, A.31, A.32, A.33) appear exclusively in proof sketches. They provide structural decomposition results, swap identities, and block-diagonal extraction lemmas. None appear in theorem statements. They are excluded from first-Blueprint nodes under the first-Blueprint policy.

### blockDecomp / blockMultiply / blockEqualities

- notes: Rocq-specific helper infrastructure for block matrix manipulation. Appears only in proof machinery for Lemma 3.1 and Lemma 5.1. Not in theorem statements.

### permutationMatrix

- notes: Permutation matrices (e.g., the matrix swapping second and fourth basis vectors) appear in proof constructions for Lemma 5.1 backward direction. Not in theorem statements.

### scalarMatrix

- notes: Scalar multiples of identity (u₀ · I₄) appear in proof expansions (e.g., Lemma 3.1 proof). Not in theorem statements. Expressible via mathlib's `Matrix.scalar` or `smul`.

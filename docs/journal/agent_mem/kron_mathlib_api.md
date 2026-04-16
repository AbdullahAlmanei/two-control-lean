# Kronecker Product & Block-Matrix API Exploration

## Custom `kron` Definition

**Location**: [TwoControl/Prelude.lean](TwoControl/Prelude.lean#L32-L34)

```lean
noncomputable def kron (A : Square m) (B : Square n) : Square (m * n) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.kroneckerMap (· * ·) A B)
```

The definition reindexes the Kronecker product from `Fin m × Fin n` indexing to `Fin (m*n)` indexing using `finProdFinEquiv`.

---

## 1. MATHLIB KRONECKER PRODUCT API (`Matrix.kroneckerMap`)

### Main Definition
- **`Matrix.kroneckerMap : (α → β → γ) → Matrix l m α → Matrix n p β → Matrix (l × n) (m × p) γ`**
  - Generalized Kronecker product: takes an arbitrary bilinear map `f` and two matrices
  - **Specialization for multiplication**: `Matrix.kronecker` = `kroneckerMap (· * ·)`
  - Notation: `A ⊗ₖ B` (uses `⊗ₖ` notation)

### Key Lemmas for Multiplication & Composition

**Associativity** (with associative operations):
- `Matrix.kroneckerMap_assoc`: $(A ⊗ B) ⊗ C = A ⊗ (B ⊗ C)$ (modulo reindexing with `Equiv.prodAssoc`)
- Uses `Equiv.prodAssoc : (l × n) × q ≃ l × (n × q)` for index reassociation

**Distributivity over Addition**:
- `Matrix.kroneckerMapBilinear`: When `f` is bilinear, `kroneckerMap f` is also bilinear
  - Implies: $(A₁ + A₂) ⊗ B = A₁ ⊗ B + A₂ ⊗ B$
  - And: $A ⊗ (B₁ + B₂) = A ⊗ B₁ + A ⊗ B₂$

**Trace Distribution**:
- `Matrix.trace_kroneckerMapBilinear`: $\text{trace}(A ⊗ B) = \text{trace}(A) · \text{trace}(B)$

**Determinant Compositivity**:
- `Matrix.det_kroneckerMapBilinear`: $\det(A ⊗ B) = (\det A)^p · (\det B)^m$ (for m×m and p×p matrices)

**Zero Properties**:
- `Matrix.zero_kronecker`: $0 ⊗ B = 0$  
- `Matrix.kronecker_zero`: $A ⊗ 0 = 0$

### Application Rules

- `Matrix.kroneckerMapBilinear_apply_apply`: Gives simp-normal form for applying `kroneckerMap f` with bilinear `f`
- `Matrix.kronecker_apply`: $(A ⊗ₖ B)[(i₁, j₁), (i₂, j₂)] = (A[i₁, i₂]) * (B[j₁, j₂])$ 

---

## 2. MATRIX REINDEXING (`Matrix.reindex`)

### Definition
- **`Matrix.reindex : (m ≃ m') → (n ≃ n') → Matrix m n α → Matrix m' n' α`**
  - Takes two equivalences for row and column index spaces
  - Returns a definitionally equal matrix with reindexed entries

### Key Property
- **`reindex_apply`** (simp lemma): `(reindex eₘ eₙ M) i j = M (eₘ.symm i) (eₙ.symm j)`
- **Preserves operations**: `reindex` is an algebra homomorphism
  - Preserves addition, multiplication, scalar multiplication, transpose, conjugation
  - Useful for converting between different index representations

### Critical Interaction
- **`Matrix.reindex_mul`**: Reindexing distributes over matrix multiplication (with compatible indices)
- Combined with `kroneckerMap`, enables transforming `Fin (m*n)` indexing back to `Fin m × Fin n` for analysis

---

## 3. OUTER PRODUCTS & `vecMulVec`

### Definition
- **`Matrix.vecMulVec : (n → α) → (m → α) → Matrix m n α`**
- Defined as: `Matrix.col v * Matrix.row w` (outer product of column then row)
- For complex matrices with conjugation: `ketbra v w := Matrix.vecMulVec v (starRingEnd ℂ w)`

### Lemmas for Block Decomposition
- **`Matrix.vecMulVec_apply`**: `(vecMulVec v w) i j = v i * w j`
- Used to express projectors: `proj0 := ketbra ket0 ket0` where `ket0 = fun _ => [1, 0]`
- Key for block-diagonal decomposition with standard basis: 
  - Block matrices via: $U = |0⟩⟨0| ⊗ V₀₀ + |0⟩⟨1| ⊗ V₀₁ + |1⟩⟨0| ⊗ V₁₀ + |1⟩⟨1| ⊗ V₁₁$

### Related Simp Lemmas
- `Matrix.vecMulVec_zero`: $v ⊗ 0 = 0$
- `Matrix.zero_vecMulVec`: $0 ⊗ w = 0$
- `Matrix.vecMulVec_add`: Bilinearity in both arguments

---

## 4. DIAGONAL MATRICES & LEMMAS

### Core Definition
- **`Matrix.diagonal : (n → α) → Matrix n n α`**
- Stored in [Definitions.lean](TwoControl/Definitions.lean#L11-L12): `diag2 c₀ c₁ := Matrix.diagonal ![c₀, c₁]`

### Fin-Specific Operations
- **`Fin.divNat` and `Fin.modNat`** (used in [Definitions.lean](TwoControl/Definitions.lean#L40)):
  - `ij.divNat`: For `ij : Fin (m*n)`, compute index in first qubit $= ⌊ ij / n ⌋$
  - `ij.modNat`: For `ij : Fin (m*n)`, compute index in second qubit $= ij \mod n$
  - Used to index `kronVec v w = fun ij => v ij.divNat * w ij.modNat`

### Diagonal Multiplication Compatibility
- `Matrix.diagonal_mul`: $\text{Diag}(d) · A$ scales each row $i$ by $d_i$
- `Matrix.mul_diagonal`: $A · \text{Diag}(d)$ scales each column $j$ by $d_j$
- Critical for extracting block structures from commutation relations

### Trace & Determinant
- trace distributes over kronecker: $\text{trace}(A ⊗ B) = (\text{trace} A) · (\text{trace} B)$
- det is multiplicative: $\det(A ⊗ B) = (\det A)^{\dim B} · (\det B)^{\dim A}$

---

## 5. EQUIVALENCES & INDEX CONVERSION: `finProdFinEquiv`

### Definition & Location
- **`finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)`**
- Converts between paired-index and flattened-index representations
- Essential in custom `kron` definition to go from Mathlib's `kroneckerMap` output to standard `Fin (m*n)` indexing

### Implementation Strategy 
- Encodes `(i : Fin m, j : Fin n)` to `⟨i.val * n + j.val⟩ : Fin (m*n)`
- Provides `.symm` for the inverse: decomposes `k : Fin (m*n)` back to `(k / n, k % n)`
- **Related**: `Equiv.prodAssoc` for three-way tensor products

### Reindexing Lemmas
- `Matrix.reindex_apply` with `finProdFinEquiv` allows extracting block matrices
- Enables converting block-diagonal structures from the flattened indexing back to structured form

---

## 6. EXISTING WORKSPACE HELPERS

### Custom Definitions in TwoControl

**Quantum gates** ([Definitions.lean](TwoControl/Definitions.lean)):
- `ketbra (v w : Vec n) : Square n := Matrix.vecMulVec v (star w)` — outer products
- `proj0, proj1 : Square 2` — computational basis projectors
- `controlledGate (U : Square 2) : Square 4 := proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ U` — controlled gate
- `ccu (U : Square 2) : Square 8` — doubly controlled gate
- `abgate, bcgate, acgate` — qubit pair embeddings in 3-qubit space

**Diagonal helpers**:
- `diag2 c₀ c₁` — 2×2 diagonal matrix
- `diag4 c₀ c₁ c₂ c₃` — 4×4 diagonal matrix

**Vector kronecker product**:
- `kronVec (v : Vec m) (w : Vec n) : Vec (m*n) := fun ij => v ij.divNat * w ij.modNat`

### Section 3 Lemmas (no proofs yet)
- Three main lemmas set up block-diagonal decomposition framework
- Statements in [Section3.lean](TwoControl/Section3.lean#L7-L50): Lemmas 3.1, 3.2, 3.3

---

## 7. BLOCK-MATRIX DECOMPOSITION WORKFLOW

### Available Operators for Proofs

1. **Kronecker expansion**: Use `Matrix.kroneckerMap_apply` to evaluate entries elementwise
2. **Reindexing transparency**: `Matrix.reindex_apply` makes index conversions automatic in simp
3. **Bilinearity**: Exploit `Matrix.kroneckerMapBilinear` for distributivity tricks
4. **Diagonal scaling**: Use `Matrix.diagonal_mul` and `Matrix.mul_diagonal` to extract scalar factors
5. **Basis projections**: Use `vecMulVec` with characteristic vectors to isolate blocks

### Theorem Proof Strategy (from documentation)

For commutativity characterization (Lemma 3.1):
- Decompose $U$ into four 4×4 blocks via Kronecker basis decomposition
- Express $\text{Diag}(u₀, u₁) ⊗ I₂ ⊗ I₂$ in block-diagonal form
- Compute $U · W$ and $W · U$ using block multiplication
- Extract component-wise equalities
- When $u₀ ≠ u₁$, scalar cancellation forces off-diagonal blocks to zero
- Unitarity recovered from $U^† U = I$ via block analysis

---

## KEY MATHLIB LEMMAS TO IMPORT

```lean
import Mathlib.LinearAlgebra.Matrix.Kronecker    -- kroneckerMap, bilinearity
import Mathlib.LinearAlgebra.Matrix.Basic       -- vecMulVec, row/col operations
import Mathlib.LinearAlgebra.Matrix.Diagonal    -- diagonal matrix lemmas
import Mathlib.Data.Fin.Basic                  -- Fin.divNat, Fin.modNat
import Mathlib.Data.Fin.Prod                   -- finProdFinEquiv (if available)
import Mathlib.LinearAlgebra.Matrix.ConjTranspose -- for star/conjugate
```

---

## SIMP LEMMAS THAT SHOULD HELP

- `Matrix.kronecker_apply` — expand inner products
- `Matrix.reindex_apply` — simplify index conversions
- `Matrix.vecMulVec_apply` — expand outer products
- `Matrix.diagonal_apply` — evaluate diagonal entries
- `Matrix.mul_apply` — expand matrix multiplication
- Various `Fin` arithmetic lemmas for `divNat`, `modNat` simplification

---

## WORKPLAN FINDINGS FOR SECTION6_LEMMA_6_2

See `/memories/session/section6_lemma_6_2_exploration.md`

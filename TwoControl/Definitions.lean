import TwoControl.Prelude

open scoped ComplexOrder
open Matrix

namespace TwoControl

/-! ## Diagonal matrix constructors -/

/-- `diag2 c₀ c₁` is the 2×2 diagonal matrix `Diag(c₀, c₁)`. -/
def diag2 (c₀ c₁ : ℂ) : Square 2 :=
  Matrix.diagonal ![c₀, c₁]

/-- `diag4 c₀ c₁ c₂ c₃` is the 4×4 diagonal matrix. -/
def diag4 (c₀ c₁ c₂ c₃ : ℂ) : Square 4 :=
  Matrix.diagonal ![c₀, c₁, c₂, c₃]

/-! ## Computational basis vectors (kets) -/

def ket0 : Vec 2 := ![1, 0]
def ket1 : Vec 2 := ![0, 1]

/-! ## Outer product (ketbra) -/

/-- `ketbra v w` is the matrix `|v⟩⟨w|`, i.e. the outer product `v * wᴴ`. -/
noncomputable def ketbra (v w : Vec n) : Square n :=
  Matrix.vecMulVec v (star w)

/-- Projector `|0⟩⟨0|` as a 2×2 matrix. -/
noncomputable def proj0 : Square 2 := ketbra ket0 ket0

/-- Projector `|1⟩⟨1|` as a 2×2 matrix. -/
noncomputable def proj1 : Square 2 := ketbra ket1 ket1

/-! ## Kronecker product of vectors -/

/-- Kronecker product of two vectors, producing a vector in the tensor product space.
    This maps `(Fin m → ℂ) → (Fin n → ℂ) → (Fin (m * n) → ℂ)`. -/
def kronVec (v : Vec m) (w : Vec n) : Vec (m * n) :=
  fun ij => v ij.divNat * w ij.modNat

/-! ## Controlled gate (C) -/

/-- The controlled-U gate: a 4×4 matrix acting on 2 qubits.
    `C(U) = |0⟩⟨0| ⊗ I₂ + |1⟩⟨1| ⊗ U`
    where the first qubit is the control. -/
noncomputable def controlledGate (U : Square 2) : Square 4 :=
  proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ U

/-! ## Doubly controlled gate (CC) -/

/-- The doubly-controlled-U gate: an 8×8 matrix acting on 3 qubits.
    `CC(U) = |0⟩⟨0| ⊗ I₄ + |1⟩⟨1| ⊗ C(U)` -/
noncomputable def ccu (U : Square 2) : Square 8 :=
  proj0 ⊗ₖ (1 : Square 4) + proj1 ⊗ₖ controlledGate U

/-! ## Qubit-pair embeddings (U^{AB}, U^{BC}, U^{AC}) -/

/-- Embed a 4×4 gate on qubits A,B into the 8×8 space:
    `U^{AB} = U ⊗ I₂` -/
noncomputable def abgate (U : Square 4) : Square 8 :=
  U ⊗ₖ (1 : Square 2)

/-- Embed a 4×4 gate on qubits B,C into the 8×8 space:
    `U^{BC} = I₂ ⊗ U` -/
noncomputable def bcgate (U : Square 4) : Square 8 :=
  (1 : Square 2) ⊗ₖ U

/-! ## SWAP gates -/

/-- The 4×4 SWAP gate that exchanges two qubits. -/
def swap2 : Square 4 :=
  Matrix.of ![![1, 0, 0, 0],
              ![0, 0, 1, 0],
              ![0, 1, 0, 0],
              ![0, 0, 0, 1]]

/-- SWAP on qubits A,B in 3-qubit space: `SWAP_{AB} = swap ⊗ I₂` -/
noncomputable def swapab : Square 8 := swap2 ⊗ₖ (1 : Square 2)

/-- SWAP on qubits B,C in 3-qubit space: `SWAP_{BC} = I₂ ⊗ swap` -/
noncomputable def swapbc : Square 8 := (1 : Square 2) ⊗ₖ swap2

/-- Embed a 4×4 gate on qubits A,C into the 8×8 space:
    `U^{AC} = SWAP_{BC} × U^{AB} × SWAP_{BC}` -/
noncomputable def acgate (U : Square 4) : Square 8 :=
  swapbc * abgate U * swapbc

/-! ## Entanglement predicate -/

/-- A 4-dimensional vector is a product state if it factors as a tensor product
    of two 2-dimensional vectors. -/
def IsProductState (v : Vec 4) : Prop :=
  ∃ (a b : Vec 2), v = kronVec a b

/-- A 4-dimensional vector is entangled if it is not a product state. -/
def IsEntangled (v : Vec 4) : Prop :=
  ¬ IsProductState v

/-! ## Qubit predicate -/

/-- A vector is a valid qubit state if it is a unit vector (under the standard inner product). -/
def IsQubit (v : Vec n) : Prop :=
  ∑ i, ‖v i‖ ^ 2 = 1

/-! ## TwoQubitGate -/

/-- A `TwoQubitGate` is an 8×8 unitary that acts nontrivially on at most two qubits:
    it is an embedding of some 4×4 unitary via AB, AC, or BC. -/
def TwoQubitGate (U : Square 8) : Prop :=
  ∃ (V : Square 4), V ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
    (U = abgate V ∨ U = acgate V ∨ U = bcgate V)

/-! ## Canonical pair set R(u₀, u₁) -/

/-- `inCanonicalPair u₀ u₁ u₂ u₃` means `(u₂, u₃) ∈ R(u₀, u₁)`,
    i.e. `(u₂, u₃) = (u₀, u₁)` or `(u₂, u₃) = (1, u₀* · u₁)`. -/
def inCanonicalPair (u₀ u₁ u₂ u₃ : ℂ) : Prop :=
  (u₂ = u₀ ∧ u₃ = u₁) ∨ (u₂ = 1 ∧ u₃ = starRingEnd ℂ u₀ * u₁)

end TwoControl

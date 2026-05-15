import TwoControl.Clifford.Statements

open Matrix

namespace TwoControl
namespace Clifford
namespace Universal

/-!
This file contains the circuit and gate-set vocabulary for the `doc.tex`
Clifford+T universality track.  The existing Clifford files already give
concrete one- and two-qubit matrix semantics.  The arbitrary `n`-qubit
embedding predicates below are intentionally isolated here: an embedding is a
padded tensor placement, reindexed to the ambient `2 ^ n` space, followed by a
basis permutation.
-/

/-- Matrix semantics of a circuit represented as a list of gates, composed left to right. -/
noncomputable def circuitMatrix {N : ℕ} (gates : List (Square N)) : Square N :=
  gates.foldr (fun gate acc => gate * acc) 1

@[simp] theorem circuitMatrix_nil {N : ℕ} :
    circuitMatrix ([] : List (Square N)) = (1 : Square N) := by
  rfl

@[simp] theorem circuitMatrix_cons {N : ℕ} (gate : Square N) (gates : List (Square N)) :
    circuitMatrix (gate :: gates) = gate * circuitMatrix gates := by
  rfl

theorem circuitMatrix_append {N : ℕ} (left right : List (Square N)) :
    circuitMatrix (left ++ right) = circuitMatrix left * circuitMatrix right := by
  induction left with
  | nil => simp [circuitMatrix]
  | cons gate left ih =>
      calc
        circuitMatrix ((gate :: left) ++ right) = gate * circuitMatrix (left ++ right) := by
          simp [circuitMatrix]
        _ = gate * (circuitMatrix left * circuitMatrix right) := by rw [ih]
        _ = circuitMatrix (gate :: left) * circuitMatrix right := by
          simp [circuitMatrix, mul_assoc]

/-- Every gate in a list belongs to the chosen gate set. -/
def CircuitOver {N : ℕ} (allowed : Square N → Prop) (gates : List (Square N)) : Prop :=
  ∀ gate ∈ gates, allowed gate

@[simp] theorem CircuitOver_nil {N : ℕ} (allowed : Square N → Prop) :
    CircuitOver allowed [] := by
  intro gate hgate
  simp at hgate

theorem CircuitOver_cons {N : ℕ} {allowed : Square N → Prop}
    {gate : Square N} {gates : List (Square N)}
    (hgate : allowed gate) (hgates : CircuitOver allowed gates) :
    CircuitOver allowed (gate :: gates) := by
  intro V hV
  rcases List.mem_cons.1 hV with hV | hV
  · cases hV
    exact hgate
  · exact hgates V hV

theorem CircuitOver_append {N : ℕ} {allowed : Square N → Prop}
    {left right : List (Square N)}
    (hleft : CircuitOver allowed left) (hright : CircuitOver allowed right) :
    CircuitOver allowed (left ++ right) := by
  intro gate hgate
  exact (List.mem_append.1 hgate).elim (hleft gate) (hright gate)

theorem CircuitOver_append_iff {N : ℕ} {allowed : Square N → Prop}
    {left right : List (Square N)} :
    CircuitOver allowed (left ++ right) ↔
      CircuitOver allowed left ∧ CircuitOver allowed right := by
  constructor
  · intro h
    exact ⟨fun gate hgate => h gate (List.mem_append_left right hgate),
      fun gate hgate => h gate (List.mem_append_right left hgate)⟩
  · intro h
    exact CircuitOver_append h.1 h.2

theorem CircuitOver.mono {N : ℕ} {allowed₁ allowed₂ : Square N → Prop}
    {gates : List (Square N)}
    (hsub : ∀ gate, allowed₁ gate → allowed₂ gate)
    (hgates : CircuitOver allowed₁ gates) :
    CircuitOver allowed₂ gates := by
  intro gate hgate
  exact hsub gate (hgates gate hgate)

/-- Exact synthesis by a gate set. -/
def Synthesizes {N : ℕ} (allowed : Square N → Prop) (U : Square N) : Prop :=
  ∃ gates : List (Square N), CircuitOver allowed gates ∧ U = circuitMatrix gates

/-- Synthesis up to global phase by a gate set. -/
def SynthesizesUpToGlobalPhase {N : ℕ} (allowed : Square N → Prop) (U : Square N) :
    Prop :=
  ∃ gates : List (Square N), CircuitOver allowed gates ∧
    GlobalPhaseEquivalent U (circuitMatrix gates)

/-! ### Embedded gate placement infrastructure -/

noncomputable def reindexSquare {N M : ℕ} (e : Fin N ≃ Fin M) (U : Square N) :
    Square M :=
  (Matrix.reindexAlgEquiv ℂ ℂ e) U

noncomputable def castSquare {N M : ℕ} (h : N = M) (U : Square N) : Square M :=
  reindexSquare (Equiv.cast (congrArg Fin h)) U

theorem reindexSquare_mul {N M : ℕ} (e : Fin N ≃ Fin M) (U V : Square N) :
    reindexSquare e (U * V) = reindexSquare e U * reindexSquare e V := by
  simp [reindexSquare]

@[simp] theorem reindexSquare_one {N M : ℕ} (e : Fin N ≃ Fin M) :
    reindexSquare e (1 : Square N) = (1 : Square M) := by
  simp [reindexSquare]

theorem castSquare_mul {N M : ℕ} (h : N = M) (U V : Square N) :
    castSquare h (U * V) = castSquare h U * castSquare h V :=
  reindexSquare_mul (Equiv.cast (congrArg Fin h)) U V

@[simp] theorem castSquare_one {N M : ℕ} (h : N = M) :
    castSquare h (1 : Square N) = (1 : Square M) := by
  simp [castSquare]

theorem reindexSquare_conjTranspose {N M : ℕ} (e : Fin N ≃ Fin M) (U : Square N) :
    (reindexSquare e U)† = reindexSquare e U† := by
  rfl

theorem reindexSquare_mem_unitaryGroup {N M : ℕ} (e : Fin N ≃ Fin M)
    {U : Square N} (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    reindexSquare e U ∈ Matrix.unitaryGroup (Fin M) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hU' : U† * U = (1 : Square N) := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU
  calc
    star (reindexSquare e U) * reindexSquare e U
        = (reindexSquare e U)† * reindexSquare e U := by
            simp [Matrix.star_eq_conjTranspose]
    _ = reindexSquare e (U† * U) := by
          rw [reindexSquare_conjTranspose, ← reindexSquare_mul]
    _ = (1 : Square M) := by
          simp [hU']

theorem castSquare_mem_unitaryGroup {N M : ℕ} (h : N = M)
    {U : Square N} (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    castSquare h U ∈ Matrix.unitaryGroup (Fin M) ℂ :=
  reindexSquare_mem_unitaryGroup (Equiv.cast (congrArg Fin h)) hU

theorem kron_mem_unitaryGroup {m n : ℕ} {U : Square m} {V : Square n}
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    U ⊗ₖ V ∈ Matrix.unitaryGroup (Fin (m * n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hU' : U† * U = (1 : Square m) := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU
  have hV' : V† * V = (1 : Square n) := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hV
  calc
    star (U ⊗ₖ V) * (U ⊗ₖ V)
        = (U ⊗ₖ V)† * (U ⊗ₖ V) := by
            simp [Matrix.star_eq_conjTranspose]
    _ = (U† * U) ⊗ₖ (V† * V) := by
          rw [KronHelpers.conjTranspose_kron_reindex, ← KronHelpers.kron_mul_reindex]
    _ = (1 : Square (m * n)) := by
          rw [hU', hV']
          exact TwoControl.one_kron_one m n

private lemma inv_sqrt_two_sq_for_hadamard :
    ((↑(Real.sqrt 2) : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
  have hsqrt_ne : (↑(Real.sqrt 2) : ℂ) ≠ 0 := by
    exact_mod_cast (show (Real.sqrt 2 : ℝ) ≠ 0 by positivity)
  have hsq_real : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hsq : ((↑(Real.sqrt 2) : ℂ)) ^ 2 = (2 : ℂ) := by
    exact_mod_cast hsq_real
  field_simp [pow_two, hsqrt_ne]
  simpa using hsq.symm

theorem hadamard2_mem_unitaryGroup :
    hadamard2 ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hhalf :
      ((↑(Real.sqrt 2) : ℂ)⁻¹) * ((↑(Real.sqrt 2) : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    simpa [pow_two] using inv_sqrt_two_sq_for_hadamard
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamard2, Matrix.mul_apply, Fin.sum_univ_two, hhalf]

theorem phaseS_mem_unitaryGroup :
    phaseS ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  exact diag2_unitary 1 Complex.I (by simp) (by simp)

theorem phaseSdagger_mem_unitaryGroup :
    phaseSdagger ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  exact diag2_unitary 1 (-Complex.I) (by simp) (by simp)

theorem phaseT_mem_unitaryGroup :
    phaseT ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply diag2_unitary
  · simp
  · simpa [phaseT, mul_comm, mul_left_comm, mul_assoc] using
      Complex.norm_exp_ofReal_mul_I (Real.pi / 4)

theorem rz_mem_unitaryGroup (θ : ℝ) :
    rz θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply diag2_unitary
  · simpa [rz, mul_comm, mul_left_comm, mul_assoc] using
      Complex.norm_exp_ofReal_mul_I (-(θ / 2))
  · simpa [rz, mul_comm, mul_left_comm, mul_assoc] using
      Complex.norm_exp_ofReal_mul_I (θ / 2)

theorem cnot_mem_unitaryGroup :
    cnot ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  simpa [cnot] using GateHelpers.notc_unitary

theorem localOnFirst_mem_unitaryGroup {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    localOnFirst U ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  exact kron_mem_unitaryGroup hU (Submonoid.one_mem _)

theorem localOnSecond_mem_unitaryGroup {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    localOnSecond U ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  exact kron_mem_unitaryGroup (Submonoid.one_mem _) hU

/-- A concrete placement of one distinguished qubit inside an `n`-qubit space.

The local gate is first placed as `I_left ⊗ (U ⊗ I_right)`, cast to the ambient
dimension using `dimension_eq`, and then conjugated by a basis reindexing
`permutation`.  The `target` field records the logical wire selected by this
placement. -/
structure OneQubitPlacement (n : ℕ) where
  target : Fin n
  left : ℕ
  right : ℕ
  dimension_eq : left * (2 * right) = 2 ^ n
  permutation : Fin (2 ^ n) ≃ Fin (2 ^ n)

namespace OneQubitPlacement

variable {n : ℕ} (p : OneQubitPlacement n)

noncomputable def tensor (U : Square 2) : Square (p.left * (2 * p.right)) :=
  (1 : Square p.left) ⊗ₖ (U ⊗ₖ (1 : Square p.right))

noncomputable def embed (U : Square 2) : Square (2 ^ n) :=
  reindexSquare p.permutation (castSquare p.dimension_eq (p.tensor U))

theorem tensor_mul (U V : Square 2) :
    p.tensor (U * V) = p.tensor U * p.tensor V := by
  have hinner :
      (U * V) ⊗ₖ (1 : Square p.right) =
        (U ⊗ₖ (1 : Square p.right)) * (V ⊗ₖ (1 : Square p.right)) := by
    simpa using
      (KronHelpers.kron_mul_reindex (A := U) (B := V)
        (C := (1 : Square p.right)) (D := (1 : Square p.right)))
  rw [tensor, tensor, tensor, hinner]
  simpa using
    (KronHelpers.kron_mul_reindex (A := (1 : Square p.left))
      (B := (1 : Square p.left)) (C := U ⊗ₖ (1 : Square p.right))
      (D := V ⊗ₖ (1 : Square p.right)))

@[simp] theorem tensor_one :
    p.tensor (1 : Square 2) = (1 : Square (p.left * (2 * p.right))) := by
  rw [tensor]
  rw [TwoControl.one_kron_one 2 p.right]
  exact TwoControl.one_kron_one p.left (2 * p.right)

theorem embed_mul (U V : Square 2) :
    p.embed (U * V) = p.embed U * p.embed V := by
  rw [embed, embed, embed, tensor_mul]
  rw [castSquare_mul, reindexSquare_mul]

@[simp] theorem embed_one :
    p.embed (1 : Square 2) = (1 : Square (2 ^ n)) := by
  simp [embed]

theorem tensor_mem_unitaryGroup {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    p.tensor U ∈ Matrix.unitaryGroup (Fin (p.left * (2 * p.right))) ℂ := by
  exact kron_mem_unitaryGroup (Submonoid.one_mem _)
    (kron_mem_unitaryGroup hU (Submonoid.one_mem _))

theorem embed_mem_unitaryGroup {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    p.embed U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  exact reindexSquare_mem_unitaryGroup p.permutation
    (castSquare_mem_unitaryGroup p.dimension_eq (p.tensor_mem_unitaryGroup hU))

end OneQubitPlacement

/-- A concrete placement of two distinguished qubits inside an `n`-qubit space.

The local two-qubit gate is placed as `I_left ⊗ (U ⊗ I_right)`, then cast and
permuted into the ambient wire order. -/
structure TwoQubitPlacement (n : ℕ) where
  first : Fin n
  second : Fin n
  distinct : first ≠ second
  left : ℕ
  right : ℕ
  dimension_eq : left * (4 * right) = 2 ^ n
  permutation : Fin (2 ^ n) ≃ Fin (2 ^ n)

namespace TwoQubitPlacement

variable {n : ℕ} (p : TwoQubitPlacement n)

noncomputable def tensor (U : Square 4) : Square (p.left * (4 * p.right)) :=
  (1 : Square p.left) ⊗ₖ (U ⊗ₖ (1 : Square p.right))

noncomputable def embed (U : Square 4) : Square (2 ^ n) :=
  reindexSquare p.permutation (castSquare p.dimension_eq (p.tensor U))

theorem tensor_mul (U V : Square 4) :
    p.tensor (U * V) = p.tensor U * p.tensor V := by
  have hinner :
      (U * V) ⊗ₖ (1 : Square p.right) =
        (U ⊗ₖ (1 : Square p.right)) * (V ⊗ₖ (1 : Square p.right)) := by
    simpa using
      (KronHelpers.kron_mul_reindex (A := U) (B := V)
        (C := (1 : Square p.right)) (D := (1 : Square p.right)))
  rw [tensor, tensor, tensor, hinner]
  simpa using
    (KronHelpers.kron_mul_reindex (A := (1 : Square p.left))
      (B := (1 : Square p.left)) (C := U ⊗ₖ (1 : Square p.right))
      (D := V ⊗ₖ (1 : Square p.right)))

@[simp] theorem tensor_one :
    p.tensor (1 : Square 4) = (1 : Square (p.left * (4 * p.right))) := by
  rw [tensor]
  rw [TwoControl.one_kron_one 4 p.right]
  exact TwoControl.one_kron_one p.left (4 * p.right)

theorem embed_mul (U V : Square 4) :
    p.embed (U * V) = p.embed U * p.embed V := by
  rw [embed, embed, embed, tensor_mul]
  rw [castSquare_mul, reindexSquare_mul]

@[simp] theorem embed_one :
    p.embed (1 : Square 4) = (1 : Square (2 ^ n)) := by
  simp [embed]

theorem tensor_mem_unitaryGroup {U : Square 4}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    p.tensor U ∈ Matrix.unitaryGroup (Fin (p.left * (4 * p.right))) ℂ := by
  exact kron_mem_unitaryGroup (Submonoid.one_mem _)
    (kron_mem_unitaryGroup hU (Submonoid.one_mem _))

theorem embed_mem_unitaryGroup {U : Square 4}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    p.embed U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  exact reindexSquare_mem_unitaryGroup p.permutation
    (castSquare_mem_unitaryGroup p.dimension_eq (p.tensor_mem_unitaryGroup hU))

end TwoQubitPlacement

/-- An embedded one-qubit gate in an `n`-qubit circuit.  The direct placement
case is the usual padded one-qubit tensor.  The two local cases let a local
factor of an embedded two-qubit placement be reused as an embedded one-qubit
gate, which is the form produced by lifted two-qubit Clifford+T circuits. -/
def IsEmbeddedOneQubitGate (n : ℕ) (U : Square 2) (E : Square (2 ^ n)) : Prop :=
  (∃ p : OneQubitPlacement n, E = p.embed U) ∨
  (∃ p : TwoQubitPlacement n, E = p.embed (localOnFirst U)) ∨
  (∃ p : TwoQubitPlacement n, E = p.embed (localOnSecond U))

/-- An embedded two-qubit gate in an `n`-qubit circuit. -/
def IsEmbeddedTwoQubitGate (n : ℕ) (U : Square 4) (E : Square (2 ^ n)) : Prop :=
  ∃ p : TwoQubitPlacement n, E = p.embed U

theorem IsEmbeddedOneQubitGate.of_placement {n : ℕ} (p : OneQubitPlacement n)
    (U : Square 2) :
    IsEmbeddedOneQubitGate n U (p.embed U) :=
  Or.inl ⟨p, rfl⟩

theorem IsEmbeddedOneQubitGate.of_twoQubit_first {n : ℕ} (p : TwoQubitPlacement n)
    (U : Square 2) :
    IsEmbeddedOneQubitGate n U (p.embed (localOnFirst U)) :=
  Or.inr (Or.inl ⟨p, rfl⟩)

theorem IsEmbeddedOneQubitGate.of_twoQubit_second {n : ℕ} (p : TwoQubitPlacement n)
    (U : Square 2) :
    IsEmbeddedOneQubitGate n U (p.embed (localOnSecond U)) :=
  Or.inr (Or.inr ⟨p, rfl⟩)

theorem IsEmbeddedTwoQubitGate.of_placement {n : ℕ} (p : TwoQubitPlacement n)
    (U : Square 4) :
    IsEmbeddedTwoQubitGate n U (p.embed U) :=
  ⟨p, rfl⟩

theorem IsEmbeddedOneQubitGate.mem_unitaryGroup {n : ℕ} {U : Square 2}
    {E : Square (2 ^ n)}
    (hEmbedded : IsEmbeddedOneQubitGate n U E)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    E ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rcases hEmbedded with ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact p.embed_mem_unitaryGroup hU
  · exact p.embed_mem_unitaryGroup (localOnFirst_mem_unitaryGroup hU)
  · exact p.embed_mem_unitaryGroup (localOnSecond_mem_unitaryGroup hU)

theorem IsEmbeddedTwoQubitGate.mem_unitaryGroup {n : ℕ} {U : Square 4}
    {E : Square (2 ^ n)}
    (hEmbedded : IsEmbeddedTwoQubitGate n U E)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    E ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rcases hEmbedded with ⟨p, rfl⟩
  exact p.embed_mem_unitaryGroup hU

/-- Gates in Lemma 1 of `doc.tex`: arbitrary two-qubit gates plus `H`, `S`, `S†`,
and `R_z(θ)` one-qubit gates. -/
def EasyGate (n : ℕ) (U : Square (2 ^ n)) : Prop :=
  (∃ V : Square 4, V ∈ unitaryGroup (Fin 4) ℂ ∧ IsEmbeddedTwoQubitGate n V U) ∨
  IsEmbeddedOneQubitGate n hadamard2 U ∨
  IsEmbeddedOneQubitGate n phaseS U ∨
  IsEmbeddedOneQubitGate n phaseSdagger U ∨
  (∃ θ : ℝ, IsEmbeddedOneQubitGate n (rz θ) U)

/-- Gates after Lemma 11 has eliminated arbitrary two-qubit gates, but before
Lemma 12 has eliminated `R_z(θ)`. -/
def CliffordTRzGate (n : ℕ) (U : Square (2 ^ n)) : Prop :=
  IsEmbeddedTwoQubitGate n cnot U ∨
  IsEmbeddedOneQubitGate n hadamard2 U ∨
  IsEmbeddedOneQubitGate n phaseT U ∨
  (∃ θ : ℝ, IsEmbeddedOneQubitGate n (rz θ) U)

/-- Final Clifford+T gate set for the main theorem. -/
def CliffordTGate (n : ℕ) (U : Square (2 ^ n)) : Prop :=
  IsEmbeddedTwoQubitGate n cnot U ∨
  IsEmbeddedOneQubitGate n hadamard2 U ∨
  IsEmbeddedOneQubitGate n phaseT U

theorem EasyGate.of_embedded_two_qubit {n : ℕ} {V : Square 4}
    {U : Square (2 ^ n)}
    (hV : V ∈ unitaryGroup (Fin 4) ℂ) (hU : IsEmbeddedTwoQubitGate n V U) :
    EasyGate n U :=
  Or.inl ⟨V, hV, hU⟩

theorem EasyGate.hadamard {n : ℕ} {U : Square (2 ^ n)}
    (hU : IsEmbeddedOneQubitGate n hadamard2 U) :
    EasyGate n U :=
  Or.inr (Or.inl hU)

theorem EasyGate.phaseS {n : ℕ} {U : Square (2 ^ n)}
    (hU : IsEmbeddedOneQubitGate n phaseS U) :
    EasyGate n U :=
  Or.inr (Or.inr (Or.inl hU))

theorem EasyGate.phaseSdagger {n : ℕ} {U : Square (2 ^ n)}
    (hU : IsEmbeddedOneQubitGate n phaseSdagger U) :
    EasyGate n U :=
  Or.inr (Or.inr (Or.inr (Or.inl hU)))

theorem EasyGate.rz {n : ℕ} (θ : ℝ) {U : Square (2 ^ n)}
    (hU : IsEmbeddedOneQubitGate n (rz θ) U) :
    EasyGate n U :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨θ, hU⟩)))

theorem CliffordTRzGate.cnot {n : ℕ} {U : Square (2 ^ n)}
    (hU : IsEmbeddedTwoQubitGate n cnot U) :
    CliffordTRzGate n U :=
  Or.inl hU

theorem CliffordTRzGate.hadamard {n : ℕ} {U : Square (2 ^ n)}
    (hU : IsEmbeddedOneQubitGate n hadamard2 U) :
    CliffordTRzGate n U :=
  Or.inr (Or.inl hU)

theorem CliffordTRzGate.phaseT {n : ℕ} {U : Square (2 ^ n)}
    (hU : IsEmbeddedOneQubitGate n phaseT U) :
    CliffordTRzGate n U :=
  Or.inr (Or.inr (Or.inl hU))

theorem CliffordTRzGate.rz {n : ℕ} (θ : ℝ) {U : Square (2 ^ n)}
    (hU : IsEmbeddedOneQubitGate n (rz θ) U) :
    CliffordTRzGate n U :=
  Or.inr (Or.inr (Or.inr ⟨θ, hU⟩))

theorem CliffordTGate.cnot {n : ℕ} {U : Square (2 ^ n)}
    (hU : IsEmbeddedTwoQubitGate n cnot U) :
    CliffordTGate n U :=
  Or.inl hU

theorem CliffordTGate.hadamard {n : ℕ} {U : Square (2 ^ n)}
    (hU : IsEmbeddedOneQubitGate n hadamard2 U) :
    CliffordTGate n U :=
  Or.inr (Or.inl hU)

theorem CliffordTGate.phaseT {n : ℕ} {U : Square (2 ^ n)}
    (hU : IsEmbeddedOneQubitGate n phaseT U) :
    CliffordTGate n U :=
  Or.inr (Or.inr hU)

theorem EasyGate.mem_unitaryGroup {n : ℕ} {U : Square (2 ^ n)}
    (hU : EasyGate n U) :
    U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rcases hU with hTwo | hH | hS | hSdg | hRz
  · rcases hTwo with ⟨V, hV, hEmbedded⟩
    exact hEmbedded.mem_unitaryGroup hV
  · exact hH.mem_unitaryGroup hadamard2_mem_unitaryGroup
  · exact hS.mem_unitaryGroup phaseS_mem_unitaryGroup
  · exact hSdg.mem_unitaryGroup phaseSdagger_mem_unitaryGroup
  · rcases hRz with ⟨θ, hEmbedded⟩
    exact hEmbedded.mem_unitaryGroup (rz_mem_unitaryGroup θ)

theorem CliffordTRzGate.mem_unitaryGroup {n : ℕ} {U : Square (2 ^ n)}
    (hU : CliffordTRzGate n U) :
    U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rcases hU with hCnot | hH | hT | hRz
  · exact hCnot.mem_unitaryGroup cnot_mem_unitaryGroup
  · exact hH.mem_unitaryGroup hadamard2_mem_unitaryGroup
  · exact hT.mem_unitaryGroup phaseT_mem_unitaryGroup
  · rcases hRz with ⟨θ, hEmbedded⟩
    exact hEmbedded.mem_unitaryGroup (rz_mem_unitaryGroup θ)

theorem CliffordTGate.mem_unitaryGroup {n : ℕ} {U : Square (2 ^ n)}
    (hU : CliffordTGate n U) :
    U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rcases hU with hCnot | hH | hT
  · exact hCnot.mem_unitaryGroup cnot_mem_unitaryGroup
  · exact hH.mem_unitaryGroup hadamard2_mem_unitaryGroup
  · exact hT.mem_unitaryGroup phaseT_mem_unitaryGroup

noncomputable def embedOneQubitPrimitive {n : ℕ}
    (p : OneQubitPlacement n) (gate : OneQubitPrimitive) : Square (2 ^ n) :=
  p.embed (OneQubitPrimitive.eval gate)

noncomputable def embedOneQubitCircuit {n : ℕ}
    (p : OneQubitPlacement n) (gates : List OneQubitPrimitive) :
    List (Square (2 ^ n)) :=
  gates.map (embedOneQubitPrimitive p)

theorem circuitMatrix_embedOneQubitCircuit {n : ℕ}
    (p : OneQubitPlacement n) (gates : List OneQubitPrimitive) :
    circuitMatrix (embedOneQubitCircuit p gates) =
      p.embed (oneQubitCircuitMatrix gates) := by
  induction gates with
  | nil =>
      simp [embedOneQubitCircuit, circuitMatrix, oneQubitCircuitMatrix]
  | cons gate gates ih =>
      calc
        circuitMatrix (embedOneQubitCircuit p (gate :: gates)) =
            p.embed (OneQubitPrimitive.eval gate) *
              circuitMatrix (embedOneQubitCircuit p gates) := by
          simp [embedOneQubitCircuit, embedOneQubitPrimitive, circuitMatrix]
        _ = p.embed (OneQubitPrimitive.eval gate) *
              p.embed (oneQubitCircuitMatrix gates) := by
          rw [ih]
        _ = p.embed (OneQubitPrimitive.eval gate * oneQubitCircuitMatrix gates) := by
          rw [p.embed_mul]
        _ = p.embed (oneQubitCircuitMatrix (gate :: gates)) := by
          rfl

theorem CliffordTRzGate.embedOneQubitPrimitive {n : ℕ}
    (p : OneQubitPlacement n) (gate : OneQubitPrimitive) :
    CliffordTRzGate n (embedOneQubitPrimitive p gate) := by
  cases gate with
  | h =>
      exact CliffordTRzGate.hadamard
        (IsEmbeddedOneQubitGate.of_placement p hadamard2)
  | t =>
      exact CliffordTRzGate.phaseT
        (IsEmbeddedOneQubitGate.of_placement p TwoControl.Clifford.phaseT)
  | rz θ =>
      exact CliffordTRzGate.rz θ
        (IsEmbeddedOneQubitGate.of_placement p (TwoControl.Clifford.rz θ))

theorem CircuitOver_embedOneQubitCircuit_cliffordTRz {n : ℕ}
    (p : OneQubitPlacement n) (gates : List OneQubitPrimitive) :
    CircuitOver (CliffordTRzGate n) (embedOneQubitCircuit p gates) := by
  intro gate hgate
  rcases List.mem_map.1 hgate with ⟨primitive, hprimitive, rfl⟩
  exact CliffordTRzGate.embedOneQubitPrimitive p primitive

noncomputable def embedTwoQubitPrimitive {n : ℕ}
    (p : TwoQubitPlacement n) (gate : TwoQubitPrimitive) : Square (2 ^ n) :=
  p.embed (TwoQubitPrimitive.eval gate)

noncomputable def embedTwoQubitCircuit {n : ℕ}
    (p : TwoQubitPlacement n) (gates : List TwoQubitPrimitive) :
    List (Square (2 ^ n)) :=
  gates.map (embedTwoQubitPrimitive p)

theorem circuitMatrix_embedTwoQubitCircuit {n : ℕ}
    (p : TwoQubitPlacement n) (gates : List TwoQubitPrimitive) :
    circuitMatrix (embedTwoQubitCircuit p gates) =
      p.embed (twoQubitCircuitMatrix gates) := by
  induction gates with
  | nil =>
      simp [embedTwoQubitCircuit, circuitMatrix, twoQubitCircuitMatrix]
  | cons gate gates ih =>
      calc
        circuitMatrix (embedTwoQubitCircuit p (gate :: gates)) =
            p.embed (TwoQubitPrimitive.eval gate) *
              circuitMatrix (embedTwoQubitCircuit p gates) := by
          simp [embedTwoQubitCircuit, embedTwoQubitPrimitive, circuitMatrix]
        _ = p.embed (TwoQubitPrimitive.eval gate) *
              p.embed (twoQubitCircuitMatrix gates) := by
          rw [ih]
        _ = p.embed (TwoQubitPrimitive.eval gate * twoQubitCircuitMatrix gates) := by
          rw [p.embed_mul]
        _ = p.embed (twoQubitCircuitMatrix (gate :: gates)) := by
          rfl

theorem CliffordTRzGate.embedTwoQubitPrimitive {n : ℕ}
    (p : TwoQubitPlacement n) (gate : TwoQubitPrimitive) :
    CliffordTRzGate n (embedTwoQubitPrimitive p gate) := by
  cases gate with
  | cnot =>
      exact CliffordTRzGate.cnot
        (IsEmbeddedTwoQubitGate.of_placement p TwoControl.Clifford.cnot)
  | onFirst primitive =>
      cases primitive with
      | h =>
          exact CliffordTRzGate.hadamard
            (IsEmbeddedOneQubitGate.of_twoQubit_first p hadamard2)
      | t =>
          exact CliffordTRzGate.phaseT
            (IsEmbeddedOneQubitGate.of_twoQubit_first p TwoControl.Clifford.phaseT)
      | rz θ =>
          exact CliffordTRzGate.rz θ
            (IsEmbeddedOneQubitGate.of_twoQubit_first p (TwoControl.Clifford.rz θ))
  | onSecond primitive =>
      cases primitive with
      | h =>
          exact CliffordTRzGate.hadamard
            (IsEmbeddedOneQubitGate.of_twoQubit_second p hadamard2)
      | t =>
          exact CliffordTRzGate.phaseT
            (IsEmbeddedOneQubitGate.of_twoQubit_second p TwoControl.Clifford.phaseT)
      | rz θ =>
          exact CliffordTRzGate.rz θ
            (IsEmbeddedOneQubitGate.of_twoQubit_second p (TwoControl.Clifford.rz θ))

theorem CircuitOver_embedTwoQubitCircuit_cliffordTRz {n : ℕ}
    (p : TwoQubitPlacement n) (gates : List TwoQubitPrimitive) :
    CircuitOver (CliffordTRzGate n) (embedTwoQubitCircuit p gates) := by
  intro gate hgate
  rcases List.mem_map.1 hgate with ⟨primitive, hprimitive, rfl⟩
  exact CliffordTRzGate.embedTwoQubitPrimitive p primitive

/-- One-qubit `{H,T}` primitives, used for Lemma 12. -/
inductive OneQubitHTPrimitive where
  | h
  | t
deriving DecidableEq

noncomputable def OneQubitHTPrimitive.eval : OneQubitHTPrimitive → Square 2
  | .h => hadamard2
  | .t => phaseT

def OneQubitHTPrimitive.toOneQubitPrimitive :
    OneQubitHTPrimitive → OneQubitPrimitive
  | .h => .h
  | .t => .t

noncomputable def oneQubitHTCircuitMatrix (gates : List OneQubitHTPrimitive) :
    Square 2 :=
  gates.foldr (fun gate acc => OneQubitHTPrimitive.eval gate * acc) 1

@[simp] theorem oneQubitHTCircuitMatrix_nil :
    oneQubitHTCircuitMatrix [] = (1 : Square 2) := by
  rfl

@[simp] theorem oneQubitHTCircuitMatrix_cons (gate : OneQubitHTPrimitive)
    (gates : List OneQubitHTPrimitive) :
    oneQubitHTCircuitMatrix (gate :: gates) =
      OneQubitHTPrimitive.eval gate * oneQubitHTCircuitMatrix gates := by
  rfl

theorem oneQubitHTCircuitMatrix_append
    (left right : List OneQubitHTPrimitive) :
    oneQubitHTCircuitMatrix (left ++ right) =
      oneQubitHTCircuitMatrix left * oneQubitHTCircuitMatrix right := by
  induction left with
  | nil => simp [oneQubitHTCircuitMatrix]
  | cons gate left ih =>
      calc
        oneQubitHTCircuitMatrix ((gate :: left) ++ right)
            = OneQubitHTPrimitive.eval gate * oneQubitHTCircuitMatrix (left ++ right) := by
              simp [oneQubitHTCircuitMatrix]
        _ = OneQubitHTPrimitive.eval gate *
              (oneQubitHTCircuitMatrix left * oneQubitHTCircuitMatrix right) := by
              rw [ih]
        _ = oneQubitHTCircuitMatrix (gate :: left) * oneQubitHTCircuitMatrix right := by
              simp [oneQubitHTCircuitMatrix, mul_assoc]

theorem oneQubitHTCircuitMatrix_eq_oneQubitCircuitMatrix_map
    (gates : List OneQubitHTPrimitive) :
    oneQubitHTCircuitMatrix gates =
      oneQubitCircuitMatrix (gates.map OneQubitHTPrimitive.toOneQubitPrimitive) := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
      cases gate
      · simpa [oneQubitHTCircuitMatrix, OneQubitHTPrimitive.eval,
          OneQubitHTPrimitive.toOneQubitPrimitive, OneQubitPrimitive.eval] using
          congrArg (fun M : Square 2 => hadamard2 * M) ih
      · simpa [oneQubitHTCircuitMatrix, OneQubitHTPrimitive.eval,
          OneQubitHTPrimitive.toOneQubitPrimitive, OneQubitPrimitive.eval] using
          congrArg (fun M : Square 2 => phaseT * M) ih

noncomputable def embedOneQubitHTPrimitive {n : ℕ}
    (p : OneQubitPlacement n) (gate : OneQubitHTPrimitive) : Square (2 ^ n) :=
  p.embed (OneQubitHTPrimitive.eval gate)

noncomputable def embedOneQubitHTCircuit {n : ℕ}
    (p : OneQubitPlacement n) (gates : List OneQubitHTPrimitive) :
    List (Square (2 ^ n)) :=
  gates.map (embedOneQubitHTPrimitive p)

theorem circuitMatrix_embedOneQubitHTCircuit {n : ℕ}
    (p : OneQubitPlacement n) (gates : List OneQubitHTPrimitive) :
    circuitMatrix (embedOneQubitHTCircuit p gates) =
      p.embed (oneQubitHTCircuitMatrix gates) := by
  induction gates with
  | nil =>
      simp [embedOneQubitHTCircuit, circuitMatrix, oneQubitHTCircuitMatrix]
  | cons gate gates ih =>
      calc
        circuitMatrix (embedOneQubitHTCircuit p (gate :: gates)) =
            p.embed (OneQubitHTPrimitive.eval gate) *
              circuitMatrix (embedOneQubitHTCircuit p gates) := by
          simp [embedOneQubitHTCircuit, embedOneQubitHTPrimitive, circuitMatrix]
        _ = p.embed (OneQubitHTPrimitive.eval gate) *
              p.embed (oneQubitHTCircuitMatrix gates) := by
          rw [ih]
        _ = p.embed (OneQubitHTPrimitive.eval gate * oneQubitHTCircuitMatrix gates) := by
          rw [p.embed_mul]
        _ = p.embed (oneQubitHTCircuitMatrix (gate :: gates)) := by
          rfl

theorem CliffordTGate.embedOneQubitHTPrimitive {n : ℕ}
    (p : OneQubitPlacement n) (gate : OneQubitHTPrimitive) :
    CliffordTGate n (embedOneQubitHTPrimitive p gate) := by
  cases gate
  · exact CliffordTGate.hadamard
      (IsEmbeddedOneQubitGate.of_placement p hadamard2)
  · exact CliffordTGate.phaseT
      (IsEmbeddedOneQubitGate.of_placement p TwoControl.Clifford.phaseT)

theorem CircuitOver_embedOneQubitHTCircuit_cliffordT {n : ℕ}
    (p : OneQubitPlacement n) (gates : List OneQubitHTPrimitive) :
    CircuitOver (CliffordTGate n) (embedOneQubitHTCircuit p gates) := by
  intro gate hgate
  rcases List.mem_map.1 hgate with ⟨prim, hprim, rfl⟩
  exact CliffordTGate.embedOneQubitHTPrimitive p prim

/-- Two-qubit Clifford+T primitives: CNOT and local `{H,T}` gates. -/
inductive TwoQubitCliffordTPrimitive where
  | cnot
  | onFirst (gate : OneQubitHTPrimitive)
  | onSecond (gate : OneQubitHTPrimitive)
deriving DecidableEq

noncomputable def TwoQubitCliffordTPrimitive.eval :
    TwoQubitCliffordTPrimitive → Square 4
  | .cnot => Clifford.cnot
  | .onFirst gate => localOnFirst (OneQubitHTPrimitive.eval gate)
  | .onSecond gate => localOnSecond (OneQubitHTPrimitive.eval gate)

def TwoQubitCliffordTPrimitive.toTwoQubitPrimitive :
    TwoQubitCliffordTPrimitive → TwoQubitPrimitive
  | .cnot => .cnot
  | .onFirst gate => .onFirst gate.toOneQubitPrimitive
  | .onSecond gate => .onSecond gate.toOneQubitPrimitive

noncomputable def twoQubitCliffordTCircuitMatrix
    (gates : List TwoQubitCliffordTPrimitive) : Square 4 :=
  gates.foldr (fun gate acc => TwoQubitCliffordTPrimitive.eval gate * acc) 1

@[simp] theorem twoQubitCliffordTCircuitMatrix_nil :
    twoQubitCliffordTCircuitMatrix [] = (1 : Square 4) := by
  rfl

@[simp] theorem twoQubitCliffordTCircuitMatrix_cons
    (gate : TwoQubitCliffordTPrimitive) (gates : List TwoQubitCliffordTPrimitive) :
    twoQubitCliffordTCircuitMatrix (gate :: gates) =
      TwoQubitCliffordTPrimitive.eval gate * twoQubitCliffordTCircuitMatrix gates := by
  rfl

theorem twoQubitCliffordTCircuitMatrix_append
    (left right : List TwoQubitCliffordTPrimitive) :
    twoQubitCliffordTCircuitMatrix (left ++ right) =
      twoQubitCliffordTCircuitMatrix left * twoQubitCliffordTCircuitMatrix right := by
  induction left with
  | nil => simp [twoQubitCliffordTCircuitMatrix]
  | cons gate left ih =>
      calc
        twoQubitCliffordTCircuitMatrix ((gate :: left) ++ right)
            = TwoQubitCliffordTPrimitive.eval gate *
                twoQubitCliffordTCircuitMatrix (left ++ right) := by
              simp [twoQubitCliffordTCircuitMatrix]
        _ = TwoQubitCliffordTPrimitive.eval gate *
              (twoQubitCliffordTCircuitMatrix left *
                twoQubitCliffordTCircuitMatrix right) := by
              rw [ih]
        _ = twoQubitCliffordTCircuitMatrix (gate :: left) *
              twoQubitCliffordTCircuitMatrix right := by
              simp [twoQubitCliffordTCircuitMatrix, mul_assoc]

theorem twoQubitCliffordTCircuitMatrix_eq_twoQubitCircuitMatrix_map
    (gates : List TwoQubitCliffordTPrimitive) :
    twoQubitCliffordTCircuitMatrix gates =
      twoQubitCircuitMatrix
        (gates.map TwoQubitCliffordTPrimitive.toTwoQubitPrimitive) := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
      cases gate with
      | cnot =>
          simpa [twoQubitCliffordTCircuitMatrix, TwoQubitCliffordTPrimitive.eval,
            TwoQubitCliffordTPrimitive.toTwoQubitPrimitive, TwoQubitPrimitive.eval] using
            congrArg (fun M : Square 4 => cnot * M) ih
      | onFirst gate =>
          cases gate
          · simpa [twoQubitCliffordTCircuitMatrix, TwoQubitCliffordTPrimitive.eval,
              TwoQubitCliffordTPrimitive.toTwoQubitPrimitive, TwoQubitPrimitive.eval,
              OneQubitHTPrimitive.toOneQubitPrimitive, OneQubitPrimitive.eval,
              OneQubitHTPrimitive.eval] using
              congrArg (fun M : Square 4 => localOnFirst hadamard2 * M) ih
          · simpa [twoQubitCliffordTCircuitMatrix, TwoQubitCliffordTPrimitive.eval,
              TwoQubitCliffordTPrimitive.toTwoQubitPrimitive, TwoQubitPrimitive.eval,
              OneQubitHTPrimitive.toOneQubitPrimitive, OneQubitPrimitive.eval,
              OneQubitHTPrimitive.eval] using
              congrArg (fun M : Square 4 => localOnFirst phaseT * M) ih
      | onSecond gate =>
          cases gate
          · simpa [twoQubitCliffordTCircuitMatrix, TwoQubitCliffordTPrimitive.eval,
              TwoQubitCliffordTPrimitive.toTwoQubitPrimitive, TwoQubitPrimitive.eval,
              OneQubitHTPrimitive.toOneQubitPrimitive, OneQubitPrimitive.eval,
              OneQubitHTPrimitive.eval] using
              congrArg (fun M : Square 4 => localOnSecond hadamard2 * M) ih
          · simpa [twoQubitCliffordTCircuitMatrix, TwoQubitCliffordTPrimitive.eval,
              TwoQubitCliffordTPrimitive.toTwoQubitPrimitive, TwoQubitPrimitive.eval,
              OneQubitHTPrimitive.toOneQubitPrimitive, OneQubitPrimitive.eval,
              OneQubitHTPrimitive.eval] using
              congrArg (fun M : Square 4 => localOnSecond phaseT * M) ih

noncomputable def embedTwoQubitCliffordTPrimitive {n : ℕ}
    (p : TwoQubitPlacement n) (gate : TwoQubitCliffordTPrimitive) : Square (2 ^ n) :=
  p.embed (TwoQubitCliffordTPrimitive.eval gate)

noncomputable def embedTwoQubitCliffordTCircuit {n : ℕ}
    (p : TwoQubitPlacement n) (gates : List TwoQubitCliffordTPrimitive) :
    List (Square (2 ^ n)) :=
  gates.map (embedTwoQubitCliffordTPrimitive p)

theorem circuitMatrix_embedTwoQubitCliffordTCircuit {n : ℕ}
    (p : TwoQubitPlacement n) (gates : List TwoQubitCliffordTPrimitive) :
    circuitMatrix (embedTwoQubitCliffordTCircuit p gates) =
      p.embed (twoQubitCliffordTCircuitMatrix gates) := by
  induction gates with
  | nil =>
      simp [embedTwoQubitCliffordTCircuit, circuitMatrix, twoQubitCliffordTCircuitMatrix]
  | cons gate gates ih =>
      calc
        circuitMatrix (embedTwoQubitCliffordTCircuit p (gate :: gates)) =
            p.embed (TwoQubitCliffordTPrimitive.eval gate) *
              circuitMatrix (embedTwoQubitCliffordTCircuit p gates) := by
          simp [embedTwoQubitCliffordTCircuit, embedTwoQubitCliffordTPrimitive,
            circuitMatrix]
        _ = p.embed (TwoQubitCliffordTPrimitive.eval gate) *
              p.embed (twoQubitCliffordTCircuitMatrix gates) := by
          rw [ih]
        _ = p.embed
              (TwoQubitCliffordTPrimitive.eval gate * twoQubitCliffordTCircuitMatrix gates) := by
          rw [p.embed_mul]
        _ = p.embed (twoQubitCliffordTCircuitMatrix (gate :: gates)) := by
          rfl

theorem CliffordTGate.embedTwoQubitCliffordTPrimitive {n : ℕ}
    (p : TwoQubitPlacement n) (gate : TwoQubitCliffordTPrimitive) :
    CliffordTGate n (embedTwoQubitCliffordTPrimitive p gate) := by
  cases gate with
  | cnot =>
      exact CliffordTGate.cnot
        (IsEmbeddedTwoQubitGate.of_placement p TwoControl.Clifford.cnot)
  | onFirst prim =>
      cases prim
      · exact CliffordTGate.hadamard
          (IsEmbeddedOneQubitGate.of_twoQubit_first p hadamard2)
      · exact CliffordTGate.phaseT
          (IsEmbeddedOneQubitGate.of_twoQubit_first p TwoControl.Clifford.phaseT)
  | onSecond prim =>
      cases prim
      · exact CliffordTGate.hadamard
          (IsEmbeddedOneQubitGate.of_twoQubit_second p hadamard2)
      · exact CliffordTGate.phaseT
          (IsEmbeddedOneQubitGate.of_twoQubit_second p TwoControl.Clifford.phaseT)

theorem CircuitOver_embedTwoQubitCliffordTCircuit_cliffordT {n : ℕ}
    (p : TwoQubitPlacement n) (gates : List TwoQubitCliffordTPrimitive) :
    CircuitOver (CliffordTGate n) (embedTwoQubitCliffordTCircuit p gates) := by
  intro gate hgate
  rcases List.mem_map.1 hgate with ⟨prim, hprim, rfl⟩
  exact CliffordTGate.embedTwoQubitCliffordTPrimitive p prim

end Universal
end Clifford
end TwoControl

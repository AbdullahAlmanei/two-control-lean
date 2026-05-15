import TwoControl.Clifford.Universal.Distance

namespace TwoControl
namespace Clifford
namespace Universal

/-!
Lemma 12 layer.  We intentionally keep the number-theoretic approximation
theorem as an explicit external axiom for now; the rest of the main theorem
can be wired against this interface while the standalone approximation
development is completed.
-/

/-- Lemma 12 in `doc.tex`: `{H,T}` approximates every `R_z(θ)` to arbitrary
Hilbert-Schmidt precision. -/
axiom lemma12_rz_approximation_by_ht (θ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List OneQubitHTPrimitive,
      hsDistance (rz θ) (oneQubitHTCircuitMatrix gates) < ε

private theorem trace_reindexSquare {N M : ℕ} (e : Fin N ≃ Fin M) (A : Square N) :
    Matrix.trace (reindexSquare e A) = Matrix.trace A := by
  simp [reindexSquare, Matrix.trace]
  rw [Fintype.sum_equiv e.symm]
  intro x
  rfl

private theorem trace_matrix_reindex {N M : Type*} [Fintype N] [Fintype M]
  (e : N ≃ M) (A : Matrix N N ℂ) :
  Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
  simp [Matrix.trace, Matrix.reindex_apply]
  rw [Fintype.sum_equiv e.symm]
  intro x
  rfl

private theorem trace_castSquare {N M : ℕ} (h : N = M) (A : Square N) :
    Matrix.trace (castSquare h A) = Matrix.trace A := by
  simpa [castSquare] using
    trace_reindexSquare (Equiv.cast (congrArg Fin h)) A

private theorem trace_kron {m n : ℕ} (A : Square m) (B : Square n) :
    Matrix.trace (A ⊗ₖ B) = Matrix.trace A * Matrix.trace B := by
  calc
    Matrix.trace (A ⊗ₖ B)
      = Matrix.trace (Matrix.kroneckerMap (· * ·) A B) := by
          unfold TwoControl.kron
          simpa using trace_matrix_reindex finProdFinEquiv (Matrix.kroneckerMap (· * ·) A B)
    _ = Matrix.trace A * Matrix.trace B := by
          simpa using Matrix.trace_kroneckerMapBilinear (LinearMap.mul ℂ ℂ) A B

private theorem castSquare_conjTranspose {N M : ℕ} (h : N = M) (A : Square N) :
    (castSquare h A)† = castSquare h A† := by
  simpa [castSquare] using
    reindexSquare_conjTranspose (Equiv.cast (congrArg Fin h)) A

private lemma localOnFirst_mul (A B : Square 2) :
    localOnFirst (A * B) = localOnFirst A * localOnFirst B := by
  unfold localOnFirst
  simpa using
    (KronHelpers.kron_mul_reindex (A := A) (B := B)
      (C := (1 : Square 2)) (D := (1 : Square 2)))

private lemma localOnSecond_mul (A B : Square 2) :
    localOnSecond (A * B) = localOnSecond A * localOnSecond B := by
  unfold localOnSecond
  simpa using
    (KronHelpers.kron_mul_reindex (A := (1 : Square 2)) (B := (1 : Square 2))
      (C := A) (D := B))

private lemma localOnFirst_conjTranspose (A : Square 2) :
    (localOnFirst A)† = localOnFirst A† := by
  unfold localOnFirst
  simpa using KronHelpers.conjTranspose_kron_reindex (A := A) (B := (1 : Square 2))

private lemma localOnSecond_conjTranspose (A : Square 2) :
    (localOnSecond A)† = localOnSecond A† := by
  unfold localOnSecond
  simpa using KronHelpers.conjTranspose_kron_reindex (A := (1 : Square 2)) (B := A)

private theorem OneQubitPlacement.tensor_conjTranspose {n : ℕ}
    (p : OneQubitPlacement n) (A : Square 2) :
    (p.tensor A)† = p.tensor A† := by
  unfold OneQubitPlacement.tensor
  rw [KronHelpers.conjTranspose_kron_reindex, KronHelpers.conjTranspose_kron_reindex]
  simp

private theorem OneQubitPlacement.embed_conjTranspose {n : ℕ}
    (p : OneQubitPlacement n) (A : Square 2) :
    (p.embed A)† = p.embed A† := by
  unfold OneQubitPlacement.embed
  rw [reindexSquare_conjTranspose, castSquare_conjTranspose, p.tensor_conjTranspose]

private theorem TwoQubitPlacement.tensor_conjTranspose {n : ℕ}
    (p : TwoQubitPlacement n) (A : Square 4) :
    (p.tensor A)† = p.tensor A† := by
  unfold TwoQubitPlacement.tensor
  rw [KronHelpers.conjTranspose_kron_reindex, KronHelpers.conjTranspose_kron_reindex]
  simp

private theorem TwoQubitPlacement.embed_conjTranspose {n : ℕ}
    (p : TwoQubitPlacement n) (A : Square 4) :
    (p.embed A)† = p.embed A† := by
  unfold TwoQubitPlacement.embed
  rw [reindexSquare_conjTranspose, castSquare_conjTranspose, p.tensor_conjTranspose]

private theorem OneQubitPlacement.trace_tensor {n : ℕ}
    (p : OneQubitPlacement n) (A : Square 2) :
    Matrix.trace (p.tensor A) = ((p.left * p.right : ℕ) : ℂ) * Matrix.trace A := by
  unfold OneQubitPlacement.tensor
  calc
    Matrix.trace ((1 : Square p.left) ⊗ₖ (A ⊗ₖ (1 : Square p.right)))
        = Matrix.trace (1 : Square p.left) * Matrix.trace (A ⊗ₖ (1 : Square p.right)) := by
            rw [trace_kron]
    _ = (p.left : ℂ) * (Matrix.trace A * Matrix.trace (1 : Square p.right)) := by
          rw [trace_kron]
          simp [Matrix.trace_one]
    _ = ((p.left * p.right : ℕ) : ℂ) * Matrix.trace A := by
          simp [Matrix.trace_one]
          ring

private theorem TwoQubitPlacement.trace_tensor {n : ℕ}
    (p : TwoQubitPlacement n) (A : Square 4) :
    Matrix.trace (p.tensor A) = ((p.left * p.right : ℕ) : ℂ) * Matrix.trace A := by
  unfold TwoQubitPlacement.tensor
  calc
    Matrix.trace ((1 : Square p.left) ⊗ₖ (A ⊗ₖ (1 : Square p.right)))
        = Matrix.trace (1 : Square p.left) * Matrix.trace (A ⊗ₖ (1 : Square p.right)) := by
            rw [trace_kron]
    _ = (p.left : ℂ) * (Matrix.trace A * Matrix.trace (1 : Square p.right)) := by
          rw [trace_kron]
          simp [Matrix.trace_one]
    _ = ((p.left * p.right : ℕ) : ℂ) * Matrix.trace A := by
          simp [Matrix.trace_one]
          ring

private theorem OneQubitPlacement.trace_embed_mul {n : ℕ}
    (p : OneQubitPlacement n) (A B : Square 2) :
    Matrix.trace ((p.embed A)† * p.embed B) =
      ((p.left * p.right : ℕ) : ℂ) * Matrix.trace (A† * B) := by
  calc
    Matrix.trace ((p.embed A)† * p.embed B)
        = Matrix.trace (p.embed (A† * B)) := by
            rw [p.embed_conjTranspose, ← p.embed_mul]
    _ = Matrix.trace (castSquare p.dimension_eq (p.tensor (A† * B))) := by
          unfold OneQubitPlacement.embed
          rw [trace_reindexSquare]
    _ = Matrix.trace (p.tensor (A† * B)) := by
          rw [trace_castSquare]
    _ = ((p.left * p.right : ℕ) : ℂ) * Matrix.trace (A† * B) := by
          rw [p.trace_tensor]

private theorem TwoQubitPlacement.trace_embed_mul {n : ℕ}
    (p : TwoQubitPlacement n) (A B : Square 4) :
    Matrix.trace ((p.embed A)† * p.embed B) =
      ((p.left * p.right : ℕ) : ℂ) * Matrix.trace (A† * B) := by
  calc
    Matrix.trace ((p.embed A)† * p.embed B)
        = Matrix.trace (p.embed (A† * B)) := by
            rw [p.embed_conjTranspose, ← p.embed_mul]
    _ = Matrix.trace (castSquare p.dimension_eq (p.tensor (A† * B))) := by
          unfold TwoQubitPlacement.embed
          rw [trace_reindexSquare]
    _ = Matrix.trace (p.tensor (A† * B)) := by
          rw [trace_castSquare]
    _ = ((p.left * p.right : ℕ) : ℂ) * Matrix.trace (A† * B) := by
          rw [p.trace_tensor]

private theorem scaled_ratio_cancel {c d x : ℝ}
    (hc : c ≠ 0) (hd : d ≠ 0) :
    (c * x) ^ 2 / (c * d) ^ 2 = x ^ 2 / d ^ 2 := by
  field_simp [hc, hd]

private theorem OneQubitPlacement.scale_ne_zero {n : ℕ} (p : OneQubitPlacement n) :
    (((p.left * p.right : ℕ) : ℝ)) ≠ 0 := by
  have hleft : p.left ≠ 0 := by
    intro hleft
    have hpow : (2 ^ n : ℕ) ≠ 0 := by
      exact pow_ne_zero n (by norm_num)
    have hzero : (0 : ℕ) = 2 ^ n := by
      simpa [hleft] using p.dimension_eq
    exact hpow hzero.symm
  have hright : p.right ≠ 0 := by
    intro hright
    have hpow : (2 ^ n : ℕ) ≠ 0 := by
      exact pow_ne_zero n (by norm_num)
    have hzero : (0 : ℕ) = 2 ^ n := by
      simpa [hright] using p.dimension_eq
    exact hpow hzero.symm
  exact_mod_cast Nat.mul_ne_zero hleft hright

private theorem TwoQubitPlacement.scale_ne_zero {n : ℕ} (p : TwoQubitPlacement n) :
    (((p.left * p.right : ℕ) : ℝ)) ≠ 0 := by
  have hleft : p.left ≠ 0 := by
    intro hleft
    have hpow : (2 ^ n : ℕ) ≠ 0 := by
      exact pow_ne_zero n (by norm_num)
    have hzero : (0 : ℕ) = 2 ^ n := by
      simpa [hleft] using p.dimension_eq
    exact hpow hzero.symm
  have hright : p.right ≠ 0 := by
    intro hright
    have hpow : (2 ^ n : ℕ) ≠ 0 := by
      exact pow_ne_zero n (by norm_num)
    have hzero : (0 : ℕ) = 2 ^ n := by
      simpa [hright] using p.dimension_eq
    exact hpow hzero.symm
  exact_mod_cast Nat.mul_ne_zero hleft hright

private theorem OneQubitPlacement.dimension_eq_real {n : ℕ} (p : OneQubitPlacement n) :
    ((2 ^ n : ℕ) : ℝ) = (((p.left * p.right : ℕ) : ℝ) * 2) := by
  calc
    ((2 ^ n : ℕ) : ℝ) = (p.left * (2 * p.right) : ℕ) := by
      exact_mod_cast p.dimension_eq.symm
    _ = (((p.left * p.right) * 2 : ℕ) : ℝ) := by
      norm_num [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = (((p.left * p.right : ℕ) : ℝ) * 2) := by
      norm_num

private theorem TwoQubitPlacement.dimension_eq_real {n : ℕ} (p : TwoQubitPlacement n) :
    ((2 ^ n : ℕ) : ℝ) = (((p.left * p.right : ℕ) : ℝ) * 4) := by
  calc
    ((2 ^ n : ℕ) : ℝ) = (p.left * (4 * p.right) : ℕ) := by
      exact_mod_cast p.dimension_eq.symm
    _ = (((p.left * p.right) * 4 : ℕ) : ℝ) := by
      norm_num [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = (((p.left * p.right : ℕ) : ℝ) * 4) := by
      norm_num

private theorem hsDistance_eq_embed_oneQubit {n : ℕ}
    (p : OneQubitPlacement n) (A B : Square 2) :
    hsDistance (p.embed A) (p.embed B) = hsDistance A B := by
  unfold hsDistance
  rw [p.trace_embed_mul, norm_mul, Complex.norm_natCast, p.dimension_eq_real]
  rw [scaled_ratio_cancel (p.scale_ne_zero) (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num

private theorem hsDistance_eq_embed_twoQubit {n : ℕ}
    (p : TwoQubitPlacement n) (A B : Square 4) :
    hsDistance (p.embed A) (p.embed B) = hsDistance A B := by
  unfold hsDistance
  rw [p.trace_embed_mul, norm_mul, Complex.norm_natCast, p.dimension_eq_real]
  rw [scaled_ratio_cancel (p.scale_ne_zero) (by norm_num : (4 : ℝ) ≠ 0)]
  norm_num

private theorem trace_localOnFirst (A : Square 2) :
    Matrix.trace (localOnFirst A) = (2 : ℂ) * Matrix.trace A := by
  unfold localOnFirst
  rw [trace_kron, Matrix.trace_one]
  norm_num [mul_comm]

private theorem trace_localOnSecond (A : Square 2) :
    Matrix.trace (localOnSecond A) = (2 : ℂ) * Matrix.trace A := by
  unfold localOnSecond
  rw [trace_kron, Matrix.trace_one]
  norm_num [mul_comm]

private theorem hsDistance_localOnFirst (A B : Square 2) :
    hsDistance (localOnFirst A) (localOnFirst B) = hsDistance A B := by
  unfold hsDistance
  rw [localOnFirst_conjTranspose, ← localOnFirst_mul, trace_localOnFirst, norm_mul]
  norm_num
  congr 1
  ring_nf

private theorem hsDistance_localOnSecond (A B : Square 2) :
    hsDistance (localOnSecond A) (localOnSecond B) = hsDistance A B := by
  unfold hsDistance
  rw [localOnSecond_conjTranspose, ← localOnSecond_mul, trace_localOnSecond, norm_mul]
  norm_num
  congr 1
  ring_nf

private theorem twoQubitCliffordTCircuitMatrix_onFirst
    (gates : List OneQubitHTPrimitive) :
    twoQubitCliffordTCircuitMatrix (gates.map TwoQubitCliffordTPrimitive.onFirst) =
      localOnFirst (oneQubitHTCircuitMatrix gates) := by
  induction gates with
  | nil =>
      simp [twoQubitCliffordTCircuitMatrix, oneQubitHTCircuitMatrix, localOnFirst,
        TwoControl.one_kron_one]
  | cons gate gates ih =>
      calc
        twoQubitCliffordTCircuitMatrix
            ((gate :: gates).map TwoQubitCliffordTPrimitive.onFirst)
            = localOnFirst (OneQubitHTPrimitive.eval gate) *
                twoQubitCliffordTCircuitMatrix (gates.map TwoQubitCliffordTPrimitive.onFirst) := by
                simp [twoQubitCliffordTCircuitMatrix, TwoQubitCliffordTPrimitive.eval]
        _ = localOnFirst (OneQubitHTPrimitive.eval gate) *
              localOnFirst (oneQubitHTCircuitMatrix gates) := by
                rw [ih]
        _ = localOnFirst
              (OneQubitHTPrimitive.eval gate * oneQubitHTCircuitMatrix gates) := by
                rw [← localOnFirst_mul]
        _ = localOnFirst (oneQubitHTCircuitMatrix (gate :: gates)) := by
                rfl

private theorem twoQubitCliffordTCircuitMatrix_onSecond
    (gates : List OneQubitHTPrimitive) :
    twoQubitCliffordTCircuitMatrix (gates.map TwoQubitCliffordTPrimitive.onSecond) =
      localOnSecond (oneQubitHTCircuitMatrix gates) := by
  induction gates with
  | nil =>
      simp [twoQubitCliffordTCircuitMatrix, oneQubitHTCircuitMatrix, localOnSecond,
        TwoControl.one_kron_one]
  | cons gate gates ih =>
      calc
        twoQubitCliffordTCircuitMatrix
            ((gate :: gates).map TwoQubitCliffordTPrimitive.onSecond)
            = localOnSecond (OneQubitHTPrimitive.eval gate) *
                twoQubitCliffordTCircuitMatrix (gates.map TwoQubitCliffordTPrimitive.onSecond) := by
                simp [twoQubitCliffordTCircuitMatrix, TwoQubitCliffordTPrimitive.eval]
        _ = localOnSecond (OneQubitHTPrimitive.eval gate) *
              localOnSecond (oneQubitHTCircuitMatrix gates) := by
                rw [ih]
        _ = localOnSecond
              (OneQubitHTPrimitive.eval gate * oneQubitHTCircuitMatrix gates) := by
                rw [← localOnSecond_mul]
        _ = localOnSecond (oneQubitHTCircuitMatrix (gate :: gates)) := by
                rfl

/-- Embedded version of Lemma 12 for replacing one `R_z` gate inside an
`n`-qubit circuit. -/
theorem embedded_rz_approximation_by_clifford_t {n : ℕ}
    {R : Square (2 ^ n)} {θ ε : ℝ}
    (hε : 0 < ε)
    (hR : IsEmbeddedOneQubitGate n (rz θ) R) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      hsDistance R (circuitMatrix gates) < ε := by
  rcases lemma12_rz_approximation_by_ht θ hε with ⟨gatesHT, hApprox⟩
  rcases hR with ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
  · refine ⟨embedOneQubitHTCircuit p gatesHT,
      CircuitOver_embedOneQubitHTCircuit_cliffordT p gatesHT, ?_⟩
    rw [circuitMatrix_embedOneQubitHTCircuit, hsDistance_eq_embed_oneQubit]
    exact hApprox
  · refine ⟨embedTwoQubitCliffordTCircuit p
        (gatesHT.map TwoQubitCliffordTPrimitive.onFirst),
      CircuitOver_embedTwoQubitCliffordTCircuit_cliffordT p
        (gatesHT.map TwoQubitCliffordTPrimitive.onFirst), ?_⟩
    rw [circuitMatrix_embedTwoQubitCliffordTCircuit,
      twoQubitCliffordTCircuitMatrix_onFirst, hsDistance_eq_embed_twoQubit,
      hsDistance_localOnFirst]
    exact hApprox
  · refine ⟨embedTwoQubitCliffordTCircuit p
        (gatesHT.map TwoQubitCliffordTPrimitive.onSecond),
      CircuitOver_embedTwoQubitCliffordTCircuit_cliffordT p
        (gatesHT.map TwoQubitCliffordTPrimitive.onSecond), ?_⟩
    rw [circuitMatrix_embedTwoQubitCliffordTCircuit,
      twoQubitCliffordTCircuitMatrix_onSecond, hsDistance_eq_embed_twoQubit,
      hsDistance_localOnSecond]
    exact hApprox

end Universal
end Clifford
end TwoControl

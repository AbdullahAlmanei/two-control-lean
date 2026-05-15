import TwoControl.BlockHelpers
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Eigenspace.Matrix

open scoped Matrix ComplexOrder ComplexStarModule
open Matrix
open Module.End

namespace TwoControl

lemma diag2_one_one : diag2 1 1 = (1 : Square 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2]

lemma diag2_unitary (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    diag2 a b ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2, Complex.conj_mul', ha, hb]

namespace DiagonalizationHelpers

lemma diag2_same_eq_smul_one (a : ℂ) :
    diag2 a a = a • (1 : Square 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2]

end DiagonalizationHelpers

lemma diag2_kron_diag2 (a b c d : ℂ) :
    diag2 a b ⊗ₖ diag2 c d = diag4 (a * c) (a * d) (b * c) (b * d) := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective j
  rw [TwoControl.kron_apply]
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [diag2, diag4, finProdFinEquiv]

namespace DiagonalizationHelpers

lemma one_kron_diag2 (c d : ℂ) :
    (1 : Square 2) ⊗ₖ diag2 c d = diag4 c d c d := by
  rw [← diag2_one_one]
  simpa using diag2_kron_diag2 1 1 c d

lemma diag2_one_right_kron (u : ℂ) :
    diag2 1 u ⊗ₖ (1 : Square 2) = diag4 1 1 u u := by
  rw [← diag2_one_one]
  simpa using diag2_kron_diag2 1 u 1 1

end DiagonalizationHelpers

@[simp] private lemma finProdFinEquiv_00 : (@finProdFinEquiv 2 2 (0, 0) : Fin 4) = 0 := by
  native_decide

@[simp] private lemma finProdFinEquiv_01 : (@finProdFinEquiv 2 2 (0, 1) : Fin 4) = 1 := by
  native_decide

@[simp] private lemma finProdFinEquiv_10 : (@finProdFinEquiv 2 2 (1, 0) : Fin 4) = 2 := by
  native_decide

@[simp] private lemma finProdFinEquiv_11 : (@finProdFinEquiv 2 2 (1, 1) : Fin 4) = 3 := by
  native_decide

lemma controlledGate_diag2_eq (u₀ u₁ : ℂ) :
    controlledGate (diag2 u₀ u₁) = diag4 1 1 u₀ u₁ := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective j
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    try simp [controlledGate, TwoControl.kron, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      proj0, proj1, ketbra, ket0, ket1, diag2, diag4]
  all_goals
    first
    | rw [finProdFinEquiv_00]
    | rw [finProdFinEquiv_01]
    | rw [finProdFinEquiv_10]
    | rw [finProdFinEquiv_11]
  all_goals simp

namespace DiagonalizationHelpers

lemma det_diag2 (a b : ℂ) : (diag2 a b).det = a * b := by
  simp [diag2, Matrix.det_diagonal]

lemma det_of_unitary_diag2_decomp {A : Square 2} {a b : ℂ} {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hA : A = U * diag2 a b * U†) :
    A.det = a * b := by
  have hdetU : U.det * star U.det = 1 := by
    exact (Unitary.mem_iff_self_mul_star).mp (Matrix.det_of_mem_unitary hU)
  calc
    A.det = (U * diag2 a b * U†).det := by rw [hA]
    _ = U.det * (diag2 a b).det * star U.det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    _ = (U.det * star U.det) * (a * b) := by
      rw [det_diag2]
      ring
    _ = a * b := by rw [hdetU, one_mul]

end DiagonalizationHelpers

namespace DiagonalizationHelpers

lemma diag4_unitary (a b c d : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
    diag4 a b c d ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag4, Complex.conj_mul', ha, hb, hc, hd]

lemma diag4_repeat_norms_of_mem_unitaryGroup {c d : ℂ}
    (h : diag4 c d c d ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ‖c‖ = 1 ∧ ‖d‖ = 1 := by
  have h' : (diag4 c d c d)† * diag4 c d c d = 1 := by
    simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'] using h
  have h00 : (starRingEnd ℂ) c * c = 1 := by
    simpa [diag4, Matrix.mul_apply, Fin.sum_univ_succ] using congrFun (congrFun h' 0) 0
  have h11 : (starRingEnd ℂ) d * d = 1 := by
    simpa [diag4, Matrix.mul_apply, Fin.sum_univ_succ] using congrFun (congrFun h' 1) 1
  have hcNormSq : Complex.normSq c = 1 := by
    apply Complex.ofReal_injective
    simpa [Complex.normSq_eq_conj_mul_self] using h00
  have hdNormSq : Complex.normSq d = 1 := by
    apply Complex.ofReal_injective
    simpa [Complex.normSq_eq_conj_mul_self] using h11
  have hcSq : ‖c‖ ^ 2 = 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hcNormSq
  have hdSq : ‖d‖ ^ 2 = 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hdNormSq
  have hc_nonneg : 0 ≤ ‖c‖ := norm_nonneg c
  have hd_nonneg : 0 ≤ ‖d‖ := norm_nonneg d
  constructor
  · have hsq : ‖c‖ ^ 2 = 1 ^ 2 := by simpa using hcSq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hEq | hEq
    · exact hEq
    · exfalso
      have : (0 : ℝ) ≤ -1 := by simpa [hEq] using hc_nonneg
      linarith
  · have hsq : ‖d‖ ^ 2 = 1 ^ 2 := by simpa using hdSq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hEq | hEq
    · exact hEq
    · exfalso
      have : (0 : ℝ) ≤ -1 := by simpa [hEq] using hd_nonneg
      linarith

end DiagonalizationHelpers

private lemma mem_unitary_of_mem_unitaryGroup {n : ℕ} {U : Square n}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : U ∈ unitary (Square n) := by
  rw [Unitary.mem_iff]
  constructor
  · simpa [Matrix.mem_unitaryGroup_iff'] using hU
  · simpa [Matrix.mem_unitaryGroup_iff] using hU

lemma unitary_conj_mem_unitaryGroup {n : ℕ} {P U : Square n}
    (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    U† * P * U ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hPleft : P * P† = 1 := by
    simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff] using hP
  have hPright : P† * P = 1 := by
    simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'] using hP
  have hUleft : U * U† = 1 := by
    simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff] using hU
  have hUright : U† * U = 1 := by
    simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'] using hU
  constructor
  · calc
      (U† * P * U)† * (U† * P * U) = U† * P† * (U * U†) * P * U := by
        simp [Matrix.conjTranspose_mul, mul_assoc]
      _ = U† * (P† * P) * U := by simp [hUleft, mul_assoc]
      _ = 1 := by simp [hPright, hUright]
  · calc
      U† * P * U * (U† * P * U)† = U† * P * (U * U†) * P† * U := by
        simp [Matrix.conjTranspose_mul, mul_assoc]
      _ = U† * (P * P†) * U := by simp [hUleft, mul_assoc]
      _ = 1 := by simp [hPleft, hUright]

lemma conjTranspose_mem_unitaryGroup {n : ℕ} {U : Square n}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    U† ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  simpa [Matrix.conjTranspose, star_eq_conjTranspose] using
    (Matrix.map_star_mem_unitaryGroup_iff).2 ((Matrix.transpose_mem_unitaryGroup_iff).2 hU)

/-- A square complex matrix with pairwise orthogonal columns and prescribed nonnegative
column norms factors as a unitary times a real diagonal matrix. -/
theorem exists_unitary_mul_realDiagonal_of_orthogonal_cols
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (σ : n → ℝ)
    (hσ_nonneg : ∀ i, 0 ≤ σ i)
    (horth : ∀ ⦃i j : n⦄, i ≠ j →
      inner ℂ (WithLp.toLp 2 (M *ᵥ Pi.single i 1))
        (WithLp.toLp 2 (M *ᵥ Pi.single j 1)) = 0)
    (hnorm : ∀ i, ‖WithLp.toLp 2 (M *ᵥ Pi.single i 1)‖ = σ i) :
    ∃ P : Matrix n n ℂ, P ∈ Matrix.unitaryGroup n ℂ ∧
      M = P * Matrix.diagonal (fun i => (σ i : ℂ)) := by
  let s : Set n := {i | σ i ≠ 0}
  let v : n → EuclideanSpace ℂ n :=
    fun i => ((σ i : ℂ)⁻¹) • WithLp.toLp 2 (M *ᵥ Pi.single i 1)
  have hv : Orthonormal ℂ (s.restrict v) := by
    refine ⟨?_, ?_⟩
    · intro i
      have hiσ_ne : σ i ≠ 0 := i.property
      have hvnorm : ‖v i‖ = 1 := by
        calc
          ‖v i‖ = ‖((σ i : ℂ)⁻¹)‖ * ‖WithLp.toLp 2 (M *ᵥ Pi.single i 1)‖ := by
            simp [v, norm_smul]
          _ = (σ i)⁻¹ * σ i := by
            rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (hσ_nonneg i), hnorm i]
          _ = 1 := by
            field_simp [hiσ_ne]
      exact hvnorm
    · intro i j hij
      have hij' : i.1 ≠ j.1 := by
        intro h
        apply hij
        exact Subtype.ext h
      calc
        inner ℂ (s.restrict v i) (s.restrict v j)
            = ((σ i.1 : ℂ)⁻¹) *
                inner ℂ (WithLp.toLp 2 (M *ᵥ Pi.single i.1 1))
                  (WithLp.toLp 2 (M *ᵥ Pi.single j.1 1)) *
                ((σ j.1 : ℂ)⁻¹) := by
                  simp [Set.restrict_apply, v, inner_smul_left, inner_smul_right,
                    mul_assoc, mul_left_comm, mul_comm]
        _ = 0 := by rw [horth hij']; simp
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := by
    exact finrank_euclideanSpace
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq (v := v) hcard
  let std : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := EuclideanSpace.basisFun n ℂ
  let P : Matrix n n ℂ := std.toBasis.toMatrix b.toBasis
  have hP : P ∈ Matrix.unitaryGroup n ℂ := by
    simpa [P] using std.toMatrix_orthonormalBasis_mem_unitary b
  have hPcol (i : n) : P *ᵥ Pi.single i 1 = ⇑(b i) := by
    rw [Matrix.mulVec_single_one]
    ext j
    simp [P, std, Module.Basis.toMatrix_apply]
  have hcol (i : n) : M *ᵥ Pi.single i 1 = (σ i : ℂ) • ⇑(b i) := by
    apply (WithLp.toLp_injective (p := 2))
    by_cases hi : i ∈ s
    · have hiσ_ne : σ i ≠ 0 := by
        simpa [s] using hi
      have hiσc_ne : (σ i : ℂ) ≠ 0 := by
        exact_mod_cast hiσ_ne
      calc
        WithLp.toLp 2 (M *ᵥ Pi.single i 1)
            = (σ i : ℂ) • (((σ i : ℂ)⁻¹) • WithLp.toLp 2 (M *ᵥ Pi.single i 1)) := by
                simp [smul_smul, hiσc_ne]
        _ = (σ i : ℂ) • v i := by
              rfl
        _ = (σ i : ℂ) • b i := by
              rw [hb i hi]
    · have hiσ_zero : σ i = 0 := by
        simpa [s] using hi
      have hzero : WithLp.toLp 2 (M *ᵥ Pi.single i 1) = 0 := by
        apply norm_eq_zero.mp
        simpa [hiσ_zero] using hnorm i
      calc
        WithLp.toLp 2 (M *ᵥ Pi.single i 1) = 0 := hzero
        _ = (σ i : ℂ) • b i := by simp [hiσ_zero]
  refine ⟨P, hP, ?_⟩
  ext r c
  have hcolEq : M *ᵥ Pi.single c (1 : ℂ) =
      (P * Matrix.diagonal (fun i => (σ i : ℂ))) *ᵥ Pi.single c (1 : ℂ) := by
    have hs : ((σ c : ℂ) • (Pi.single c (1 : ℂ) : n → ℂ)) =
        (Pi.single c ((σ c : ℂ) * 1) : n → ℂ) := by
      ext i
      by_cases hi : i = c
      · subst hi
        simp [Pi.smul_apply]
      · simp [Pi.smul_apply, hi]
    calc
      M *ᵥ Pi.single c (1 : ℂ) = (σ c : ℂ) • ⇑(b c) := hcol c
      _ = (σ c : ℂ) • (P *ᵥ Pi.single c (1 : ℂ)) := by rw [hPcol c]
      _ = P *ᵥ (Matrix.diagonal (fun i => (σ i : ℂ)) *ᵥ Pi.single c (1 : ℂ)) := by
        rw [Matrix.diagonal_mulVec_single, ← Matrix.mulVec_smul]
        rw [hs]
      _ = (P * Matrix.diagonal (fun i => (σ i : ℂ))) *ᵥ Pi.single c (1 : ℂ) := by
        rw [← Matrix.mulVec_mulVec]
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun hcolEq r

/-- If the Gram matrix of a square complex matrix is already a real diagonal matrix, then the
matrix factors as a unitary times the diagonal of the square roots of those entries. -/
theorem exists_unitary_mul_realDiagonal_of_gram_eq_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (diagVals : n → ℝ)
    (hDiagVals_nonneg : ∀ i, 0 ≤ diagVals i)
    (hGram : M† * M = Matrix.diagonal (fun i => (diagVals i : ℂ))) :
    ∃ P : Matrix n n ℂ, P ∈ Matrix.unitaryGroup n ℂ ∧
      M = P * Matrix.diagonal (fun i => ((Real.sqrt (diagVals i)) : ℂ)) := by
  have horth : ∀ ⦃i j : n⦄, i ≠ j →
      inner ℂ (WithLp.toLp 2 (M *ᵥ Pi.single i 1))
        (WithLp.toLp 2 (M *ᵥ Pi.single j 1)) = 0 := by
    intro i j hij
    calc
      inner ℂ (WithLp.toLp 2 (M *ᵥ Pi.single i 1))
          (WithLp.toLp 2 (M *ᵥ Pi.single j 1)) = (M† * M) i j := by
            simpa [Matrix.mulVec_single_one] using inner_matrix_col_col M M i j
      _ = (Matrix.diagonal (fun i => (diagVals i : ℂ))) i j := by rw [hGram]
      _ = 0 := by simp [Matrix.diagonal, hij]
  have hnorm : ∀ i, ‖WithLp.toLp 2 (M *ᵥ Pi.single i 1)‖ = Real.sqrt (diagVals i) := by
    intro i
    have hdiag : inner ℂ (WithLp.toLp 2 (M *ᵥ Pi.single i 1))
        (WithLp.toLp 2 (M *ᵥ Pi.single i 1)) = (diagVals i : ℂ) := by
      calc
        inner ℂ (WithLp.toLp 2 (M *ᵥ Pi.single i 1))
            (WithLp.toLp 2 (M *ᵥ Pi.single i 1)) = (M† * M) i i := by
              simpa [Matrix.mulVec_single_one] using inner_matrix_col_col M M i i
        _ = (Matrix.diagonal (fun j => (diagVals j : ℂ))) i i := by rw [hGram]
        _ = (diagVals i : ℂ) := by simp
    have hsq_complex : (((‖WithLp.toLp 2 (M *ᵥ Pi.single i 1)‖ ^ 2 : ℝ)) : ℂ) = (diagVals i : ℂ) := by
      simpa [inner_self_eq_norm_sq_to_K] using hdiag
    have hsq : ‖WithLp.toLp 2 (M *ᵥ Pi.single i 1)‖ ^ 2 = diagVals i := by
      exact_mod_cast hsq_complex
    have hnorm_nonneg : 0 ≤ ‖WithLp.toLp 2 (M *ᵥ Pi.single i 1)‖ := norm_nonneg _
    have hsqrt_nonneg : 0 ≤ Real.sqrt (diagVals i) := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt (diagVals i)) ^ 2 = diagVals i := Real.sq_sqrt (hDiagVals_nonneg i)
    nlinarith
  exact exists_unitary_mul_realDiagonal_of_orthogonal_cols M (fun i => Real.sqrt (diagVals i))
    (fun i => Real.sqrt_nonneg _) horth hnorm

lemma conjTranspose_diagonal {n : ℕ} (d : Fin n → ℂ) :
    (Matrix.diagonal d)† = Matrix.diagonal (star d) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]
    have hji : j ≠ i := by
      intro h
      exact hij h.symm
    simp [Matrix.diagonal_apply_ne, hij, hji]

lemma diagonal_unitary {n : ℕ} (d : Fin n → ℂ)
    (hd : ∀ i, ‖d i‖ = 1) :
    Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.2
  calc
    (Matrix.diagonal d)† * Matrix.diagonal d
        = Matrix.diagonal (fun i => (starRingEnd ℂ) (d i) * d i) := by
            calc
              (Matrix.diagonal d)† * Matrix.diagonal d
                  = Matrix.diagonal (star d) * Matrix.diagonal d := by
                      rw [conjTranspose_diagonal]
              _ = Matrix.diagonal (fun i => (starRingEnd ℂ) (d i) * d i) := by
                  simpa using (Matrix.diagonal_mul_diagonal (d₁ := star d) (d₂ := d))
    _ = 1 := by
          ext i j
          by_cases hij : i = j
          · subst j
            simp [Complex.conj_mul', hd i]
          · simp [hij]

lemma diagonal_norms_of_mem_unitaryGroup {n : ℕ} {d : Fin n → ℂ}
    (h : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∀ i, ‖d i‖ = 1 := by
  intro i
  have hdiag : Matrix.diagonal (fun i => (starRingEnd ℂ) (d i) * d i) = (1 : Square n) := by
    calc
      Matrix.diagonal (fun i => (starRingEnd ℂ) (d i) * d i)
          = Matrix.diagonal (star d) * Matrix.diagonal d := by
            simpa using (Matrix.diagonal_mul_diagonal (d₁ := star d) (d₂ := d)).symm
      _ = (Matrix.diagonal d)† * Matrix.diagonal d := by
            rw [conjTranspose_diagonal]
      _ = 1 := Matrix.mem_unitaryGroup_iff'.mp h
  have hii : (starRingEnd ℂ) (d i) * d i = 1 := by
    simpa using congrFun (congrFun hdiag i) i
  have hNormSq : Complex.normSq (d i) = 1 := by
    apply Complex.ofReal_injective
    simpa [Complex.normSq_eq_conj_mul_self] using hii
  have hSq : ‖d i‖ ^ 2 = 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hNormSq
  have hnonneg : 0 ≤ ‖d i‖ := norm_nonneg _
  have hsq : ‖d i‖ ^ 2 = 1 ^ 2 := by simpa using hSq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hEq | hEq
  · exact hEq
  · exfalso
    have : (0 : ℝ) ≤ -1 := by simpa [hEq] using hnonneg
    linarith

set_option maxHeartbeats 10000000 in
lemma unitary_diagonal_exists {N : ℕ} (P : Square N)
    (hP : P ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ∃ d : Fin N → ℂ, ∃ U : Square N,
      (∀ i, ‖d i‖ = 1) ∧
      U ∈ Matrix.unitaryGroup (Fin N) ℂ ∧
      P = U * Matrix.diagonal d * U† := by
  let std : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
    EuclideanSpace.basisFun (Fin N) ℂ
  let ReP : Square N := (((realPart P : selfAdjoint (Square N)) : Square N))
  let ImP : Square N := (((imaginaryPart P : selfAdjoint (Square N)) : Square N))
  let A : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    Matrix.toLinAlgEquiv std.toBasis ReP
  let B : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    Matrix.toLinAlgEquiv std.toBasis ImP
  have hReHerm : ReP.IsHermitian := by
    dsimp [ReP]
    exact (show IsSelfAdjoint ((((realPart P : selfAdjoint (Square N)) : Square N))) from
      (realPart P : selfAdjoint (Square N)).property).isHermitian
  have hImHerm : ImP.IsHermitian := by
    dsimp [ImP]
    exact (show IsSelfAdjoint ((((imaginaryPart P : selfAdjoint (Square N)) : Square N))) from
      (imaginaryPart P : selfAdjoint (Square N)).property).isHermitian
  have hA : A.IsSymmetric := by
    change (Matrix.toLin std.toBasis std.toBasis ReP).IsSymmetric
    exact (Matrix.isSymmetric_toLin_iff std).2 hReHerm
  have hB : B.IsSymmetric := by
    change (Matrix.toLin std.toBasis std.toBasis ImP).IsSymmetric
    exact (Matrix.isSymmetric_toLin_iff std).2 hImHerm
  have hPnormal : IsStarNormal P := by
    rw [isStarNormal_iff]
    have hleft : P * star P = 1 := by
      simpa [Matrix.mem_unitaryGroup_iff] using hP
    have hright : star P * P = 1 := by
      simpa [Matrix.mem_unitaryGroup_iff'] using hP
    exact hright.trans hleft.symm
  have hCommMat : Commute ReP ImP := by
    dsimp [ReP, ImP]
    exact isStarNormal_iff_commute_realPart_imaginaryPart.mp hPnormal
  have hComm : Commute A B := by
    apply (LinearMap.toMatrixAlgEquiv std.toBasis).injective
    simpa [A, B] using hCommMat.eq
  let F : ℂ × ℂ → Submodule ℂ (EuclideanSpace ℂ (Fin N)) :=
    fun i => eigenspace A i.2 ⊓ eigenspace B i.1
  let K : Type :=
    {i : ℂ × ℂ // F i ≠ ⊥}
  let key : K → Eigenvalues B × Eigenvalues A := fun i =>
    ⟨⟨i.1.1, by
        intro hbot
        exact i.2 (by simp [F, hbot])⟩,
      ⟨i.1.2, by
        intro hbot
        exact i.2 (by simp [F, hbot])⟩⟩
  have hkey_inj : Function.Injective key := by
    intro i j hij
    apply Subtype.ext
    exact Prod.ext
      (by exact congrArg Subtype.val (congrArg Prod.fst hij))
      (by exact congrArg Subtype.val (congrArg Prod.snd hij))
  letI : Finite K := Finite.of_injective key hkey_inj
  letI : Fintype K := Fintype.ofFinite K
  have hTopAll :
      (⨆ i : ℂ × ℂ, F i) = ⊤ := by
    rw [iSup_prod]
    have htop :=
      LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hA hB hComm
    rw [iSup_comm] at htop
    simpa [F] using htop
  have hTop :
      (⨆ i : K, F i.1) = ⊤ := by
    rw [iSup_ne_bot_subtype]
    exact hTopAll
  have hOrth :
      OrthogonalFamily ℂ (fun i : K => F i.1) fun i => (F i.1).subtypeₗᵢ := by
    simpa [F] using
      (LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB).comp
        Subtype.val_injective
  have hInternal :
      DirectSum.IsInternal (fun i : K => F i.1) := by
    refine hOrth.isInternal_iff.mpr ?_
    rw [hTop, Submodule.top_orthogonal_eq_bot]
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = N := by
    simpa using
      (finrank_euclideanSpace : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) =
        Fintype.card (Fin N))
  let basis : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
    hInternal.subordinateOrthonormalBasis hdim hOrth
  let κ : Fin N → K :=
    fun i => hInternal.subordinateOrthonormalBasisIndex hdim i hOrth
  let χ : Fin N → ℂ × ℂ := fun i => (κ i).1
  have hb_sub (i : Fin N) : basis i ∈ eigenspace A (χ i).2 ⊓ eigenspace B (χ i).1 := by
    simpa [basis, κ, χ, F] using
      hInternal.subordinateOrthonormalBasis_subordinate (hn := hdim) i hOrth
  have hbA (i : Fin N) : A (basis i) = (χ i).2 • basis i := by
    exact Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp (hb_sub i)).1
  have hbB (i : Fin N) : B (basis i) = (χ i).1 • basis i := by
    exact Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp (hb_sub i)).2
  let d : Fin N → ℂ := fun i => (χ i).2 + Complex.I * (χ i).1
  have hP_lin : Matrix.toLinAlgEquiv std.toBasis P = A + Complex.I • B := by
    dsimp [A, B]
    simpa [ReP, ImP] using
      congrArg (Matrix.toLinAlgEquiv std.toBasis)
        (realPart_add_I_smul_imaginaryPart P).symm
  have hP_apply_basis : ∀ i : Fin N, Matrix.toLinAlgEquiv std.toBasis P (basis i) = d i • basis i := by
    intro i
    have htmp := congrArg (fun f => f (basis i)) hP_lin
    simpa [d, hbA i, hbB i, add_smul, smul_smul] using htmp
  have hP_apply_basis' : ∀ i : Fin N, P.toEuclideanLin (basis i) = d i • basis i := by
    intro i
    change Matrix.toLinAlgEquiv (EuclideanSpace.basisFun (Fin N) ℂ).toBasis P (basis i) =
      d i • basis i
    simpa [std] using hP_apply_basis i
  let U : Square N := std.toBasis.toMatrix basis
  have hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    simpa [U] using std.toMatrix_orthonormalBasis_mem_unitary basis
  have hU_apply (i : Fin N) : U *ᵥ Pi.single i 1 = ⇑(basis i) := by
    rw [Matrix.mulVec_single_one]
    ext j
    simp [U, std, Module.Basis.toMatrix_apply]
  have hstarU_apply (i : Fin N) : (star U) *ᵥ ⇑(basis i) = Pi.single i 1 := by
    have hU' : star U * U = 1 := by
      simpa [Matrix.mem_unitaryGroup_iff'] using hU
    calc
      (star U) *ᵥ ⇑(basis i) = (star U) *ᵥ (U *ᵥ Pi.single i 1) := by rw [hU_apply i]
      _ = (star U * U) *ᵥ Pi.single i 1 := by rw [mulVec_mulVec]
      _ = (1 : Square N) *ᵥ Pi.single i 1 := by rw [hU']
      _ = Pi.single i 1 := by
        rw [Matrix.mulVec_single_one]
        ext j
        simp [Matrix.one_apply, Pi.single_apply]
  have hP_apply (i : Fin N) : P *ᵥ ⇑(basis i) = d i • ⇑(basis i) := by
    simpa [Matrix.toEuclideanLin, Matrix.ofLp_toLpLin] using
      congrArg WithLp.ofLp (hP_apply_basis' i)
  have hdiag_col (i : Fin N) :
      (star U * P * U) *ᵥ Pi.single i 1 = (Matrix.diagonal d) *ᵥ Pi.single i 1 := by
    calc
      (star U * P * U) *ᵥ Pi.single i 1 = (star U) *ᵥ (P *ᵥ (U *ᵥ Pi.single i 1)) := by
        rw [mulVec_mulVec, mulVec_mulVec]
      _ = (star U) *ᵥ (P *ᵥ ⇑(basis i)) := by rw [hU_apply i]
      _ = (star U) *ᵥ (d i • ⇑(basis i)) := by rw [hP_apply i]
      _ = d i • ((star U) *ᵥ ⇑(basis i)) := by rw [Matrix.mulVec_smul]
      _ = d i • (Pi.single i (1 : ℂ) : Fin N → ℂ) := by
        exact congrArg (fun v : Fin N → ℂ => d i • v) (hstarU_apply i)
      _ = (Matrix.diagonal d) *ᵥ Pi.single i 1 := by
        rw [Matrix.diagonal_mulVec_single]
        ext j
        by_cases hji : j = i
        · subst hji
          simp [Pi.smul_apply, Pi.single_apply]
        · simp [Pi.smul_apply, Pi.single_apply, hji]
  have hdiag : star U * P * U = Matrix.diagonal d := by
    ext r c
    have hcolEq : ((star U * P * U) *ᵥ Pi.single c 1) r =
        ((Matrix.diagonal d) *ᵥ Pi.single c 1) r := by
      exact congrFun (hdiag_col c) r
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hcolEq
  have hP_diag : P = U * Matrix.diagonal d * U† := by
    have hUU : U * U† = 1 := by
      simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff] using hU
    have hdiag' : U† * P * U = Matrix.diagonal d := by
      simpa [star_eq_conjTranspose] using hdiag
    calc
      P = (U * U†) * P * (U * U†) := by simp [hUU]
      _ = U * (U† * P * U) * U† := by simp [mul_assoc]
      _ = U * Matrix.diagonal d * U† := by rw [hdiag']
  have hdiag_unitary : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    have hconj : U† * P * U = Matrix.diagonal d := by
      simpa [star_eq_conjTranspose] using hdiag
    simpa [hconj] using unitary_conj_mem_unitaryGroup hP hU
  have hnorms := diagonal_norms_of_mem_unitaryGroup hdiag_unitary
  exact ⟨d, U, hnorms, hU, hP_diag⟩

private lemma diag2_norms_of_mem_unitaryGroup {a b : ℂ}
    (h : diag2 a b ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖a‖ = 1 ∧ ‖b‖ = 1 := by
  have h' : (diag2 a b)† * diag2 a b = 1 := by
    simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'] using h
  have h00 : (starRingEnd ℂ) a * a = 1 := by
    simpa [diag2, Matrix.mul_apply] using congrFun (congrFun h' 0) 0
  have h11 : (starRingEnd ℂ) b * b = 1 := by
    simpa [diag2, Matrix.mul_apply] using congrFun (congrFun h' 1) 1
  have haNormSq : Complex.normSq a = 1 := by
    apply Complex.ofReal_injective
    simpa [Complex.normSq_eq_conj_mul_self] using h00
  have hbNormSq : Complex.normSq b = 1 := by
    apply Complex.ofReal_injective
    simpa [Complex.normSq_eq_conj_mul_self] using h11
  have haSq : ‖a‖ ^ 2 = 1 := by
    simpa [Complex.normSq_eq_norm_sq] using haNormSq
  have hbSq : ‖b‖ ^ 2 = 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hbNormSq
  have ha_nonneg : 0 ≤ ‖a‖ := norm_nonneg a
  have hb_nonneg : 0 ≤ ‖b‖ := norm_nonneg b
  constructor
  · have hsq : ‖a‖ ^ 2 = 1 ^ 2 := by simpa using haSq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hEq | hEq
    · exact hEq
    · exfalso
      have : (0 : ℝ) ≤ -1 := by simpa [hEq] using ha_nonneg
      linarith
  · have hsq : ‖b‖ ^ 2 = 1 ^ 2 := by simpa using hbSq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hEq | hEq
    · exact hEq
    · exfalso
      have : (0 : ℝ) ≤ -1 := by simpa [hEq] using hb_nonneg
      linarith

set_option maxHeartbeats 10000000 in
lemma unitary_diag2_exists (P : Square 2) (hP : P ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (a b : ℂ) (U : Square 2),
      ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      P = U * diag2 a b * U† := by
  let std : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
    EuclideanSpace.basisFun (Fin 2) ℂ
  let ReP : Square 2 := (((realPart P : selfAdjoint (Square 2)) : Square 2))
  let ImP : Square 2 := (((imaginaryPart P : selfAdjoint (Square 2)) : Square 2))
  let A : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
    Matrix.toLinAlgEquiv std.toBasis ReP
  let B : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
    Matrix.toLinAlgEquiv std.toBasis ImP
  have hReHerm : ReP.IsHermitian := by
    dsimp [ReP]
    exact (show IsSelfAdjoint ((((realPart P : selfAdjoint (Square 2)) : Square 2))) from
      (realPart P : selfAdjoint (Square 2)).property).isHermitian
  have hImHerm : ImP.IsHermitian := by
    dsimp [ImP]
    exact (show IsSelfAdjoint ((((imaginaryPart P : selfAdjoint (Square 2)) : Square 2))) from
      (imaginaryPart P : selfAdjoint (Square 2)).property).isHermitian
  have hA : A.IsSymmetric := by
    change (Matrix.toLin std.toBasis std.toBasis ReP).IsSymmetric
    exact (Matrix.isSymmetric_toLin_iff std).2 hReHerm
  have hB : B.IsSymmetric := by
    change (Matrix.toLin std.toBasis std.toBasis ImP).IsSymmetric
    exact (Matrix.isSymmetric_toLin_iff std).2 hImHerm
  have hPnormal : IsStarNormal P := by
    rw [isStarNormal_iff]
    have hleft : P * star P = 1 := by
      simpa [Matrix.mem_unitaryGroup_iff] using hP
    have hright : star P * P = 1 := by
      simpa [Matrix.mem_unitaryGroup_iff'] using hP
    exact hright.trans hleft.symm
  have hCommMat : Commute ReP ImP := by
    dsimp [ReP, ImP]
    exact isStarNormal_iff_commute_realPart_imaginaryPart.mp hPnormal
  have hComm : Commute A B := by
    apply (LinearMap.toMatrixAlgEquiv std.toBasis).injective
    simpa [A, B] using hCommMat.eq
  let F : ℂ × ℂ → Submodule ℂ (EuclideanSpace ℂ (Fin 2)) :=
    fun i => eigenspace A i.2 ⊓ eigenspace B i.1
  let K : Type :=
    {i : ℂ × ℂ // F i ≠ ⊥}
  let key : K → Eigenvalues B × Eigenvalues A := fun i =>
    ⟨⟨i.1.1, by
        intro hbot
        exact i.2 (by simp [F, hbot])⟩,
      ⟨i.1.2, by
        intro hbot
        exact i.2 (by simp [F, hbot])⟩⟩
  have hkey_inj : Function.Injective key := by
    intro i j hij
    apply Subtype.ext
    exact Prod.ext
      (by exact congrArg Subtype.val (congrArg Prod.fst hij))
      (by exact congrArg Subtype.val (congrArg Prod.snd hij))
  letI : Finite K := Finite.of_injective key hkey_inj
  letI : Fintype K := Fintype.ofFinite K
  have hTopAll :
      (⨆ i : ℂ × ℂ, F i) = ⊤ := by
    rw [iSup_prod]
    have htop :=
      LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hA hB hComm
    rw [iSup_comm] at htop
    simpa [F] using htop
  have hTop :
      (⨆ i : K, F i.1) = ⊤ := by
    rw [iSup_ne_bot_subtype]
    exact hTopAll
  have hOrth :
      OrthogonalFamily ℂ (fun i : K => F i.1) fun i => (F i.1).subtypeₗᵢ := by
    simpa [F] using
      (LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB).comp
        Subtype.val_injective
  have hInternal :
      DirectSum.IsInternal (fun i : K => F i.1) := by
    refine hOrth.isInternal_iff.mpr ?_
    rw [hTop, Submodule.top_orthogonal_eq_bot]
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) = 2 := by
    simp
  let basis : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
    hInternal.subordinateOrthonormalBasis hdim hOrth
  let κ : Fin 2 → K :=
    fun i => hInternal.subordinateOrthonormalBasisIndex hdim i hOrth
  let χ : Fin 2 → ℂ × ℂ := fun i => (κ i).1
  have hb_sub (i : Fin 2) : basis i ∈ eigenspace A (χ i).2 ⊓ eigenspace B (χ i).1 := by
    simpa [basis, κ, χ, F] using hInternal.subordinateOrthonormalBasis_subordinate (hn := hdim) i hOrth
  have hbA (i : Fin 2) : A (basis i) = (χ i).2 • basis i := by
    exact Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp (hb_sub i)).1
  have hbB (i : Fin 2) : B (basis i) = (χ i).1 • basis i := by
    exact Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp (hb_sub i)).2
  have hb_ne_zero (i : Fin 2) : basis i ≠ 0 := by
    exact basis.orthonormal.ne_zero i
  let ev : Fin 2 → ℂ := fun i => (χ i).2 + Complex.I * (χ i).1
  have hP_lin : Matrix.toLinAlgEquiv std.toBasis P = A + Complex.I • B := by
    dsimp [A, B]
    simpa [ReP, ImP] using
      congrArg (Matrix.toLinAlgEquiv std.toBasis)
        (realPart_add_I_smul_imaginaryPart P).symm
  have hP_apply_basis : ∀ i : Fin 2, Matrix.toLinAlgEquiv std.toBasis P (basis i) = ev i • basis i := by
    intro i
    have htmp := congrArg (fun f => f (basis i)) hP_lin
    simpa [ev, hbA i, hbB i, add_smul, smul_smul] using htmp
  have hP_apply_basis' : ∀ i : Fin 2, P.toEuclideanLin (basis i) = ev i • basis i := by
    intro i
    change Matrix.toLinAlgEquiv (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis P (basis i) =
      ev i • basis i
    simpa [std] using hP_apply_basis i
  let U : Square 2 := std.toBasis.toMatrix basis
  have hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    simpa [U] using std.toMatrix_orthonormalBasis_mem_unitary basis
  have hU_apply (i : Fin 2) : U *ᵥ Pi.single i 1 = ⇑(basis i) := by
    rw [Matrix.mulVec_single_one]
    ext j
    simp [U, std, Module.Basis.toMatrix_apply]
  have hstarU_apply (i : Fin 2) : (star U) *ᵥ ⇑(basis i) = Pi.single i 1 := by
    have hU' : star U * U = 1 := by
      simpa [Matrix.mem_unitaryGroup_iff'] using hU
    calc
      (star U) *ᵥ ⇑(basis i) = (star U) *ᵥ (U *ᵥ Pi.single i 1) := by rw [hU_apply i]
      _ = (star U * U) *ᵥ Pi.single i 1 := by rw [mulVec_mulVec]
      _ = (1 : Square 2) *ᵥ Pi.single i 1 := by rw [hU']
      _ = Pi.single i 1 := by
        rw [Matrix.mulVec_single_one]
        ext j
        simp [Matrix.one_apply, Pi.single_apply]
  have hP_apply (i : Fin 2) : P *ᵥ ⇑(basis i) = ev i • ⇑(basis i) := by
    simpa [Matrix.toEuclideanLin, Matrix.ofLp_toLpLin] using
      congrArg WithLp.ofLp (hP_apply_basis' i)
  have hdiag : star U * P * U = diag2 (ev 0) (ev 1) := by
    apply Matrix.toEuclideanLin.injective
    refine (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis.ext ?_
    intro i
    fin_cases i
    · apply PiLp.ext
      intro j
      fin_cases j <;>
        simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
          hU_apply, hstarU_apply, hP_apply, diag2]
    · apply PiLp.ext
      intro j
      fin_cases j <;>
        simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
          hU_apply, hstarU_apply, hP_apply, diag2]
  have hP_diag : P = U * diag2 (ev 0) (ev 1) * U† := by
    have hUU : U * U† = 1 := by
      simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff] using hU
    have hstarUU : U† * U = 1 := by
      simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'] using hU
    have hdiag' : U† * P * U = diag2 (ev 0) (ev 1) := by
      simpa [star_eq_conjTranspose] using hdiag
    calc
      P = (U * U†) * P * (U * U†) := by simp [hUU]
      _ = U * (U† * P * U) * U† := by simp [mul_assoc]
      _ = U * diag2 (ev 0) (ev 1) * U† := by rw [hdiag']
  have hdiag_unitary : diag2 (ev 0) (ev 1) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    have hconj : U† * P * U = diag2 (ev 0) (ev 1) := by
      simpa [star_eq_conjTranspose] using hdiag
    simpa [hconj] using unitary_conj_mem_unitaryGroup hP hU
  have hnorms := diag2_norms_of_mem_unitaryGroup hdiag_unitary
  exact ⟨ev 0, ev 1, U, hnorms.1, hnorms.2, hU, hP_diag⟩

lemma kron_mul_two (A B C D : Square 2) :
    (A * B) ⊗ₖ (C * D) = (A ⊗ₖ C) * (B ⊗ₖ D) := by
  simpa [TwoControl.kron, Matrix.reindexAlgEquiv_apply] using
    congrArg (Matrix.reindexAlgEquiv ℂ ℂ (@finProdFinEquiv 2 2))
      (Matrix.mul_kronecker_mul A B C D)

lemma conjTranspose_kron_two (A B : Square 2) :
    (A ⊗ₖ B)† = A† ⊗ₖ B† := by
  simpa [TwoControl.kron, Matrix.reindexAlgEquiv_apply, star_eq_conjTranspose] using
    congrArg (Matrix.reindexAlgEquiv ℂ ℂ (@finProdFinEquiv 2 2))
      (Matrix.conjTranspose_kronecker A B)

lemma kron_unitary_two (U V : Square 2)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    U ⊗ₖ V ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  calc
    star (U ⊗ₖ V) * (U ⊗ₖ V) = (U† ⊗ₖ V†) * (U ⊗ₖ V) := by
      rw [star_eq_conjTranspose, conjTranspose_kron_two]
    _ = (U† * U) ⊗ₖ (V† * V) := by
      rw [← kron_mul_two]
    _ = (1 : Square 2) ⊗ₖ (1 : Square 2) := by
      rw [show U† * U = 1 by simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'] using hU,
        show V† * V = 1 by simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'] using hV]
    _ = (1 : Square 4) := by
      simpa using TwoControl.one_kron_one 2 2

lemma charpoly_unitary_conj {n : ℕ} (U D : Square n)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (U * D * U†).charpoly = D.charpoly := by
  have hU' : U† * U = 1 := by
    simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'] using hU
  calc
    (U * D * U†).charpoly = (U * (D * U†)).charpoly := by simp [mul_assoc]
    _ = ((D * U†) * U).charpoly := Matrix.charpoly_mul_comm _ _
    _ = D.charpoly := by simp [mul_assoc, hU']

lemma roots_charpoly_diag4 (a b c d : ℂ) :
    (diag4 a b c d).charpoly.roots = ({a, b, c, d} : Multiset ℂ) := by
  rw [diag4, Matrix.charpoly_diagonal,
    Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
  simp [Polynomial.roots_X_sub_C]
  rfl

end TwoControl

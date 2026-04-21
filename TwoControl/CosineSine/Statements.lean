import TwoControl.CosineSine.Definitions
import TwoControl.KronHelpers
import TwoControl.StateHelpers
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open scoped ComplexOrder
open Matrix
open TwoControl.StateHelpers

namespace TwoControl
namespace CosineSine

private lemma blockify_kron_right_two (A B : Square 2) :
    blockify (n := 2) (A ⊗ₖ B) =
      Matrix.fromBlocks
        (A 0 0 • B)
        (A 0 1 • B)
        (A 1 0 • B)
        (A 1 1 • B) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simpa [blockify] using (TwoControl.kron_apply (A := A) (B := B) 0 i 0 j)
  · simpa [blockify] using (TwoControl.kron_apply (A := A) (B := B) 0 i 1 j)
  · simpa [blockify] using (TwoControl.kron_apply (A := A) (B := B) 1 i 0 j)
  · simpa [blockify] using (TwoControl.kron_apply (A := A) (B := B) 1 i 1 j)

private lemma blockify_blockDiag2 (P₀ P₁ : Square 2) :
    blockify (n := 2) (blockDiag2 P₀ P₁) =
      Matrix.fromBlocks P₀ 0 0 P₁ := by
  rw [blockDiag2, blockify_add, blockify_kron_right_two, blockify_kron_right_two]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, ketbra, ket0, ket1]

private lemma blockify_conditionalRy (θ₀ θ₁ : ℝ) :
    blockify (n := 2) (conditionalRy θ₀ θ₁) =
      Matrix.fromBlocks
        (realDiag2 (Real.cos (θ₀ / 2)) (Real.cos (θ₁ / 2)))
        (- realDiag2 (Real.sin (θ₀ / 2)) (Real.sin (θ₁ / 2)))
        (realDiag2 (Real.sin (θ₀ / 2)) (Real.sin (θ₁ / 2)))
        (realDiag2 (Real.cos (θ₀ / 2)) (Real.cos (θ₁ / 2))) := by
  rw [conditionalRy, blockify_add, blockify_kron_right_two, blockify_kron_right_two]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [realDiag2, ry, diag2, proj0, proj1, ketbra, ket0, ket1]


private lemma conj_complex_half_angle (θ : ℝ) :
    (starRingEnd ℂ) (↑θ / 2 : ℂ) = (↑θ / 2 : ℂ) := by
  rw [div_eq_mul_inv, map_mul, map_inv₀]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
    simpa using (Complex.conj_ofReal (2 : ℝ))
  rw [h2]
  rw [show (starRingEnd ℂ) (↑θ : ℂ) = (↑θ : ℂ) by simp]

private lemma conj_complex_cos_half (θ : ℝ) :
    (starRingEnd ℂ) (Complex.cos (↑θ / 2)) = Complex.cos (↑θ / 2) := by
  calc
    (starRingEnd ℂ) (Complex.cos (↑θ / 2)) = Complex.cos ((starRingEnd ℂ) (↑θ / 2)) := by
      simpa using (Complex.cos_conj (x := (↑θ / 2 : ℂ))).symm
    _ = Complex.cos (↑θ / 2) := by
      rw [conj_complex_half_angle θ]

private lemma conj_complex_sin_half (θ : ℝ) :
    (starRingEnd ℂ) (Complex.sin (↑θ / 2)) = Complex.sin (↑θ / 2) := by
  calc
    (starRingEnd ℂ) (Complex.sin (↑θ / 2)) = Complex.sin ((starRingEnd ℂ) (↑θ / 2)) := by
      simpa using (Complex.sin_conj (x := (↑θ / 2 : ℂ))).symm
    _ = Complex.sin (↑θ / 2) := by
      rw [conj_complex_half_angle θ]

private lemma gram_entry_eq_dot (M : Square 2) (i j : Fin 2) :
    (M† * M) i j = star (M.mulVec (Pi.single i 1)) ⬝ᵥ M.mulVec (Pi.single j 1) := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma row_cross_entry_eq_dot (M N : Square 2) (i j : Fin 2) :
    (M * N†) i j = star (M†.mulVec (Pi.single i 1)) ⬝ᵥ N†.mulVec (Pi.single j 1) := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma matrix_eq_of_mulVec_ket (M N : Square 2)
    (h0 : M.mulVec ket0 = N.mulVec ket0)
    (h1 : M.mulVec ket1 = N.mulVec ket1) :
    M = N := by
  ext i j
  fin_cases j
  · simpa [ket0, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h0 i
  · simpa [ket1, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h1 i

private lemma realDiag2_mulVec_ket0 (x y : ℝ) :
    (realDiag2 x y).mulVec ket0 = (x : ℂ) • ket0 := by
  ext i
  fin_cases i <;> simp [realDiag2, diag2, ket0, Matrix.mulVec, dotProduct]

private lemma mul_realDiag2_mulVec_ket0 (M : Square 2) (x y : ℝ) :
    (M * realDiag2 x y) *ᵥ ket0 = (x : ℂ) • (M *ᵥ ket0) := by
  rw [← Matrix.mulVec_mulVec, realDiag2_mulVec_ket0, Matrix.mulVec_smul]

private lemma realDiag2_mulVec_ket1 (x y : ℝ) :
    (realDiag2 x y).mulVec ket1 = (y : ℂ) • ket1 := by
  ext i
  fin_cases i <;> simp [realDiag2, diag2, ket1, Matrix.mulVec, dotProduct]

private lemma mul_realDiag2_mulVec_ket1 (M : Square 2) (x y : ℝ) :
    (M * realDiag2 x y) *ᵥ ket1 = (y : ℂ) • (M *ᵥ ket1) := by
  rw [← Matrix.mulVec_mulVec, realDiag2_mulVec_ket1, Matrix.mulVec_smul]

private lemma realDiag2_conjTranspose (x y : ℝ) :
    (realDiag2 x y)† = realDiag2 x y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realDiag2, diag2]


private lemma mul_neg_realDiag2_mulVec_ket0 (M : Square 2) (x y : ℝ) :
    (M * (- realDiag2 x y)) *ᵥ ket0 = - (x : ℂ) • (M *ᵥ ket0) := by
  calc
    (M * (- realDiag2 x y)) *ᵥ ket0 = M *ᵥ ((- realDiag2 x y) *ᵥ ket0) := by
      rw [Matrix.mulVec_mulVec]
    _ = M *ᵥ ((-(x : ℂ)) • ket0) := by
      rw [Matrix.neg_mulVec, realDiag2_mulVec_ket0]
      simp
    _ = (-(x : ℂ)) • (M *ᵥ ket0) := by
      rw [Matrix.mulVec_smul]
    _ = - (x : ℂ) • (M *ᵥ ket0) := by
      rfl

private lemma mul_neg_realDiag2_mulVec_ket1 (M : Square 2) (x y : ℝ) :
    (M * (- realDiag2 x y)) *ᵥ ket1 = - (y : ℂ) • (M *ᵥ ket1) := by
  calc
    (M * (- realDiag2 x y)) *ᵥ ket1 = M *ᵥ ((- realDiag2 x y) *ᵥ ket1) := by
      rw [Matrix.mulVec_mulVec]
    _ = M *ᵥ ((-(y : ℂ)) • ket1) := by
      rw [Matrix.neg_mulVec, realDiag2_mulVec_ket1]
      simp
    _ = (-(y : ℂ)) • (M *ᵥ ket1) := by
      rw [Matrix.mulVec_smul]
    _ = - (y : ℂ) • (M *ᵥ ket1) := by
      rfl

private lemma scalar_conj_cancel_smul (a b : ℂ) (ha : a ≠ 0) (v : Vec 2) :
    ((a⁻¹ * b * a) : ℂ) • v = b • v := by
  have hs : a⁻¹ * b * a = b := by
    calc
      a⁻¹ * b * a = (a⁻¹ * a) * b := by ring
      _ = b := by simp [ha]
  simpa [hs]

private lemma gram_diag_eq_norm_sq (M : Square 2) (i : Fin 2) :
    (M† * M) i i = ((‖WithLp.toLp 2 (M.mulVec (Pi.single i 1) : Vec 2)‖ ^ 2 : ℝ) : ℂ) := by
  rw [gram_entry_eq_dot]
  fin_cases i
  · have hnorm : ‖WithLp.toLp 2 (M.mulVec (Pi.single 0 1) : Vec 2)‖ ^ 2 = ‖M 0 0‖ ^ 2 + ‖M 1 0‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    calc
      star (M *ᵥ Pi.single 0 1) ⬝ᵥ M *ᵥ Pi.single 0 1
          = (((Complex.normSq (M 0 0) + Complex.normSq (M 1 0) : ℝ)) : ℂ) := by
              simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.normSq_eq_conj_mul_self]
      _ = (((‖M 0 0‖ ^ 2 + ‖M 1 0‖ ^ 2 : ℝ)) : ℂ) := by
            rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      _ = ((‖WithLp.toLp 2 (M.mulVec (Pi.single 0 1) : Vec 2)‖ ^ 2 : ℝ) : ℂ) := by rw [hnorm]
  · have hnorm : ‖WithLp.toLp 2 (M.mulVec (Pi.single 1 1) : Vec 2)‖ ^ 2 = ‖M 0 1‖ ^ 2 + ‖M 1 1‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    calc
      star (M *ᵥ Pi.single 1 1) ⬝ᵥ M *ᵥ Pi.single 1 1
          = (((Complex.normSq (M 0 1) + Complex.normSq (M 1 1) : ℝ)) : ℂ) := by
              simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.normSq_eq_conj_mul_self]
      _ = (((‖M 0 1‖ ^ 2 + ‖M 1 1‖ ^ 2 : ℝ)) : ℂ) := by
            rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      _ = ((‖WithLp.toLp 2 (M.mulVec (Pi.single 1 1) : Vec 2)‖ ^ 2 : ℝ) : ℂ) := by rw [hnorm]

private lemma row_gram_diag_eq_norm_sq (M : Square 2) (i : Fin 2) :
    (M * M†) i i = ((‖WithLp.toLp 2 (M†.mulVec (Pi.single i 1) : Vec 2)‖ ^ 2 : ℝ) : ℂ) := by
  rw [row_cross_entry_eq_dot]
  fin_cases i
  · have hnorm : ‖WithLp.toLp 2 (M†.mulVec (Pi.single 0 1) : Vec 2)‖ ^ 2 = ‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    calc
      star (M† *ᵥ Pi.single 0 1) ⬝ᵥ M† *ᵥ Pi.single 0 1
          = (((Complex.normSq (M 0 0) + Complex.normSq (M 0 1) : ℝ)) : ℂ) := by
              simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_conj]
      _ = (((‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 : ℝ)) : ℂ) := by
            rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      _ = ((‖WithLp.toLp 2 (M†.mulVec (Pi.single 0 1) : Vec 2)‖ ^ 2 : ℝ) : ℂ) := by rw [hnorm]
  · have hnorm : ‖WithLp.toLp 2 (M†.mulVec (Pi.single 1 1) : Vec 2)‖ ^ 2 = ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    calc
      star (M† *ᵥ Pi.single 1 1) ⬝ᵥ M† *ᵥ Pi.single 1 1
          = (((Complex.normSq (M 1 0) + Complex.normSq (M 1 1) : ℝ)) : ℂ) := by
              simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_conj]
      _ = (((‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2 : ℝ)) : ℂ) := by
            rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      _ = ((‖WithLp.toLp 2 (M†.mulVec (Pi.single 1 1) : Vec 2)‖ ^ 2 : ℝ) : ℂ) := by rw [hnorm]

private lemma qubitPerp_orthogonal_left (ψ : Vec 2) :
    star (qubitPerp ψ) ⬝ᵥ ψ = 0 := by
  simpa [dotProduct, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc, mul_comm] using
    congrArg star (qubitPerp_orthogonal ψ)

private lemma neg_realDiag2_conjTranspose (x y : ℝ) :
    (- realDiag2 x y)† = - realDiag2 x y := by
  rw [Matrix.conjTranspose_neg, realDiag2_conjTranspose]

private lemma normalize_with_toLp_norm (v : Vec 2) (hv : v ≠ 0) :
    ∃ ψ : Vec 2, IsQubit ψ ∧ v = ((‖WithLp.toLp 2 v‖ : ℂ)) • ψ := by
  let r2 : ℝ := ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2
  have hr2_ne : r2 ≠ 0 := sumSq_ne_zero_of_ne_zero v hv
  have hr2_nonneg : 0 ≤ r2 := by
    dsimp [r2]
    positivity
  have hr2_pos : 0 < r2 := lt_of_le_of_ne hr2_nonneg (Ne.symm hr2_ne)
  let r : ℝ := Real.sqrt r2
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hr_ne : r ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 hr2_pos
  have hnorm_sq : ‖WithLp.toLp 2 v‖ ^ 2 = r2 := by
    simp [r2, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  have hr_sq : r ^ 2 = r2 := by
    dsimp [r]
    nlinarith [Real.sq_sqrt hr2_nonneg]
  have hnorm : ‖WithLp.toLp 2 v‖ = r := by
    have hsq : ‖WithLp.toLp 2 v‖ ^ 2 = r ^ 2 := by rw [hr_sq]; exact hnorm_sq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · exfalso
      have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_ne)
      have : (0 : ℝ) ≤ -r := by simpa [h] using norm_nonneg (WithLp.toLp 2 v)
      linarith
  refine ⟨((r : ℂ)⁻¹) • v, ?_, ?_⟩
  · simp [IsQubit, Fin.sum_univ_two]
    field_simp [hr_ne]
    have habs : |r| = r := abs_of_nonneg hr_nonneg
    simp [r2, habs] at *
    nlinarith [hr_sq]
  · ext i
    simp [hnorm, hr_ne]

private lemma mulVec_ket0_eq_col0 (M : Square 2) :
    M *ᵥ ket0 = M.col 0 := by
  ext i
  fin_cases i <;>
    simp [ket0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma mulVec_ket1_eq_col1 (M : Square 2) :
    M *ᵥ ket1 = M.col 1 := by
  ext i
  fin_cases i <;>
    simp [ket1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma exists_unitary_mul_realDiag2_of_orthogonal_cols
    (u₀ u₁ : Vec 2) (c₀ c₁ : ℝ)
  (_hc₀ : 0 ≤ c₀) (_hc₁ : 0 ≤ c₁)
    (hn₀ : ‖WithLp.toLp 2 u₀‖ = c₀)
    (hn₁ : ‖WithLp.toLp 2 u₁‖ = c₁)
    (horth : star u₀ ⬝ᵥ u₁ = 0) :
    ∃ P : Square 2, P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      colMatrix u₀ u₁ = P * realDiag2 c₀ c₁ := by
  by_cases hc₀_zero : c₀ = 0
  · have hu₀_zero : u₀ = 0 := by
      have hto : WithLp.toLp 2 u₀ = 0 := by
        apply norm_eq_zero.mp
        simpa [hc₀_zero] using hn₀
      simpa using congrArg (WithLp.ofLp (p := 2)) hto
    by_cases hc₁_zero : c₁ = 0
    · have hu₁_zero : u₁ = 0 := by
        have hto : WithLp.toLp 2 u₁ = 0 := by
          apply norm_eq_zero.mp
          simpa [hc₁_zero] using hn₁
        simpa using congrArg (WithLp.ofLp (p := 2)) hto
      refine ⟨1, by simp, ?_⟩
      apply matrix_eq_of_mulVec_ket
      · simp [colMatrix_mulVec_ket0, hu₀_zero, hc₀_zero, realDiag2_mulVec_ket0]
      · simp [colMatrix_mulVec_ket1, hu₁_zero, hc₁_zero, realDiag2_mulVec_ket1]
    · have hu₁_ne : u₁ ≠ 0 := by
        intro hu₁_zero
        have : ‖WithLp.toLp 2 u₁‖ = 0 := by simp [hu₁_zero]
        rw [hn₁] at this
        exact hc₁_zero this
      rcases normalize_with_toLp_norm u₁ hu₁_ne with ⟨ψ₁, hψ₁, hu₁⟩
      have hu₁' : u₁ = (c₁ : ℂ) • ψ₁ := by simpa [hn₁] using hu₁
      let P : Square 2 := colMatrix (qubitPerp ψ₁) ψ₁
      have hP : P ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
        dsimp [P]
        exact colMatrix_unitary_of_orthonormal (qubitPerp ψ₁) ψ₁
          (isQubit_qubitPerp hψ₁) hψ₁ (qubitPerp_orthogonal_left ψ₁)
      refine ⟨P, hP, ?_⟩
      apply matrix_eq_of_mulVec_ket
      · rw [colMatrix_mulVec_ket0]
        calc
          u₀ = 0 := hu₀_zero
          _ = P *ᵥ ((c₀ : ℂ) • ket0) := by simp [hc₀_zero]
          _ = (P * realDiag2 c₀ c₁) *ᵥ ket0 := by
                rw [← Matrix.mulVec_mulVec, realDiag2_mulVec_ket0, Matrix.mulVec_smul]
      · rw [colMatrix_mulVec_ket1]
        calc
          u₁ = (c₁ : ℂ) • ψ₁ := hu₁'
          _ = P *ᵥ ((c₁ : ℂ) • ket1) := by
                rw [Matrix.mulVec_smul]
                simp [P, colMatrix_mulVec_ket1]
          _ = (P * realDiag2 c₀ c₁) *ᵥ ket1 := by
                rw [← Matrix.mulVec_mulVec, realDiag2_mulVec_ket1, Matrix.mulVec_smul]
  · by_cases hc₁_zero : c₁ = 0
    · have hu₀_ne : u₀ ≠ 0 := by
        intro hu₀_zero
        have : ‖WithLp.toLp 2 u₀‖ = 0 := by simp [hu₀_zero]
        rw [hn₀] at this
        exact hc₀_zero this
      have hu₁_zero : u₁ = 0 := by
        have hto : WithLp.toLp 2 u₁ = 0 := by
          apply norm_eq_zero.mp
          simpa [hc₁_zero] using hn₁
        simpa using congrArg (WithLp.ofLp (p := 2)) hto
      rcases normalize_with_toLp_norm u₀ hu₀_ne with ⟨ψ₀, hψ₀, hu₀⟩
      have hu₀' : u₀ = (c₀ : ℂ) • ψ₀ := by simpa [hn₀] using hu₀
      let P : Square 2 := colMatrix ψ₀ (qubitPerp ψ₀)
      have hP : P ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
        dsimp [P]
        exact qubit_basis_unitary ψ₀ hψ₀
      refine ⟨P, hP, ?_⟩
      apply matrix_eq_of_mulVec_ket
      · rw [colMatrix_mulVec_ket0]
        calc
          u₀ = (c₀ : ℂ) • ψ₀ := hu₀'
          _ = P *ᵥ ((c₀ : ℂ) • ket0) := by
                rw [Matrix.mulVec_smul]
                simp [P, colMatrix_mulVec_ket0]
          _ = (P * realDiag2 c₀ c₁) *ᵥ ket0 := by
                rw [← Matrix.mulVec_mulVec, realDiag2_mulVec_ket0, Matrix.mulVec_smul]
      · rw [colMatrix_mulVec_ket1]
        calc
          u₁ = 0 := hu₁_zero
          _ = P *ᵥ ((c₁ : ℂ) • ket1) := by simp [hc₁_zero]
          _ = (P * realDiag2 c₀ c₁) *ᵥ ket1 := by
                rw [← Matrix.mulVec_mulVec, realDiag2_mulVec_ket1, Matrix.mulVec_smul]
    · have hu₀_ne : u₀ ≠ 0 := by
        intro hu₀_zero
        have : ‖WithLp.toLp 2 u₀‖ = 0 := by simp [hu₀_zero]
        rw [hn₀] at this
        exact hc₀_zero this
      have hu₁_ne : u₁ ≠ 0 := by
        intro hu₁_zero
        have : ‖WithLp.toLp 2 u₁‖ = 0 := by simp [hu₁_zero]
        rw [hn₁] at this
        exact hc₁_zero this
      rcases normalize_with_toLp_norm u₀ hu₀_ne with ⟨ψ₀, hψ₀, hu₀⟩
      rcases normalize_with_toLp_norm u₁ hu₁_ne with ⟨ψ₁, hψ₁, hu₁⟩
      have hu₀' : u₀ = (c₀ : ℂ) • ψ₀ := by simpa [hn₀] using hu₀
      have hu₁' : u₁ = (c₁ : ℂ) • ψ₁ := by simpa [hn₁] using hu₁
      have hψorth : star ψ₀ ⬝ᵥ ψ₁ = 0 := by
        have hscaled : star ((c₀ : ℂ) • ψ₀) ⬝ᵥ ((c₁ : ℂ) • ψ₁) = 0 := by
          simpa [hu₀', hu₁'] using horth
        rw [star_smul, smul_dotProduct, dotProduct_smul] at hscaled
        simp only [smul_eq_mul] at hscaled
        have hscaled' : (star (c₀ : ℂ) * (c₁ : ℂ)) * (star ψ₀ ⬝ᵥ ψ₁) = 0 := by
          simpa [mul_assoc] using hscaled
        have hcc : (star (c₀ : ℂ) * (c₁ : ℂ)) ≠ 0 := by
          have hc₀c : star (c₀ : ℂ) ≠ 0 := by
            simpa using (show (c₀ : ℂ) ≠ 0 from by exact_mod_cast hc₀_zero)
          have hc₁c : (c₁ : ℂ) ≠ 0 := by exact_mod_cast hc₁_zero
          exact mul_ne_zero hc₀c hc₁c
        exact (mul_eq_zero.mp hscaled').resolve_left hcc
      let P : Square 2 := colMatrix ψ₀ ψ₁
      have hP : P ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
        dsimp [P]
        exact colMatrix_unitary_of_orthonormal ψ₀ ψ₁ hψ₀ hψ₁ hψorth
      refine ⟨P, hP, ?_⟩
      apply matrix_eq_of_mulVec_ket
      · rw [colMatrix_mulVec_ket0]
        calc
          u₀ = (c₀ : ℂ) • ψ₀ := hu₀'
          _ = P *ᵥ ((c₀ : ℂ) • ket0) := by
            rw [Matrix.mulVec_smul]
            simp [P, colMatrix_mulVec_ket0]
          _ = (P * realDiag2 c₀ c₁) *ᵥ ket0 := by
            rw [← Matrix.mulVec_mulVec, realDiag2_mulVec_ket0, Matrix.mulVec_smul]
      · rw [colMatrix_mulVec_ket1]
        calc
          u₁ = (c₁ : ℂ) • ψ₁ := hu₁'
          _ = P *ᵥ ((c₁ : ℂ) • ket1) := by
            rw [Matrix.mulVec_smul]
            simp [P, colMatrix_mulVec_ket1]
          _ = (P * realDiag2 c₀ c₁) *ᵥ ket1 := by
            rw [← Matrix.mulVec_mulVec, realDiag2_mulVec_ket1, Matrix.mulVec_smul]


/-- `R_y(θ)` is unitary for every real angle `θ`. -/
theorem ry_unitary (θ : ℝ) :
    ry θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j
  · have h : (((Real.cos (θ / 2)) ^ 2 + (Real.sin (θ / 2)) ^ 2 : ℝ) : ℂ) = 1 := by
      exact_mod_cast (Real.cos_sq_add_sin_sq (θ / 2))
    simpa [ry, Matrix.mul_apply, pow_two, ← Complex.ofReal_cos, ← Complex.ofReal_sin] using h
  · simp [ry, Matrix.mul_apply]
    rw [conj_complex_cos_half θ, conj_complex_sin_half θ]
    ring
  · simp [ry, Matrix.mul_apply]
    rw [conj_complex_sin_half θ, conj_complex_cos_half θ]
    ring
  · have h : (((Real.sin (θ / 2)) ^ 2 + (Real.cos (θ / 2)) ^ 2 : ℝ) : ℂ) = 1 := by
      exact_mod_cast (Real.sin_sq_add_cos_sq (θ / 2))
    simpa [ry, Matrix.mul_apply, pow_two, ← Complex.ofReal_cos, ← Complex.ofReal_sin] using h

/-- A single cosine-sine parameter pair with `c, s ≥ 0` and `c^2 + s^2 = 1` can be realized by
some `R_y` angle. -/
theorem csParameters_exist_angle (c s : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ θ : ℝ,
      c = Real.cos (θ / 2) ∧
      s = Real.sin (θ / 2) := by
  have hc_neg_one : -1 ≤ c := by
    linarith
  have hc_le_one : c ≤ 1 := by
    nlinarith [hc, sq_nonneg s, hcs]
  have hs_sq : 1 - c ^ 2 = s ^ 2 := by
    nlinarith [hcs]
  have hs_sqrt : s = Real.sqrt (1 - c ^ 2) := by
    rw [hs_sq, Real.sqrt_sq hs]
  refine ⟨2 * Real.arccos c, ?_, ?_⟩
  · rw [show (2 * Real.arccos c) / 2 = Real.arccos c by ring]
    rw [Real.cos_arccos hc_neg_one hc_le_one]
  · rw [show (2 * Real.arccos c) / 2 = Real.arccos c by ring]
    rw [Real.sin_arccos]
    exact hs_sqrt

set_option maxHeartbeats 800000 in
/-- Matrix-level `2 + 2` square-block cosine-sine decomposition for a `4 × 4` unitary.
This is the specialized Paige-Wei theorem we actually need to formalize. The outer factors are
already written in the paper's block-diagonal gate language; the middle factor is kept in pure
cosine-sine form so the linear-algebra proof and the trigonometric translation stay separate. -/
theorem squareBlockCSD_exists (V : Square 4)
    (hV : V ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ (P₀ P₁ Q₀ Q₁ : Square 2) (c₀ c₁ s₀ s₁ : ℝ),
      P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      0 ≤ c₀ ∧
      0 ≤ c₁ ∧
      0 ≤ s₀ ∧
      0 ≤ s₁ ∧
      c₀ ^ 2 + s₀ ^ 2 = 1 ∧
      c₁ ^ 2 + s₁ ^ 2 = 1 ∧
      V = blockDiag2 P₀ P₁ * csBlockCore c₀ c₁ s₀ s₁ * blockDiag2 Q₀ Q₁ := by
  classical
  let Ub : BlockMatrix 2 := blockify (n := 2) V
  let A : Square 2 := Ub.toBlocks₁₁
  let B : Square 2 := Ub.toBlocks₁₂
  let C : Square 2 := Ub.toBlocks₂₁
  let D : Square 2 := Ub.toBlocks₂₂
  have hUb : Ub ∈ Matrix.unitaryGroup (Fin 2 ⊕ Fin 2) ℂ := by
    exact (blockify_mem_unitaryGroup_iff (n := 2) V).2 hV
  have hUbBlocks : Matrix.fromBlocks A B C D = Ub := by
    simpa [Ub, A, B, C, D] using (Matrix.fromBlocks_toBlocks Ub)
  have hUbLeft : Ub† * Ub = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hUb)
  have hUbRight : Ub * Ub† = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hUb)
  have hBlocksLeft :
      Matrix.fromBlocks
          (A† * A + C† * C)
          (A† * B + C† * D)
          (B† * A + D† * C)
          (B† * B + D† * D) =
        Matrix.fromBlocks (1 : Square 2) 0 0 (1 : Square 2) := by
    calc
      Matrix.fromBlocks
          (A† * A + C† * C)
          (A† * B + C† * D)
          (B† * A + D† * C)
          (B† * B + D† * D)
          = (Matrix.fromBlocks A B C D)† * Matrix.fromBlocks A B C D := by
              rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
      _ = Ub† * Ub := by rw [hUbBlocks]
      _ = 1 := hUbLeft
      _ = Matrix.fromBlocks (1 : Square 2) 0 0 (1 : Square 2) := by
        exact BlockHelpers.block_one_eq 2
  have hBlocksRight :
      Matrix.fromBlocks
          (A * A† + B * B†)
          (A * C† + B * D†)
          (C * A† + D * B†)
          (C * C† + D * D†) =
        Matrix.fromBlocks (1 : Square 2) 0 0 (1 : Square 2) := by
    calc
      Matrix.fromBlocks
          (A * A† + B * B†)
          (A * C† + B * D†)
          (C * A† + D * B†)
          (C * C† + D * D†)
          = Matrix.fromBlocks A B C D * (Matrix.fromBlocks A B C D)† := by
              rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
      _ = Ub * Ub† := by rw [hUbBlocks]
      _ = 1 := hUbRight
      _ = Matrix.fromBlocks (1 : Square 2) 0 0 (1 : Square 2) := by
        exact BlockHelpers.block_one_eq 2
  rcases Matrix.fromBlocks_inj.mp hBlocksLeft with ⟨hAA_CC, hAB_CD, hBA_DC, hBB_DD⟩
  rcases Matrix.fromBlocks_inj.mp hBlocksRight with ⟨hAA_BB, hAC_BD, hCA_DB, hCC_DD⟩
  let H : Square 2 := A† * A
  have hHherm : H.IsHermitian := by
    dsimp [H]
    exact isHermitian_conjTranspose_mul_self A
  let U₀ : unitary (Square 2) := hHherm.eigenvectorUnitary
  have hU₀ : (U₀ : Square 2) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    dsimp [U₀]
    exact ⟨Unitary.coe_star_mul_self _, Unitary.coe_mul_star_self _⟩
  let Q₀u : unitary (Square 2) := star U₀
  let Q₀ : Square 2 := Q₀u
  have hQ₀ : Q₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    dsimp [Q₀, Q₀u]
    simpa [Matrix.star_eq_conjTranspose] using conjTranspose_mem_unitaryGroup hU₀
  have hQ₀left : Q₀† * Q₀ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hQ₀)
  have hQ₀right : Q₀ * Q₀† = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hQ₀)
  let Δ : Square 2 := diagonal (Complex.ofReal ∘ hHherm.eigenvalues)
  have hHdiag : Q₀ * H * Q₀† = Δ := by
    dsimp [Q₀, Q₀u, U₀, H, Δ]
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hHherm.conjStarAlgAut_star_eigenvectorUnitary
  let A₀ : Square 2 := A * Q₀†
  let C₀ : Square 2 := C * Q₀†
  have hA₀Gram : A₀† * A₀ = Δ := by
    calc
      A₀† * A₀ = Q₀ * H * Q₀† := by
        dsimp [A₀, H]
        simp [mul_assoc]
      _ = Δ := hHdiag
  have hCC : C† * C = 1 - H := by
    rw [eq_sub_iff_add_eq]
    simpa [H, add_assoc, add_comm, add_left_comm] using hAA_CC
  have hC₀Gram : C₀† * C₀ = 1 - Δ := by
    calc
      C₀† * C₀ = Q₀ * (C† * C) * Q₀† := by
        dsimp [C₀]
        simp [mul_assoc]
      _ = Q₀ * (1 - H) * Q₀† := by rw [hCC]
      _ = Q₀ * Q₀† - Q₀ * H * Q₀† := by
            simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc]
      _ = 1 - Δ := by simp [hQ₀right, hHdiag]
  let acol : Fin 2 → Vec 2 := fun i => A₀.mulVec (Pi.single i 1)
  let scol : Fin 2 → Vec 2 := fun i => C₀.mulVec (Pi.single i 1)
  let c₀ : ℝ := ‖WithLp.toLp 2 (acol 0)‖
  let c₁ : ℝ := ‖WithLp.toLp 2 (acol 1)‖
  let s₀ : ℝ := ‖WithLp.toLp 2 (scol 0)‖
  let s₁ : ℝ := ‖WithLp.toLp 2 (scol 1)‖
  have hacol01 : star (acol 0) ⬝ᵥ acol 1 = 0 := by
    have h := congrFun (congrFun hA₀Gram 0) 1
    simpa [Δ, acol, gram_entry_eq_dot] using h
  have hscol01 : star (scol 0) ⬝ᵥ scol 1 = 0 := by
    have h := congrFun (congrFun hC₀Gram 0) 1
    simpa [Δ, scol, gram_entry_eq_dot] using h
  have hA₀col : colMatrix (acol 0) (acol 1) = A₀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [colMatrix, acol, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hC₀col : colMatrix (scol 0) (scol 1) = C₀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [colMatrix, scol, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hc₀_nonneg : 0 ≤ c₀ := by exact norm_nonneg _
  have hc₁_nonneg : 0 ≤ c₁ := by exact norm_nonneg _
  have hs₀_nonneg : 0 ≤ s₀ := by exact norm_nonneg _
  have hs₁_nonneg : 0 ≤ s₁ := by exact norm_nonneg _
  rcases exists_unitary_mul_realDiag2_of_orthogonal_cols (acol 0) (acol 1) c₀ c₁
      hc₀_nonneg hc₁_nonneg rfl rfl hacol01 with ⟨P₀, hP₀, hP₀eq⟩
  rcases exists_unitary_mul_realDiag2_of_orthogonal_cols (scol 0) (scol 1) s₀ s₁
      hs₀_nonneg hs₁_nonneg rfl rfl hscol01 with ⟨P₁, hP₁, hP₁eq⟩
  have hA₀eq : A₀ = P₀ * realDiag2 c₀ c₁ := by
    calc
      A₀ = colMatrix (acol 0) (acol 1) := hA₀col.symm
      _ = P₀ * realDiag2 c₀ c₁ := hP₀eq
  have hC₀eq : C₀ = P₁ * realDiag2 s₀ s₁ := by
    calc
      C₀ = colMatrix (scol 0) (scol 1) := hC₀col.symm
      _ = P₁ * realDiag2 s₀ s₁ := hP₁eq
  have hP₀leftU : P₀† * P₀ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hP₀)
  have hP₁leftU : P₁† * P₁ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hP₁)
  have hP₀cancel (X : Square 2) : P₀† * (P₀ * X) = X := by
    calc
      P₀† * (P₀ * X) = (P₀† * P₀) * X := by simp [mul_assoc]
      _ = X := by simp [hP₀leftU]
  have hP₁cancel (X : Square 2) : P₁† * (P₁ * X) = X := by
    calc
      P₁† * (P₁ * X) = (P₁† * P₁) * X := by simp [mul_assoc]
      _ = X := by simp [hP₁leftU]
  have hP₀sandwich (X : Square 2) : P₀† * (P₀ * X * P₀†) * P₀ = X := by
    calc
      P₀† * (P₀ * X * P₀†) * P₀ = (((P₀† * P₀) * X) * P₀†) * P₀ := by simp [mul_assoc]
      _ = (X * P₀†) * P₀ := by simp [hP₀leftU]
      _ = X * (P₀† * P₀) := by simp [mul_assoc]
      _ = X := by simp [hP₀leftU]
  have hP₁sandwich (X : Square 2) : P₁† * (P₁ * X * P₁†) * P₁ = X := by
    calc
      P₁† * (P₁ * X * P₁†) * P₁ = (((P₁† * P₁) * X) * P₁†) * P₁ := by simp [mul_assoc]
      _ = (X * P₁†) * P₁ := by simp [hP₁leftU]
      _ = X * (P₁† * P₁) := by simp [mul_assoc]
      _ = X := by simp [hP₁leftU]
  have hGramSum : A₀† * A₀ + C₀† * C₀ = 1 := by
    rw [hA₀Gram, hC₀Gram]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Δ, sub_eq_add_neg]
  have hcs₀_complex : (((c₀ ^ 2 + s₀ ^ 2 : ℝ)) : ℂ) = 1 := by
    have h := congrFun (congrFun hGramSum 0) 0
    rw [Matrix.add_apply] at h
    simpa [c₀, s₀, acol, scol, gram_diag_eq_norm_sq] using h
  have hcs₁_complex : (((c₁ ^ 2 + s₁ ^ 2 : ℝ)) : ℂ) = 1 := by
    have h := congrFun (congrFun hGramSum 1) 1
    rw [Matrix.add_apply] at h
    simpa [c₁, s₁, acol, scol, gram_diag_eq_norm_sq] using h
  have hcs₀ : c₀ ^ 2 + s₀ ^ 2 = 1 := by exact_mod_cast hcs₀_complex
  have hcs₁ : c₁ ^ 2 + s₁ ^ 2 = 1 := by exact_mod_cast hcs₁_complex
  let B₁ : Square 2 := P₀† * B
  let D₁ : Square 2 := P₁† * D
  have hAB₀ : A₀† * B + C₀† * D = 0 := by
    calc
      A₀† * B + C₀† * D = Q₀ * (A† * B) + Q₀ * (C† * D) := by
        dsimp [A₀, C₀]
        simp [mul_assoc]
      _ = Q₀ * (A† * B + C† * D) := by rw [Matrix.mul_add]
      _ = 0 := by rw [hAB_CD]; simp
  have hAC₀ : A₀ * C₀† + B * D† = 0 := by
    calc
      A₀ * C₀† + B * D† = A * (Q₀† * Q₀) * C† + B * D† := by
        dsimp [A₀, C₀]
        simp [mul_assoc]
      _ = A * C† + B * D† := by simp [hQ₀left, mul_assoc]
      _ = 0 := hAC_BD
  have hCA₀ : C₀ * A₀† + D * B† = 0 := by
    calc
      C₀ * A₀† + D * B† = C * (Q₀† * Q₀) * A† + D * B† := by
        dsimp [A₀, C₀]
        simp [mul_assoc]
      _ = C * A† + D * B† := by simp [hQ₀left, mul_assoc]
      _ = 0 := hCA_DB
  have hAA₀_BB : A₀ * A₀† + B * B† = 1 := by
    calc
      A₀ * A₀† + B * B† = A * (Q₀† * Q₀) * A† + B * B† := by
        dsimp [A₀]
        simp [mul_assoc]
      _ = A * A† + B * B† := by simp [hQ₀left, mul_assoc]
      _ = 1 := hAA_BB
  have hCC₀_DD : C₀ * C₀† + D * D† = 1 := by
    calc
      C₀ * C₀† + D * D† = C * (Q₀† * Q₀) * C† + D * D† := by
        dsimp [C₀]
        simp [mul_assoc]
      _ = C * C† + D * D† := by simp [hQ₀left, mul_assoc]
      _ = 1 := hCC_DD
  have hLeftRel : realDiag2 c₀ c₁ * B₁ + realDiag2 s₀ s₁ * D₁ = 0 := by
    rw [hA₀eq, hC₀eq] at hAB₀
    simpa [B₁, D₁, mul_assoc, realDiag2_conjTranspose] using hAB₀
  have hRightRel : realDiag2 c₀ c₁ * realDiag2 s₀ s₁ + B₁ * D₁† = 0 := by
    have h := congrArg (fun M => P₀† * M * P₁) hAC₀
    have htmp : P₀† * (A₀ * C₀† + B * D†) * P₁ = realDiag2 c₀ c₁ * realDiag2 s₀ s₁ + B₁ * D₁† := by
      rw [Matrix.mul_add, add_mul, hA₀eq, hC₀eq]
      dsimp [B₁, D₁]
      simp [hP₀cancel, hP₁leftU, mul_assoc, realDiag2_conjTranspose]
    calc
      realDiag2 c₀ c₁ * realDiag2 s₀ s₁ + B₁ * D₁†
          = P₀† * (A₀ * C₀† + B * D†) * P₁ := htmp.symm
      _ = 0 := by simpa using h
  have hRightRelT : realDiag2 s₀ s₁ * realDiag2 c₀ c₁ + D₁ * B₁† = 0 := by
    have h := congrArg (fun M => P₁† * M * P₀) hCA₀
    have htmp : P₁† * (C₀ * A₀† + D * B†) * P₀ = realDiag2 s₀ s₁ * realDiag2 c₀ c₁ + D₁ * B₁† := by
      rw [Matrix.mul_add, add_mul, hA₀eq, hC₀eq]
      dsimp [B₁, D₁]
      simp [hP₁cancel, hP₀leftU, mul_assoc, realDiag2_conjTranspose]
    calc
      realDiag2 s₀ s₁ * realDiag2 c₀ c₁ + D₁ * B₁†
          = P₁† * (C₀ * A₀† + D * B†) * P₀ := htmp.symm
      _ = 0 := by simpa using h
  have hBGram : B₁ * B₁† = 1 - realDiag2 c₀ c₁ * realDiag2 c₀ c₁ := by
    have h := congrArg (fun M => P₀† * M * P₀) hAA₀_BB
    have hmain : realDiag2 c₀ c₁ * realDiag2 c₀ c₁ + B₁ * B₁† = 1 := by
      have htmp : P₀† * (A₀ * A₀† + B * B†) * P₀ = realDiag2 c₀ c₁ * realDiag2 c₀ c₁ + B₁ * B₁† := by
        rw [Matrix.mul_add, add_mul, hA₀eq, Matrix.conjTranspose_mul, realDiag2_conjTranspose]
        dsimp [B₁]
        have hs : P₀† * (P₀ * realDiag2 c₀ c₁ * (realDiag2 c₀ c₁ * P₀†)) * P₀ =
            realDiag2 c₀ c₁ * realDiag2 c₀ c₁ := by
          simpa [mul_assoc] using hP₀sandwich (realDiag2 c₀ c₁ * realDiag2 c₀ c₁)
        rw [hs]
        simp [mul_assoc]
      calc
        realDiag2 c₀ c₁ * realDiag2 c₀ c₁ + B₁ * B₁† = P₀† * (A₀ * A₀† + B * B†) * P₀ := htmp.symm
        _ = P₀† * P₀ := by simpa using h
        _ = 1 := hP₀leftU
    rw [eq_sub_iff_add_eq]
    simpa [add_comm, add_left_comm, add_assoc] using hmain
  have hDGram : D₁ * D₁† = 1 - realDiag2 s₀ s₁ * realDiag2 s₀ s₁ := by
    have h := congrArg (fun M => P₁† * M * P₁) hCC₀_DD
    have hmain : realDiag2 s₀ s₁ * realDiag2 s₀ s₁ + D₁ * D₁† = 1 := by
      have htmp : P₁† * (C₀ * C₀† + D * D†) * P₁ = realDiag2 s₀ s₁ * realDiag2 s₀ s₁ + D₁ * D₁† := by
        rw [Matrix.mul_add, add_mul, hC₀eq, Matrix.conjTranspose_mul, realDiag2_conjTranspose]
        dsimp [D₁]
        have hs : P₁† * (P₁ * realDiag2 s₀ s₁ * (realDiag2 s₀ s₁ * P₁†)) * P₁ =
            realDiag2 s₀ s₁ * realDiag2 s₀ s₁ := by
          simpa [mul_assoc] using hP₁sandwich (realDiag2 s₀ s₁ * realDiag2 s₀ s₁)
        rw [hs]
        simp [mul_assoc]
      calc
        realDiag2 s₀ s₁ * realDiag2 s₀ s₁ + D₁ * D₁† = P₁† * (C₀ * C₀† + D * D†) * P₁ := htmp.symm
        _ = P₁† * P₁ := by simpa using h
        _ = 1 := hP₁leftU
    rw [eq_sub_iff_add_eq]
    simpa [add_comm, add_left_comm, add_assoc] using hmain
  have hColRel : B₁† * realDiag2 c₀ c₁ + D₁† * realDiag2 s₀ s₁ = 0 := by
    simpa [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, realDiag2_conjTranspose] using
      congrArg Matrix.conjTranspose hLeftRel
  let Bcol : Fin 2 → Vec 2 := fun i => B₁†.mulVec (Pi.single i 1)
  let Dcol : Fin 2 → Vec 2 := fun i => D₁†.mulVec (Pi.single i 1)
  have hBnorm₀_complex : (((‖WithLp.toLp 2 (Bcol 0)‖ ^ 2 : ℝ)) : ℂ) = ((s₀ ^ 2 : ℝ) : ℂ) := by
    have h := congrFun (congrFun hBGram 0) 0
    have hsq : (((1 - c₀ ^ 2 : ℝ)) : ℂ) = ((s₀ ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast (by nlinarith [hcs₀])
    calc
      (((‖WithLp.toLp 2 (Bcol 0)‖ ^ 2 : ℝ)) : ℂ) = (B₁ * B₁†) 0 0 := by
        simp [Bcol, row_gram_diag_eq_norm_sq]
      _ = (((1 - c₀ ^ 2 : ℝ)) : ℂ) := by simpa [realDiag2, diag2, pow_two] using h
      _ = ((s₀ ^ 2 : ℝ) : ℂ) := hsq
  have hBnorm₁_complex : (((‖WithLp.toLp 2 (Bcol 1)‖ ^ 2 : ℝ)) : ℂ) = ((s₁ ^ 2 : ℝ) : ℂ) := by
    have h := congrFun (congrFun hBGram 1) 1
    have hsq : (((1 - c₁ ^ 2 : ℝ)) : ℂ) = ((s₁ ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast (by nlinarith [hcs₁])
    calc
      (((‖WithLp.toLp 2 (Bcol 1)‖ ^ 2 : ℝ)) : ℂ) = (B₁ * B₁†) 1 1 := by
        simp [Bcol, row_gram_diag_eq_norm_sq]
      _ = (((1 - c₁ ^ 2 : ℝ)) : ℂ) := by simpa [realDiag2, diag2, pow_two] using h
      _ = ((s₁ ^ 2 : ℝ) : ℂ) := hsq
  have hDnorm₀_complex : (((‖WithLp.toLp 2 (Dcol 0)‖ ^ 2 : ℝ)) : ℂ) = ((c₀ ^ 2 : ℝ) : ℂ) := by
    have h := congrFun (congrFun hDGram 0) 0
    have hsq : (((1 - s₀ ^ 2 : ℝ)) : ℂ) = ((c₀ ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast (by nlinarith [hcs₀])
    calc
      (((‖WithLp.toLp 2 (Dcol 0)‖ ^ 2 : ℝ)) : ℂ) = (D₁ * D₁†) 0 0 := by
        simp [Dcol, row_gram_diag_eq_norm_sq]
      _ = (((1 - s₀ ^ 2 : ℝ)) : ℂ) := by simpa [realDiag2, diag2, pow_two] using h
      _ = ((c₀ ^ 2 : ℝ) : ℂ) := hsq
  have hDnorm₁_complex : (((‖WithLp.toLp 2 (Dcol 1)‖ ^ 2 : ℝ)) : ℂ) = ((c₁ ^ 2 : ℝ) : ℂ) := by
    have h := congrFun (congrFun hDGram 1) 1
    have hsq : (((1 - s₁ ^ 2 : ℝ)) : ℂ) = ((c₁ ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast (by nlinarith [hcs₁])
    calc
      (((‖WithLp.toLp 2 (Dcol 1)‖ ^ 2 : ℝ)) : ℂ) = (D₁ * D₁†) 1 1 := by
        simp [Dcol, row_gram_diag_eq_norm_sq]
      _ = (((1 - s₁ ^ 2 : ℝ)) : ℂ) := by simpa [realDiag2, diag2, pow_two] using h
      _ = ((c₁ ^ 2 : ℝ) : ℂ) := hsq
  have hBoff01 : star (Bcol 0) ⬝ᵥ Bcol 1 = 0 := by
    have h := congrFun (congrFun hBGram 0) 1
    simpa [Bcol, row_cross_entry_eq_dot, realDiag2, diag2] using h
  have hBoff10 : star (Bcol 1) ⬝ᵥ Bcol 0 = 0 := by
    have h := congrFun (congrFun hBGram 1) 0
    simpa [Bcol, row_cross_entry_eq_dot, realDiag2, diag2] using h
  have hDoff01 : star (Dcol 0) ⬝ᵥ Dcol 1 = 0 := by
    have h := congrFun (congrFun hDGram 0) 1
    simpa [Dcol, row_cross_entry_eq_dot, realDiag2, diag2] using h
  have hDoff10 : star (Dcol 1) ⬝ᵥ Dcol 0 = 0 := by
    have h := congrFun (congrFun hDGram 1) 0
    simpa [Dcol, row_cross_entry_eq_dot, realDiag2, diag2] using h
  have hBDoff01 : star (Bcol 0) ⬝ᵥ Dcol 1 = 0 := by
    have h := congrFun (congrFun hRightRel 0) 1
    simpa [Bcol, Dcol, row_cross_entry_eq_dot, realDiag2, diag2] using h
  have hBDoff10 : star (Bcol 1) ⬝ᵥ Dcol 0 = 0 := by
    have h := congrFun (congrFun hRightRel 1) 0
    simpa [Bcol, Dcol, row_cross_entry_eq_dot, realDiag2, diag2] using h
  have hDBoff01 : star (Dcol 0) ⬝ᵥ Bcol 1 = 0 := by
    have h := congrFun (congrFun hRightRelT 0) 1
    simpa [Bcol, Dcol, row_cross_entry_eq_dot, realDiag2, diag2] using h
  have hDBoff10 : star (Dcol 1) ⬝ᵥ Bcol 0 = 0 := by
    have h := congrFun (congrFun hRightRelT 1) 0
    simpa [Bcol, Dcol, row_cross_entry_eq_dot, realDiag2, diag2] using h
  let qcol : Fin 2 → Vec 2
    | 0 => if c₀ = 0 then - Bcol 0 else Dcol 0
    | 1 => if c₁ = 0 then - Bcol 1 else Dcol 1
  have hq01 : star (qcol 0) ⬝ᵥ qcol 1 = 0 := by
    by_cases hc₀_zero : c₀ = 0
    · by_cases hc₁_zero : c₁ = 0
      · simpa [qcol, c₀, c₁, hc₀_zero, hc₁_zero] using hBoff01
      · simpa [qcol, c₀, c₁, hc₀_zero, hc₁_zero] using neg_eq_zero.mpr hBDoff01
    · by_cases hc₁_zero : c₁ = 0
      · simpa [qcol, c₀, c₁, hc₀_zero, hc₁_zero] using neg_eq_zero.mpr hDBoff01
      · simpa [qcol, c₀, c₁, hc₀_zero, hc₁_zero] using hDoff01
  have hq10 : star (qcol 1) ⬝ᵥ qcol 0 = 0 := by
    by_cases hc₀_zero : c₀ = 0
    · by_cases hc₁_zero : c₁ = 0
      · simpa [qcol, c₀, c₁, hc₀_zero, hc₁_zero] using hBoff10
      · simpa [qcol, c₀, c₁, hc₀_zero, hc₁_zero] using neg_eq_zero.mpr hDBoff10
    · by_cases hc₁_zero : c₁ = 0
      · simpa [qcol, c₀, c₁, hc₀_zero, hc₁_zero] using neg_eq_zero.mpr hBDoff10
      · simpa [qcol, c₀, c₁, hc₀_zero, hc₁_zero] using hDoff10
  let t₀ : ℝ := ‖WithLp.toLp 2 (qcol 0)‖
  let t₁ : ℝ := ‖WithLp.toLp 2 (qcol 1)‖
  have ht₀_nonneg : 0 ≤ t₀ := by exact norm_nonneg _
  have ht₁_nonneg : 0 ≤ t₁ := by exact norm_nonneg _
  rcases exists_unitary_mul_realDiag2_of_orthogonal_cols (qcol 0) (qcol 1) t₀ t₁
      ht₀_nonneg ht₁_nonneg rfl rfl hq01 with ⟨R, hR, hRq⟩
  have hqcol0 : qcol 0 = (t₀ : ℂ) • (R *ᵥ ket0) := by
    have h := congrArg (fun M => M *ᵥ ket0) hRq
    calc
      qcol 0 = (R * realDiag2 t₀ t₁) *ᵥ ket0 := by
        simpa [colMatrix_mulVec_ket0] using h
      _ = R *ᵥ (realDiag2 t₀ t₁ *ᵥ ket0) := by rw [Matrix.mulVec_mulVec]
      _ = R *ᵥ ((t₀ : ℂ) • ket0) := by rw [realDiag2_mulVec_ket0]
      _ = (t₀ : ℂ) • (R *ᵥ ket0) := by
        rw [Matrix.mulVec_smul]
  have hqcol1 : qcol 1 = (t₁ : ℂ) • (R *ᵥ ket1) := by
    have h := congrArg (fun M => M *ᵥ ket1) hRq
    calc
      qcol 1 = (R * realDiag2 t₀ t₁) *ᵥ ket1 := by
        simpa [colMatrix_mulVec_ket1] using h
      _ = R *ᵥ (realDiag2 t₀ t₁ *ᵥ ket1) := by rw [Matrix.mulVec_mulVec]
      _ = R *ᵥ ((t₁ : ℂ) • ket1) := by rw [realDiag2_mulVec_ket1]
      _ = (t₁ : ℂ) • (R *ᵥ ket1) := by
        rw [Matrix.mulVec_smul]
  have hColRel0 : (c₀ : ℂ) • Bcol 0 + (s₀ : ℂ) • Dcol 0 = 0 := by
      calc
      (c₀ : ℂ) • Bcol 0 + (s₀ : ℂ) • Dcol 0
          = (B₁† * realDiag2 c₀ c₁) *ᵥ ket0 + (D₁† * realDiag2 s₀ s₁) *ᵥ ket0 := by
              rw [mul_realDiag2_mulVec_ket0, mul_realDiag2_mulVec_ket0]
              rfl
    _ = (B₁† * realDiag2 c₀ c₁ + D₁† * realDiag2 s₀ s₁) *ᵥ ket0 := by
            rw [Matrix.add_mulVec]
    _ = 0 *ᵥ ket0 := by rw [hColRel]
    _ = 0 := by simp
  have hColRel1 : (c₁ : ℂ) • Bcol 1 + (s₁ : ℂ) • Dcol 1 = 0 := by
    have h := congrArg (fun M => M *ᵥ ket1) hColRel
    calc
      (c₁ : ℂ) • Bcol 1 + (s₁ : ℂ) • Dcol 1
          = (B₁† * realDiag2 c₀ c₁) *ᵥ ket1 + (D₁† * realDiag2 s₀ s₁) *ᵥ ket1 := by
              rw [mul_realDiag2_mulVec_ket1, mul_realDiag2_mulVec_ket1]
              rfl
      _ = 0 := by simpa [Matrix.add_mulVec] using h
  have hDcol0 : Dcol 0 = (c₀ : ℂ) • (R *ᵥ ket0) := by
    by_cases hc₀_zero : c₀ = 0
    · have hDzero : Dcol 0 = 0 := by
        have hto : WithLp.toLp 2 (Dcol 0) = 0 := by
          apply norm_eq_zero.mp
          apply sq_eq_zero_iff.mp
          have hnorm_real : ‖WithLp.toLp 2 (Dcol 0)‖ ^ 2 = c₀ ^ 2 := by
            exact_mod_cast hDnorm₀_complex
          simpa [hc₀_zero] using hnorm_real
        simpa using congrArg (WithLp.ofLp (p := 2)) hto
      simp [hc₀_zero, hDzero]
    · have ht₀_sq : t₀ ^ 2 = c₀ ^ 2 := by
        have hnorm_real : ‖WithLp.toLp 2 (Dcol 0)‖ ^ 2 = c₀ ^ 2 := by exact_mod_cast hDnorm₀_complex
        simpa [t₀, qcol, hc₀_zero] using hnorm_real
      have ht₀_eq : t₀ = c₀ := by
        nlinarith [ht₀_nonneg, hc₀_nonneg, ht₀_sq]
      calc
        Dcol 0 = qcol 0 := by simp [qcol, c₀, hc₀_zero]
        _ = (t₀ : ℂ) • (R *ᵥ ket0) := hqcol0
        _ = (c₀ : ℂ) • (R *ᵥ ket0) := by simp [ht₀_eq]
  have hDcol1 : Dcol 1 = (c₁ : ℂ) • (R *ᵥ ket1) := by
    by_cases hc₁_zero : c₁ = 0
    · have hDzero : Dcol 1 = 0 := by
        have hto : WithLp.toLp 2 (Dcol 1) = 0 := by
          apply norm_eq_zero.mp
          apply sq_eq_zero_iff.mp
          have hnorm_real : ‖WithLp.toLp 2 (Dcol 1)‖ ^ 2 = c₁ ^ 2 := by
            exact_mod_cast hDnorm₁_complex
          simpa [hc₁_zero] using hnorm_real
        simpa using congrArg (WithLp.ofLp (p := 2)) hto
      simp [hc₁_zero, hDzero]
    · have ht₁_sq : t₁ ^ 2 = c₁ ^ 2 := by
        have hnorm_real : ‖WithLp.toLp 2 (Dcol 1)‖ ^ 2 = c₁ ^ 2 := by exact_mod_cast hDnorm₁_complex
        simpa [t₁, qcol, hc₁_zero] using hnorm_real
      have ht₁_eq : t₁ = c₁ := by
        nlinarith [ht₁_nonneg, hc₁_nonneg, ht₁_sq]
      calc
        Dcol 1 = qcol 1 := by simp [qcol, c₁, hc₁_zero]
        _ = (t₁ : ℂ) • (R *ᵥ ket1) := hqcol1
        _ = (c₁ : ℂ) • (R *ᵥ ket1) := by simp [ht₁_eq]
  have hBcol0 : Bcol 0 = - (s₀ : ℂ) • (R *ᵥ ket0) := by
    by_cases hc₀_zero : c₀ = 0
    · have ht₀_sq : t₀ ^ 2 = s₀ ^ 2 := by
        have hnorm_real : ‖WithLp.toLp 2 (Bcol 0)‖ ^ 2 = s₀ ^ 2 := by exact_mod_cast hBnorm₀_complex
        simpa [t₀, qcol, hc₀_zero] using hnorm_real
      have ht₀_eq : t₀ = s₀ := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa [pow_two] using ht₀_sq) with h | h
        · exact h
        · linarith [ht₀_nonneg, hs₀_nonneg]
      calc
        Bcol 0 = - qcol 0 := by simp [qcol, c₀, hc₀_zero]
        _ = - ((t₀ : ℂ) • (R *ᵥ ket0)) := by rw [hqcol0]
        _ = - (s₀ : ℂ) • (R *ᵥ ket0) := by simp [ht₀_eq]
    · have hc₀_ne : (c₀ : ℂ) ≠ 0 := by exact_mod_cast hc₀_zero
      have htmp0 : (c₀ : ℂ) • Bcol 0 = - ((s₀ : ℂ) • Dcol 0) := by
        exact eq_neg_of_add_eq_zero_left hColRel0
      have htmp : (c₀ : ℂ) • Bcol 0 = - (s₀ : ℂ) • Dcol 0 := by
        simpa [neg_smul] using htmp0
      calc
        Bcol 0 = ((c₀ : ℂ)⁻¹) • ((c₀ : ℂ) • Bcol 0) := by
          rw [smul_smul, inv_mul_cancel₀ hc₀_ne, one_smul]
        _ = ((c₀ : ℂ)⁻¹) • (- (s₀ : ℂ) • Dcol 0) := by
          rw [htmp]
        _ = ((c₀ : ℂ)⁻¹) • (- (s₀ : ℂ) • ((c₀ : ℂ) • (R *ᵥ ket0))) := by
          rw [hDcol0]
        _ = (((c₀ : ℂ)⁻¹) * (-(s₀ : ℂ)) * (c₀ : ℂ)) • (R *ᵥ ket0) := by
          rw [smul_smul, smul_smul]
        _ = - (s₀ : ℂ) • (R *ᵥ ket0) := by
          simpa using
            scalar_conj_cancel_smul
              (a := (c₀ : ℂ)) (b := (-(s₀ : ℂ))) hc₀_ne (R *ᵥ ket0)
  have hBcol1 : Bcol 1 = - (s₁ : ℂ) • (R *ᵥ ket1) := by
    by_cases hc₁_zero : c₁ = 0
    · have ht₁_sq : t₁ ^ 2 = s₁ ^ 2 := by
        have hnorm_real : ‖WithLp.toLp 2 (Bcol 1)‖ ^ 2 = s₁ ^ 2 := by exact_mod_cast hBnorm₁_complex
        simpa [t₁, qcol, hc₁_zero] using hnorm_real
      have ht₁_eq : t₁ = s₁ := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa [pow_two] using ht₁_sq) with h | h
        · exact h
        · linarith [ht₁_nonneg, hs₁_nonneg]
      calc
        Bcol 1 = - qcol 1 := by simp [qcol, c₁, hc₁_zero]
        _ = - ((t₁ : ℂ) • (R *ᵥ ket1)) := by rw [hqcol1]
        _ = - (s₁ : ℂ) • (R *ᵥ ket1) := by simp [ht₁_eq]
    · have hc₁_ne : (c₁ : ℂ) ≠ 0 := by exact_mod_cast hc₁_zero
      have htmp0 : (c₁ : ℂ) • Bcol 1 = - ((s₁ : ℂ) • Dcol 1) := by
        exact eq_neg_of_add_eq_zero_left hColRel1
      have htmp : (c₁ : ℂ) • Bcol 1 = - (s₁ : ℂ) • Dcol 1 := by
        simpa [neg_smul] using htmp0
      calc
        Bcol 1 = ((c₁ : ℂ)⁻¹) • ((c₁ : ℂ) • Bcol 1) := by
          rw [smul_smul, inv_mul_cancel₀ hc₁_ne, one_smul]
        _ = ((c₁ : ℂ)⁻¹) • (- (s₁ : ℂ) • Dcol 1) := by
          rw [htmp]
        _ = ((c₁ : ℂ)⁻¹) • (- (s₁ : ℂ) • ((c₁ : ℂ) • (R *ᵥ ket1))) := by
          rw [hDcol1]
        _ = (((c₁ : ℂ)⁻¹) * (-(s₁ : ℂ)) * (c₁ : ℂ)) • (R *ᵥ ket1) := by
          rw [smul_smul, smul_smul]
        _ = - (s₁ : ℂ) • (R *ᵥ ket1) := by
          simpa using
            scalar_conj_cancel_smul
              (a := (c₁ : ℂ)) (b := (-(s₁ : ℂ))) hc₁_ne (R *ᵥ ket1)
  have hReqD : D₁† = R * realDiag2 c₀ c₁ := by
    apply matrix_eq_of_mulVec_ket
    · calc
        D₁† *ᵥ ket0 = D₁†.col 0 := by
          simpa using mulVec_ket0_eq_col0 D₁†
        _ = (c₀ : ℂ) • (R *ᵥ ket0) := by
          simpa [Dcol] using hDcol0
        _ = (R * realDiag2 c₀ c₁) *ᵥ ket0 := by
          rw [mul_realDiag2_mulVec_ket0]
    · calc
        D₁† *ᵥ ket1 = D₁†.col 1 := by
          simpa using mulVec_ket1_eq_col1 D₁†
        _ = (c₁ : ℂ) • (R *ᵥ ket1) := by
          simpa [Dcol] using hDcol1
        _ = (R * realDiag2 c₀ c₁) *ᵥ ket1 := by
          rw [mul_realDiag2_mulVec_ket1]

  have hReqB : B₁† = R * (- realDiag2 s₀ s₁) := by
    apply matrix_eq_of_mulVec_ket
    · calc
        B₁† *ᵥ ket0 = B₁†.col 0 := by
          simpa using mulVec_ket0_eq_col0 B₁†
        _ = - (s₀ : ℂ) • (R *ᵥ ket0) := by
          simpa [Bcol] using hBcol0
        _ = (R * (- realDiag2 s₀ s₁)) *ᵥ ket0 := by
          rw [mul_neg_realDiag2_mulVec_ket0]
    · calc
        B₁† *ᵥ ket1 = B₁†.col 1 := by
          simpa using mulVec_ket1_eq_col1 B₁†
        _ = - (s₁ : ℂ) • (R *ᵥ ket1) := by
          simpa [Bcol] using hBcol1
        _ = (R * (- realDiag2 s₀ s₁)) *ᵥ ket1 := by
          rw [mul_neg_realDiag2_mulVec_ket1]
  let Q₁ : Square 2 := R†
  have hQ₁ : Q₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ := conjTranspose_mem_unitaryGroup hR
  have hB₁eq : B₁ = (- realDiag2 s₀ s₁) * Q₁ := by
    calc
      B₁ = (B₁†)† := by simp
      _ = (R * (- realDiag2 s₀ s₁))† := by rw [hReqB]
      _ = ((- realDiag2 s₀ s₁)†) * R† := by
            rw [Matrix.conjTranspose_mul]
      _ = (- realDiag2 s₀ s₁) * R† := by
            rw [neg_realDiag2_conjTranspose]
      _ = (- realDiag2 s₀ s₁) * Q₁ := by
            rfl

  have hD₁eq : D₁ = realDiag2 c₀ c₁ * Q₁ := by
    calc
      D₁ = (D₁†)† := by simp
      _ = (R * realDiag2 c₀ c₁)† := by rw [hReqD]
      _ = (realDiag2 c₀ c₁)† * R† := by
            rw [Matrix.conjTranspose_mul]
      _ = realDiag2 c₀ c₁ * R† := by
            rw [realDiag2_conjTranspose]
      _ = realDiag2 c₀ c₁ * Q₁ := by
            rfl
  have hAeq : A = P₀ * realDiag2 c₀ c₁ * Q₀ := by
    calc
      A = A₀ * Q₀ := by
            dsimp [A₀]
            simp [mul_assoc, hQ₀left]
      _ = P₀ * realDiag2 c₀ c₁ * Q₀ := by rw [hA₀eq, mul_assoc]
  have hCeq : C = P₁ * realDiag2 s₀ s₁ * Q₀ := by
    calc
      C = C₀ * Q₀ := by
            dsimp [C₀]
            simp [mul_assoc, hQ₀left]
      _ = P₁ * realDiag2 s₀ s₁ * Q₀ := by rw [hC₀eq, mul_assoc]
  have hBeq : B = P₀ * (- realDiag2 s₀ s₁) * Q₁ := by
    calc
      B = 1 * B := by simp
      _ = (P₀ * P₀†) * B := by
        have h : P₀ * P₀† = 1 := by
          simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hP₀)
        rw [h]
      _ = P₀ * B₁ := by
        simp [B₁, mul_assoc]
      _ = P₀ * (- realDiag2 s₀ s₁) * Q₁ := by
        rw [hB₁eq]
        simp [mul_assoc]

  have hDeq : D = P₁ * realDiag2 c₀ c₁ * Q₁ := by
    calc
      D = 1 * D := by simp
      _ = (P₁ * P₁†) * D := by
        have h : P₁ * P₁† = 1 := by
          simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hP₁)
        rw [h]
      _ = P₁ * D₁ := by
        simp [D₁, mul_assoc]
      _ = P₁ * realDiag2 c₀ c₁ * Q₁ := by
        rw [hD₁eq]
        simp [mul_assoc]
  refine ⟨P₀, P₁, Q₀, Q₁, c₀, c₁, s₀, s₁,
    hP₀, hP₁, hQ₀, hQ₁,
    hc₀_nonneg, hc₁_nonneg, hs₀_nonneg, hs₁_nonneg,
    hcs₀, hcs₁, ?_⟩
  apply blockify_injective (n := 2)
  have hBlockCore :
      blockify (n := 2) (csBlockCore c₀ c₁ s₀ s₁) =
        Matrix.fromBlocks
          (realDiag2 c₀ c₁)
          (- realDiag2 s₀ s₁)
          (realDiag2 s₀ s₁)
          (realDiag2 c₀ c₁) := by
    simp [csBlockCore]

  have hVblocks :
      blockify (n := 2) V =
        blockify (n := 2)
          (blockDiag2 P₀ P₁ * csBlockCore c₀ c₁ s₀ s₁ * blockDiag2 Q₀ Q₁) := by
    calc
      blockify (n := 2) V = Ub := by
        rfl
      _ = Matrix.fromBlocks A B C D := by
        rw [← hUbBlocks]
      _ = Matrix.fromBlocks P₀ 0 0 P₁ *
            Matrix.fromBlocks
              (realDiag2 c₀ c₁)
              (- realDiag2 s₀ s₁)
              (realDiag2 s₀ s₁)
              (realDiag2 c₀ c₁) *
            Matrix.fromBlocks Q₀ 0 0 Q₁ := by
              rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
              simp [hAeq, hBeq, hCeq, hDeq, mul_assoc]
      _ = blockify (n := 2) (blockDiag2 P₀ P₁) *
            blockify (n := 2) (csBlockCore c₀ c₁ s₀ s₁) *
            blockify (n := 2) (blockDiag2 Q₀ Q₁) := by
              rw [blockify_blockDiag2, hBlockCore, blockify_blockDiag2]
      _ = blockify (n := 2)
            (blockDiag2 P₀ P₁ * csBlockCore c₀ c₁ s₀ s₁ * blockDiag2 Q₀ Q₁) := by
              rw [blockify_mul, blockify_mul]

  have hfinal :
      V = blockDiag2 P₀ P₁ * csBlockCore c₀ c₁ s₀ s₁ * blockDiag2 Q₀ Q₁ := by
    apply blockify_injective (n := 2)
    simpa using hVblocks

  exact ⟨P₀, P₁, Q₀, Q₁, c₀, c₁, s₀, s₁,
    hP₀, hP₁, hQ₀, hQ₁,
    hc₀_nonneg, hc₁_nonneg, hs₀_nonneg, hs₁_nonneg,
    hcs₀, hcs₁, hfinal⟩
/-- Basis translation from the square-block cosine-sine core to the conditional-`R_y` middle
factor used in the paper packet. -/
theorem csBlockCore_eq_conditionalRy
    {c₀ c₁ s₀ s₁ θ₀ θ₁ : ℝ}
    (hc₀ : c₀ = Real.cos (θ₀ / 2))
    (hc₁ : c₁ = Real.cos (θ₁ / 2))
    (hs₀ : s₀ = Real.sin (θ₀ / 2))
    (hs₁ : s₁ = Real.sin (θ₁ / 2)) :
    csBlockCore c₀ c₁ s₀ s₁ = conditionalRy θ₀ θ₁ := by
  apply blockify_injective (n := 2)
  calc
    blockify (n := 2) (csBlockCore c₀ c₁ s₀ s₁)
      = Matrix.fromBlocks
          (realDiag2 c₀ c₁)
          (- realDiag2 s₀ s₁)
          (realDiag2 s₀ s₁)
          (realDiag2 c₀ c₁) := by
            simp [csBlockCore]
    _ = Matrix.fromBlocks
          (realDiag2 (Real.cos (θ₀ / 2)) (Real.cos (θ₁ / 2)))
          (- realDiag2 (Real.sin (θ₀ / 2)) (Real.sin (θ₁ / 2)))
          (realDiag2 (Real.sin (θ₀ / 2)) (Real.sin (θ₁ / 2)))
          (realDiag2 (Real.cos (θ₀ / 2)) (Real.cos (θ₁ / 2))) := by
            simp [hc₀, hc₁, hs₀, hs₁]
    _ = blockify (n := 2) (conditionalRy θ₀ θ₁) := by
          rw [blockify_conditionalRy]

/-- Paper-facing formulation of Lemma `cosinesine`.

The matrix equation is written as `V = P * R * Q`, matching the specialization-and-translation
packet rather than relying on circuit-diagram reading conventions. -/
theorem cosinesine_exists (V : Square 4)
    (hV : V ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ (P₀ P₁ Q₀ Q₁ : Square 2) (θ₀ θ₁ : ℝ),
      P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      V = blockDiag2 P₀ P₁ * conditionalRy θ₀ θ₁ * blockDiag2 Q₀ Q₁ := by
  rcases squareBlockCSD_exists V hV with
    ⟨P₀, P₁, Q₀, Q₁, c₀, c₁, s₀, s₁,
      hP₀, hP₁, hQ₀, hQ₁,
      hc₀_nonneg, hc₁_nonneg, hs₀_nonneg, hs₁_nonneg,
      hcs₀, hcs₁, hVeq⟩
  rcases csParameters_exist_angle c₀ s₀ hc₀_nonneg hs₀_nonneg hcs₀ with ⟨θ₀, hc₀, hs₀⟩
  rcases csParameters_exist_angle c₁ s₁ hc₁_nonneg hs₁_nonneg hcs₁ with ⟨θ₁, hc₁, hs₁⟩
  refine ⟨P₀, P₁, Q₀, Q₁, θ₀, θ₁, hP₀, hP₁, hQ₀, hQ₁, ?_⟩
  calc
    V = blockDiag2 P₀ P₁ * csBlockCore c₀ c₁ s₀ s₁ * blockDiag2 Q₀ Q₁ := hVeq
    _ = blockDiag2 P₀ P₁ * conditionalRy θ₀ θ₁ * blockDiag2 Q₀ Q₁ := by
          rw [csBlockCore_eq_conditionalRy hc₀ hc₁ hs₀ hs₁]

end CosineSine
end TwoControl

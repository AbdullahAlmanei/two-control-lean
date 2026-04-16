import TwoControl.BlockHelpers
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

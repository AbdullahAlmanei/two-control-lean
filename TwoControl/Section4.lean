import TwoControl.BlockHelpers
import TwoControl.DiagonalizationHelpers
import TwoControl.Section3

namespace TwoControl

/-- **Lemma 4.1** (First building block).
    Suppose `u₀, u₁` are complex numbers with `‖u₀‖ = 1` and `‖u₁‖ = 1`.
    There exist 4×4 unitaries `U, V` and 2×2 unitaries `P₀, P₁, Q₀, Q₁` such that
    `|0⟩⟨0| ⊗ U(P₀ ⊗ Q₀)V + |1⟩⟨1| ⊗ U(P₁ ⊗ Q₁)V = CC(Diag(u₀, u₁))`
    if and only if either `u₀ = u₁` or `u₀ * u₁ = 1`. -/
lemma section4_lemma_4_1 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (U V : Square 4) (P₀ P₁ Q₀ Q₁ : Square 2),
      U ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      proj0 ⊗ₖ (U * (P₀ ⊗ₖ Q₀) * V) + proj1 ⊗ₖ (U * (P₁ ⊗ₖ Q₁) * V)
        = ccu (diag2 u₀ u₁))
        ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by
    constructor
    ·
        rintro ⟨U, V, P₀, P₁, Q₀, Q₁, hU, _hV, hP₀, hP₁, hQ₀, hQ₁, hEq⟩
        have hBlocks :
                Matrix.fromBlocks (U * (P₀ ⊗ₖ Q₀) * V) 0 0 (U * (P₁ ⊗ₖ Q₁) * V) =
                    Matrix.fromBlocks (1 : Square 4) 0 0 (controlledGate (diag2 u₀ u₁)) := by
            calc
                Matrix.fromBlocks (U * (P₀ ⊗ₖ Q₀) * V) 0 0 (U * (P₁ ⊗ₖ Q₁) * V) =
                        blockify (n := 4)
                            (proj0 ⊗ₖ (U * (P₀ ⊗ₖ Q₀) * V) + proj1 ⊗ₖ (U * (P₁ ⊗ₖ Q₁) * V)) := by
                                symm
                                rw [blockify_add, blockify_proj0_kron, blockify_proj1_kron]
                                simp [Matrix.fromBlocks_add]
                _ = blockify (n := 4) (ccu (diag2 u₀ u₁)) := by
                            simpa using congrArg (blockify (n := 4)) hEq
                _ = Matrix.fromBlocks (1 : Square 4) 0 0 (controlledGate (diag2 u₀ u₁)) := by
                            rw [ccu, blockify_add, blockify_proj0_kron, blockify_proj1_kron]
                            simp [Matrix.fromBlocks_add]
        rcases Matrix.fromBlocks_inj.mp hBlocks with ⟨h00, _, _, h11⟩
        have h11diag : U * (P₁ ⊗ₖ Q₁) * V = diag4 1 1 u₀ u₁ := by
            rw [h11, controlledGate_diag2_eq]
        have hUleft : U† * U = 1 := by
            simpa using (Matrix.mem_unitaryGroup_iff'.mp hU)
        have hP₀Q₀ : P₀ ⊗ₖ Q₀ ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
            kron_unitary_two P₀ Q₀ hP₀ hQ₀
        have hP₀Q₀left : (P₀ ⊗ₖ Q₀)† * (P₀ ⊗ₖ Q₀) = 1 := by
            simpa using (Matrix.mem_unitaryGroup_iff'.mp hP₀Q₀)
        have hP₀Q₀V : (P₀ ⊗ₖ Q₀) * V = U† := by
            calc
                (P₀ ⊗ₖ Q₀) * V = 1 * ((P₀ ⊗ₖ Q₀) * V) := by simp
                _ = (U† * U) * ((P₀ ⊗ₖ Q₀) * V) := by rw [← hUleft]
                _ = U† * (U * (P₀ ⊗ₖ Q₀) * V) := by simp [mul_assoc]
                _ = U† * 1 := by rw [h00]
                _ = U† := by simp
        have hVeq : V = (P₀† ⊗ₖ Q₀†) * U† := by
            calc
                V = 1 * V := by simp
                _ = ((P₀ ⊗ₖ Q₀)† * (P₀ ⊗ₖ Q₀)) * V := by rw [← hP₀Q₀left]
                _ = (P₀ ⊗ₖ Q₀)† * ((P₀ ⊗ₖ Q₀) * V) := by simp [mul_assoc]
                _ = (P₀ ⊗ₖ Q₀)† * U† := by rw [hP₀Q₀V]
                _ = (P₀† ⊗ₖ Q₀†) * U† := by rw [conjTranspose_kron_two]
        have hDiagConj :
                diag4 1 1 u₀ u₁ = U * ((P₁ * P₀†) ⊗ₖ (Q₁ * Q₀†)) * U† := by
            calc
                diag4 1 1 u₀ u₁ = U * (P₁ ⊗ₖ Q₁) * V := h11diag.symm
                _ = U * (P₁ ⊗ₖ Q₁) * ((P₀† ⊗ₖ Q₀†) * U†) := by rw [hVeq]
                _ = U * (((P₁ ⊗ₖ Q₁) * (P₀† ⊗ₖ Q₀†)) * U†) := by simp [mul_assoc]
                _ = U * (((P₁ * P₀†) ⊗ₖ (Q₁ * Q₀†)) * U†) := by rw [← kron_mul_two]
                _ = U * ((P₁ * P₀†) ⊗ₖ (Q₁ * Q₀†)) * U† := by simp [mul_assoc]
        have hWitness :
                (P₁ * P₀†) ⊗ₖ (Q₁ * Q₀†) = U† * diag4 1 1 u₀ u₁ * U := by
            calc
                (P₁ * P₀†) ⊗ₖ (Q₁ * Q₀†) = 1 * ((P₁ * P₀†) ⊗ₖ (Q₁ * Q₀†)) * 1 := by simp
                _ = (U† * U) * ((P₁ * P₀†) ⊗ₖ (Q₁ * Q₀†)) * 1 := by rw [← hUleft]
                _ = (U† * U) * ((P₁ * P₀†) ⊗ₖ (Q₁ * Q₀†)) * (U† * U) := by rw [← hUleft]
                _ = U† * (U * ((P₁ * P₀†) ⊗ₖ (Q₁ * Q₀†)) * U†) * U := by simp [mul_assoc]
                _ = U† * diag4 1 1 u₀ u₁ * U := by rw [hDiagConj]
        have hP : P₁ * P₀† ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
            exact Submonoid.mul_mem _ hP₁ (conjTranspose_mem_unitaryGroup hP₀)
        have hQ : Q₁ * Q₀† ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
            exact Submonoid.mul_mem _ hQ₁ (conjTranspose_mem_unitaryGroup hQ₀)
        have hUadj : U† ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
            conjTranspose_mem_unitaryGroup hU
        exact (section3_lemma_3_2 u₀ u₁ hu₀ hu₁).mp <| by
            refine ⟨P₁ * P₀†, Q₁ * Q₀†, U†, hP, hQ, hUadj, ?_⟩
            simpa using hWitness
    ·
        intro h
        rcases (section3_lemma_3_2 u₀ u₁ hu₀ hu₁).2 h with ⟨P, Q, W, hP, hQ, hW, hEq⟩
        have hWleft : W† * W = 1 := by
            simpa using (Matrix.mem_unitaryGroup_iff'.mp hW)
        have hUpper : W† * ((1 : Square 2) ⊗ₖ (1 : Square 2)) * W = (1 : Square 4) := by
            calc
                W† * ((1 : Square 2) ⊗ₖ (1 : Square 2)) * W = W† * (1 : Square 4) * W := by
                    rw [TwoControl.one_kron_one 2 2]
                _ = W† * W := by simp
                _ = 1 := hWleft
        have hLower : W† * (P ⊗ₖ Q) * W = controlledGate (diag2 u₀ u₁) := by
            calc
                W† * (P ⊗ₖ Q) * W = W† * (W * diag4 1 1 u₀ u₁ * W†) * W := by rw [hEq]
                _ = (W† * W) * diag4 1 1 u₀ u₁ * (W† * W) := by simp [mul_assoc]
                _ = diag4 1 1 u₀ u₁ := by simp [hWleft]
                _ = controlledGate (diag2 u₀ u₁) := by
                    symm
                    exact controlledGate_diag2_eq u₀ u₁
        refine ⟨W†, W, 1, P, 1, Q, conjTranspose_mem_unitaryGroup hW, hW,
            Submonoid.one_mem _, hP, Submonoid.one_mem _, hQ, ?_⟩
        calc
            proj0 ⊗ₖ (W† * ((1 : Square 2) ⊗ₖ (1 : Square 2)) * W) +
                proj1 ⊗ₖ (W† * (P ⊗ₖ Q) * W)
                = proj0 ⊗ₖ (1 : Square 4) + proj1 ⊗ₖ controlledGate (diag2 u₀ u₁) := by
                    rw [hUpper, hLower]
            _ = ccu (diag2 u₀ u₁) := by rw [ccu]

private lemma kron_add_right (A : Square m) (B₁ B₂ : Square n) :
        A ⊗ₖ (B₁ + B₂) = A ⊗ₖ B₁ + A ⊗ₖ B₂ := by
    ext i j
    obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (@finProdFinEquiv m n).surjective i
    obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (@finProdFinEquiv m n).surjective j
    simp [TwoControl.kron_apply, mul_add]

@[simp] private lemma mulVec_ket0_apply (Q : Square 2) (i : Fin 2) :
        Q.mulVec ket0 i = Q i 0 := by
    rw [show ket0 = Pi.single 0 1 by
        ext j
        fin_cases j <;> simp [ket0]]
    rw [Matrix.mulVec_single_one]
    rfl

@[simp] private lemma mulVec_ket1_apply (Q : Square 2) (i : Fin 2) :
        Q.mulVec ket1 i = Q i 1 := by
    rw [show ket1 = Pi.single 1 1 by
        ext j
        fin_cases j <;> simp [ket1]]
    rw [Matrix.mulVec_single_one]
    rfl

private lemma unitary_column0_norm (Q : Square 2)
        (hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
        star ((Q.mulVec ket0) 0) * (Q.mulVec ket0) 0 +
            star ((Q.mulVec ket0) 1) * (Q.mulVec ket0) 1 = 1 := by
    have hleft : Q† * Q = 1 := by
        simpa using (Matrix.mem_unitaryGroup_iff'.mp hQ)
    simpa [Matrix.mul_apply, Matrix.mulVec, ket0, Matrix.one_apply] using
        congrFun (congrFun hleft 0) 0

private lemma unitary_column1_norm (Q : Square 2)
        (hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
        star ((Q.mulVec ket1) 0) * (Q.mulVec ket1) 0 +
            star ((Q.mulVec ket1) 1) * (Q.mulVec ket1) 1 = 1 := by
    have hleft : Q† * Q = 1 := by
        simpa using (Matrix.mem_unitaryGroup_iff'.mp hQ)
    simpa [Matrix.mul_apply, Matrix.mulVec, ket1, Matrix.one_apply] using
        congrFun (congrFun hleft 1) 1

private lemma unitary_columns_orthogonal_left (Q : Square 2)
        (hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
        star ((Q.mulVec ket1) 0) * (Q.mulVec ket0) 0 +
            star ((Q.mulVec ket1) 1) * (Q.mulVec ket0) 1 = 0 := by
    have hleft : Q† * Q = 1 := by
        simpa using (Matrix.mem_unitaryGroup_iff'.mp hQ)
    simpa [Matrix.mul_apply, Matrix.mulVec, ket0, ket1, Matrix.one_apply] using
        congrFun (congrFun hleft 1) 0

private lemma unitary_columns_orthogonal_right (Q : Square 2)
        (hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
        star ((Q.mulVec ket0) 0) * (Q.mulVec ket1) 0 +
            star ((Q.mulVec ket0) 1) * (Q.mulVec ket1) 1 = 0 := by
    have hleft : Q† * Q = 1 := by
        simpa using (Matrix.mem_unitaryGroup_iff'.mp hQ)
    simpa [Matrix.mul_apply, Matrix.mulVec, ket0, ket1, Matrix.one_apply] using
        congrFun (congrFun hleft 0) 1

private lemma unitary_column_projector_sum (Q : Square 2)
        (hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
        ketbra (Q.mulVec ket0) (Q.mulVec ket0) + ketbra (Q.mulVec ket1) (Q.mulVec ket1) = (1 : Square 2) := by
    have hright : Q * Q† = 1 := by
        simpa using (Matrix.mem_unitaryGroup_iff.mp hQ)
    calc
        ketbra (Q.mulVec ket0) (Q.mulVec ket0) + ketbra (Q.mulVec ket1) (Q.mulVec ket1) = Q * Q† := by
            ext i j
            fin_cases i <;> fin_cases j <;>
                simp [ketbra, Matrix.vecMulVec, Matrix.mul_apply]
        _ = 1 := hright

private lemma diag4_one : diag4 1 1 1 1 = (1 : Square 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag4]

private lemma proj0_add_proj1 : proj0 + proj1 = (1 : Square 2) := by
    calc
        proj0 + proj1 = 1 • proj0 + 1 • proj1 := by simp
        _ = diag2 1 1 := by
            symm
            simpa using (diag2_decomp 1 1)
        _ = 1 := diag2_one_one

private lemma controlledGate_diag2_one : controlledGate (diag2 1 1) = (1 : Square 4) := by
    rw [controlledGate_diag2_eq, diag4_one]

private lemma ccu_diag2_one : ccu (diag2 1 1) = (1 : Square 8) := by
    calc
        ccu (diag2 1 1) = proj0 ⊗ₖ (1 : Square 4) + proj1 ⊗ₖ (1 : Square 4) := by
            rw [ccu, controlledGate_diag2_one]
        _ = (proj0 + proj1) ⊗ₖ (1 : Square 4) := by
            symm
            exact kron_add_left proj0 proj1 (1 : Square 4)
        _ = (1 : Square 2) ⊗ₖ (1 : Square 4) := by rw [proj0_add_proj1]
        _ = (1 : Square 8) := by simpa using (TwoControl.one_kron_one 2 4)

@[simp] private lemma kronVec_zero_right (x : Vec m) :
        kronVec x (0 : Vec n) = 0 := by
    ext i
    simp [kronVec]

@[simp] private lemma proj0_mulVec_apply (β : Vec 2) (i : Fin 2) :
        (proj0.mulVec β) i = if i = 0 then β 0 else 0 := by
    fin_cases i <;> simp [proj0, ketbra, ket0, Matrix.mulVec, dotProduct]

@[simp] private lemma proj1_mulVec_apply (β : Vec 2) (i : Fin 2) :
        (proj1.mulVec β) i = if i = 1 then β 1 else 0 := by
    fin_cases i <;> simp [proj1, ketbra, ket1, Matrix.mulVec, dotProduct]

@[simp] private lemma diag2_mulVec_apply_zero (u₀ u₁ : ℂ) (β : Vec 2) :
        (diag2 u₀ u₁).mulVec β 0 = u₀ * β 0 := by
    simp [diag2, Matrix.mulVec, dotProduct]

@[simp] private lemma diag2_mulVec_apply_one (u₀ u₁ : ℂ) (β : Vec 2) :
        (diag2 u₀ u₁).mulVec β 1 = u₁ * β 1 := by
    simp [diag2, Matrix.mulVec, dotProduct]

private lemma ketbra_mulVec (v w x : Vec 2) :
        (ketbra v w).mulVec x = (star w ⬝ᵥ x) • v := by
    ext i
    fin_cases i <;>
        simp [ketbra, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
            mul_add, mul_left_comm, mul_comm]

private lemma ketbra_self_mulVec_of_dotProduct_eq_one {β : Vec 2}
        (hβ : star β ⬝ᵥ β = 1) :
        (ketbra β β).mulVec β = β := by
    rw [ketbra_mulVec]
    simp [hβ]

private lemma ketbra_orthogonal_mulVec {β γ : Vec 2}
        (h : star γ ⬝ᵥ β = 0) :
        (ketbra γ γ).mulVec β = 0 := by
    rw [ketbra_mulVec]
    simp [h]

private lemma ketbra_eq_proj1_of_first_zero {β : Vec 2}
        (ha : β 0 = 0) (hb : star (β 1) * β 1 = 1) :
        ketbra β β = proj1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
        simp [ketbra, proj1, Matrix.vecMulVec_apply, ket1, ha]
    simpa [mul_comm] using hb

private lemma ketbra_eq_proj0_of_second_zero {β : Vec 2}
        (hb : β 1 = 0) (ha : star (β 0) * β 0 = 1) :
        ketbra β β = proj0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
        simp [ketbra, proj0, Matrix.vecMulVec_apply, ket0, hb]
    simpa [mul_comm] using ha

private lemma finProd_assoc_222 (a b c : Fin 2) :
    (@finProdFinEquiv 4 2 (@finProdFinEquiv 2 2 (a, b), c) : Fin 8) =
        @finProdFinEquiv 2 4 (a, @finProdFinEquiv 2 2 (b, c)) := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

@[simp] private lemma finProdFinEquiv_00 : (@finProdFinEquiv 2 2 (0, 0) : Fin 4) = 0 := by
    decide

@[simp] private lemma finProdFinEquiv_01 : (@finProdFinEquiv 2 2 (0, 1) : Fin 4) = 1 := by
    decide

@[simp] private lemma finProdFinEquiv_10 : (@finProdFinEquiv 2 2 (1, 0) : Fin 4) = 2 := by
    decide

@[simp] private lemma finProdFinEquiv_11 : (@finProdFinEquiv 2 2 (1, 1) : Fin 4) = 3 := by
    decide

@[simp] private lemma finProdFinEquiv_30 : (@finProdFinEquiv 4 2 (3, 0) : Fin 8) = 6 := by
    decide

@[simp] private lemma finProdFinEquiv_31 : (@finProdFinEquiv 4 2 (3, 1) : Fin 8) = 7 := by
    decide

private lemma finProd_assoc_11 (i : Fin 2) :
        (@finProdFinEquiv 4 2 (3, i) : Fin 8) = @finProdFinEquiv 2 4 (1, @finProdFinEquiv 2 2 (1, i)) := by
    simpa [finProdFinEquiv_11] using (finProd_assoc_222 1 1 i)

private lemma ccu_diag2_last_zero_block (u₀ u₁ : ℂ) (a b : Fin 4) :
        (ccu (diag2 u₀ u₁)) (@finProdFinEquiv 4 2 (a, 0)) (@finProdFinEquiv 4 2 (b, 0)) =
            (diag4 1 1 1 u₀) a b := by
    obtain ⟨⟨a1, a2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective a
    obtain ⟨⟨b1, b2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective b
    rw [finProd_assoc_222 a1 a2 0, finProd_assoc_222 b1 b2 0]
    fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
        try simp [ccu, controlledGate, TwoControl.kron, Matrix.reindex_apply,
            Matrix.kroneckerMap_apply, proj0, proj1, ketbra, ket0, ket1, diag2, diag4]
    all_goals
        first
        | rw [finProdFinEquiv_00]
        | rw [finProdFinEquiv_01]
        | rw [finProdFinEquiv_10]
        | rw [finProdFinEquiv_11]
    all_goals simp

private lemma ccu_diag2_last_one_block (u₀ u₁ : ℂ) (a b : Fin 4) :
        (ccu (diag2 u₀ u₁)) (@finProdFinEquiv 4 2 (a, 1)) (@finProdFinEquiv 4 2 (b, 1)) =
            (diag4 1 1 1 u₁) a b := by
    obtain ⟨⟨a1, a2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective a
    obtain ⟨⟨b1, b2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective b
    rw [finProd_assoc_222 a1 a2 1, finProd_assoc_222 b1 b2 1]
    fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
        try simp [ccu, controlledGate, TwoControl.kron, Matrix.reindex_apply,
            Matrix.kroneckerMap_apply, proj0, proj1, ketbra, ket0, ket1, diag2, diag4]
    all_goals
        first
        | rw [finProdFinEquiv_00]
        | rw [finProdFinEquiv_01]
        | rw [finProdFinEquiv_10]
        | rw [finProdFinEquiv_11]
    all_goals simp

private lemma ccu_diag2_11_block (u₀ u₁ : ℂ) (i j : Fin 2) :
        (ccu (diag2 u₀ u₁)) (@finProdFinEquiv 4 2 (3, i)) (@finProdFinEquiv 4 2 (3, j)) =
            (diag2 u₀ u₁) i j := by
    rw [finProd_assoc_11 i, finProd_assoc_11 j]
    fin_cases i <;> fin_cases j <;>
        try simp [ccu, controlledGate, TwoControl.kron, Matrix.reindex_apply,
            Matrix.kroneckerMap_apply, proj0, proj1, ketbra, ket0, ket1, diag2]

/-- **Lemma 4.2** (Second building block).
    Suppose `u₀, u₁` are complex numbers with `‖u₀‖ = 1` and `‖u₁‖ = 1`.
    Suppose `Q` is a 2×2 unitary and let `β = Q * ket0` and `β⊥ = Q * ket1`.
    There exist 2×2 unitaries `P₀, P₁` such that
    `I ⊗ I ⊗ |β⟩⟨β| + P₀ ⊗ P₁ ⊗ |β⊥⟩⟨β⊥| = CC(Diag(u₀, u₁))`
    if and only if `u₀ = 1` and `u₁ = 1`. -/
lemma section4_lemma_4_2 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (Q : Square 2) (hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    let β := Q.mulVec ket0
    let β_perp := Q.mulVec ket1
    (∃ (P₀ P₁ : Square 2),
      P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      (1 : Square 2) ⊗ₖ (1 : Square 2) ⊗ₖ ketbra β β
        + P₀ ⊗ₖ P₁ ⊗ₖ ketbra β_perp β_perp
        = ccu (diag2 u₀ u₁))
        ↔ u₀ = 1 ∧ u₁ = 1 := by
    dsimp
    constructor
    ·
        rintro ⟨P₀, P₁, hP₀, hP₁, hEq⟩
        let β : Vec 2 := Q.mulVec ket0
        let β_perp : Vec 2 := Q.mulVec ket1
        have hβnorm : star β ⬝ᵥ β = 1 := by
            dsimp [β]
            simpa [dotProduct] using unitary_column0_norm Q hQ
        have hβorth : star β_perp ⬝ᵥ β = 0 := by
            dsimp [β, β_perp]
            simpa [dotProduct] using unitary_columns_orthogonal_left Q hQ
        by_cases ha : β 0 = 0
        · have hbNorm : star (β 1) * β 1 = 1 := by
              dsimp [β] at ha ⊢
              simpa [ha] using unitary_column0_norm Q hQ
          have hβproj : ketbra β β = proj1 :=
              ketbra_eq_proj1_of_first_zero ha hbNorm
          have hβperpProj : ketbra β_perp β_perp = proj0 := by
              have hsum : ketbra β β + ketbra β_perp β_perp = (1 : Square 2) := by
                  dsimp [β, β_perp]
                  simpa using unitary_column_projector_sum Q hQ
              have hsum' : proj1 + ketbra β_perp β_perp = proj1 + proj0 := by
                  calc
                      proj1 + ketbra β_perp β_perp = ketbra β β + ketbra β_perp β_perp := by
                          rw [hβproj]
                      _ = (1 : Square 2) := hsum
                      _ = proj0 + proj1 := by rw [← proj0_add_proj1]
                      _ = proj1 + proj0 := by ac_rfl
              exact add_left_cancel hsum'
          have hEqProj :
                  (1 : Square 4) ⊗ₖ proj1 + (P₀ ⊗ₖ P₁) ⊗ₖ proj0 = ccu (diag2 u₀ u₁) := by
              simpa [β, β_perp, hβproj, hβperpProj, TwoControl.one_kron_one 2 2] using hEq
          have hTensor0 : P₀ ⊗ₖ P₁ = diag4 1 1 1 u₀ := by
              ext a b
              have hij := congrFun (congrFun hEqProj (@finProdFinEquiv 4 2 (a, 0))) (@finProdFinEquiv 4 2 (b, 0))
              have hL0 :
                      (((1 : Square 4) ⊗ₖ proj1) (@finProdFinEquiv 4 2 (a, 0)) (@finProdFinEquiv 4 2 (b, 0))) = 0 := by
                  simpa [proj0, proj1, ketbra, ket0, ket1] using
                      (TwoControl.kron_apply (A := (1 : Square 4)) (B := proj1) a 0 b 0)
              have hL1 :
                      (((P₀ ⊗ₖ P₁) ⊗ₖ proj0) (@finProdFinEquiv 4 2 (a, 0)) (@finProdFinEquiv 4 2 (b, 0))) =
                          (P₀ ⊗ₖ P₁) a b := by
                  simpa [proj0, proj1, ketbra, ket0, ket1] using
                      (TwoControl.kron_apply (A := P₀ ⊗ₖ P₁) (B := proj0) a 0 b 0)
              simpa [Matrix.add_apply, hL0, hL1, ccu_diag2_last_zero_block u₀ u₁ a b] using hij
          have hId1 : (1 : Square 4) = diag4 1 1 1 u₁ := by
              ext a b
              have hij := congrFun (congrFun hEqProj (@finProdFinEquiv 4 2 (a, 1))) (@finProdFinEquiv 4 2 (b, 1))
              have hL0 :
                      (((1 : Square 4) ⊗ₖ proj1) (@finProdFinEquiv 4 2 (a, 1)) (@finProdFinEquiv 4 2 (b, 1))) =
                          (1 : Square 4) a b := by
                  simpa [proj0, proj1, ketbra, ket0, ket1] using
                      (TwoControl.kron_apply (A := (1 : Square 4)) (B := proj1) a 1 b 1)
              have hL1 :
                      (((P₀ ⊗ₖ P₁) ⊗ₖ proj0) (@finProdFinEquiv 4 2 (a, 1)) (@finProdFinEquiv 4 2 (b, 1))) = 0 := by
                  simpa [proj0, proj1, ketbra, ket0, ket1] using
                      (TwoControl.kron_apply (A := P₀ ⊗ₖ P₁) (B := proj0) a 1 b 1)
              simpa [Matrix.add_apply, hL0, hL1, ccu_diag2_last_one_block u₀ u₁ a b] using hij
          have hu1One : 1 = u₁ := by
              simpa [diag4, Matrix.one_apply] using congrFun (congrFun hId1 3) 3
          have hu0Eq : u₀ = 1 := by
                            have hSection := (section3_lemma_3_2 1 u₀ (by simp) hu₀).mp <| by
                                refine ⟨P₀, P₁, (1 : Square 4), hP₀, hP₁, Submonoid.one_mem _, ?_⟩
                                simpa using hTensor0
                            rcases hSection with hEq | hEq
                            · exact hEq.symm
                            · simpa using hEq
          exact ⟨hu0Eq, hu1One.symm⟩
        · by_cases hb : β 1 = 0
          · have haNorm : star (β 0) * β 0 = 1 := by
                dsimp [β] at hb ⊢
                simpa [hb] using unitary_column0_norm Q hQ
            have hβproj : ketbra β β = proj0 :=
                ketbra_eq_proj0_of_second_zero hb haNorm
            have hβperpProj : ketbra β_perp β_perp = proj1 := by
                have hsum : ketbra β β + ketbra β_perp β_perp = (1 : Square 2) := by
                    dsimp [β, β_perp]
                    simpa using unitary_column_projector_sum Q hQ
                have hsum' : proj0 + ketbra β_perp β_perp = proj0 + proj1 := by
                    calc
                        proj0 + ketbra β_perp β_perp = ketbra β β + ketbra β_perp β_perp := by
                            rw [hβproj]
                        _ = (1 : Square 2) := hsum
                        _ = proj0 + proj1 := by rw [← proj0_add_proj1]
                exact add_left_cancel hsum'
            have hEqProj :
                    (1 : Square 4) ⊗ₖ proj0 + (P₀ ⊗ₖ P₁) ⊗ₖ proj1 = ccu (diag2 u₀ u₁) := by
                simpa [β, β_perp, hβproj, hβperpProj, TwoControl.one_kron_one 2 2] using hEq
            have hId0 : (1 : Square 4) = diag4 1 1 1 u₀ := by
                ext a b
                have hij := congrFun (congrFun hEqProj (@finProdFinEquiv 4 2 (a, 0))) (@finProdFinEquiv 4 2 (b, 0))
                have hL0 :
                        (((1 : Square 4) ⊗ₖ proj0) (@finProdFinEquiv 4 2 (a, 0)) (@finProdFinEquiv 4 2 (b, 0))) =
                            (1 : Square 4) a b := by
                    simpa [proj0, proj1, ketbra, ket0, ket1] using
                        (TwoControl.kron_apply (A := (1 : Square 4)) (B := proj0) a 0 b 0)
                have hL1 :
                        (((P₀ ⊗ₖ P₁) ⊗ₖ proj1) (@finProdFinEquiv 4 2 (a, 0)) (@finProdFinEquiv 4 2 (b, 0))) = 0 := by
                    simpa [proj0, proj1, ketbra, ket0, ket1] using
                        (TwoControl.kron_apply (A := P₀ ⊗ₖ P₁) (B := proj1) a 0 b 0)
                simpa [Matrix.add_apply, hL0, hL1, ccu_diag2_last_zero_block u₀ u₁ a b] using hij
            have hTensor1 : P₀ ⊗ₖ P₁ = diag4 1 1 1 u₁ := by
                ext a b
                have hij := congrFun (congrFun hEqProj (@finProdFinEquiv 4 2 (a, 1))) (@finProdFinEquiv 4 2 (b, 1))
                have hL0 :
                        (((1 : Square 4) ⊗ₖ proj0) (@finProdFinEquiv 4 2 (a, 1)) (@finProdFinEquiv 4 2 (b, 1))) = 0 := by
                    simpa [proj0, proj1, ketbra, ket0, ket1] using
                        (TwoControl.kron_apply (A := (1 : Square 4)) (B := proj0) a 1 b 1)
                have hL1 :
                        (((P₀ ⊗ₖ P₁) ⊗ₖ proj1) (@finProdFinEquiv 4 2 (a, 1)) (@finProdFinEquiv 4 2 (b, 1))) =
                            (P₀ ⊗ₖ P₁) a b := by
                    simpa [proj0, proj1, ketbra, ket0, ket1] using
                        (TwoControl.kron_apply (A := P₀ ⊗ₖ P₁) (B := proj1) a 1 b 1)
                simpa [Matrix.add_apply, hL0, hL1, ccu_diag2_last_one_block u₀ u₁ a b] using hij
            have hu0One : 1 = u₀ := by
                simpa [diag4, Matrix.one_apply] using congrFun (congrFun hId0 3) 3
            have hu1Eq : u₁ = 1 := by
                have hSection := (section3_lemma_3_2 1 u₁ (by simp) hu₁).mp <| by
                    refine ⟨P₀, P₁, (1 : Square 4), hP₀, hP₁, Submonoid.one_mem _, ?_⟩
                    simpa using hTensor1
                rcases hSection with hEq | hEq
                · simpa using hEq.symm
                · simpa using hEq
            exact ⟨hu0One.symm, hu1Eq⟩
          · let μ : ℂ := (P₀ ⊗ₖ P₁) 3 3
            have hBlock : ketbra β β + μ • ketbra β_perp β_perp = diag2 u₀ u₁ := by
                ext i j
                have hij := congrFun (congrFun hEq (@finProdFinEquiv 4 2 (3, i))) (@finProdFinEquiv 4 2 (3, j))
                have hLeftβ :
                        (((1 : Square 2) ⊗ₖ (1 : Square 2) ⊗ₖ ketbra β β)
                            (@finProdFinEquiv 4 2 (3, i)) (@finProdFinEquiv 4 2 (3, j))) =
                            (ketbra β β) i j := by
                    rw [TwoControl.kron_apply]
                    simp [TwoControl.one_kron_one 2 2]
                have hLeftβperp :
                        ((P₀ ⊗ₖ P₁ ⊗ₖ ketbra β_perp β_perp)
                            (@finProdFinEquiv 4 2 (3, i)) (@finProdFinEquiv 4 2 (3, j))) =
                            μ * (ketbra β_perp β_perp) i j := by
                    simpa [μ] using (TwoControl.kron_apply (A := P₀ ⊗ₖ P₁) (B := ketbra β_perp β_perp) 3 i 3 j)
                have hRight :
                        (ccu (diag2 u₀ u₁)) (@finProdFinEquiv 4 2 (3, i)) (@finProdFinEquiv 4 2 (3, j)) =
                            (diag2 u₀ u₁) i j := ccu_diag2_11_block u₀ u₁ i j
                simpa [β, β_perp, smul_eq_mul, hLeftβ, hLeftβperp, hRight] using hij
            have hβeig : β = (diag2 u₀ u₁).mulVec β := by
                have hApply := congrArg (fun M => M.mulVec β) hBlock
                simpa [Matrix.add_mulVec, Matrix.smul_mulVec,
                    ketbra_self_mulVec_of_dotProduct_eq_one hβnorm,
                    ketbra_orthogonal_mulVec hβorth] using hApply
            have h0 : β 0 = u₀ * β 0 := by
                simpa using congrFun hβeig 0
            have h1 : β 1 = u₁ * β 1 := by
                simpa using congrFun hβeig 1
            have hu0One : 1 = u₀ := by
                have h0' : 1 * β 0 = u₀ * β 0 := by simpa using h0
                exact mul_right_cancel₀ ha h0'
            have hu1One : 1 = u₁ := by
                have h1' : 1 * β 1 = u₁ * β 1 := by simpa using h1
                exact mul_right_cancel₀ hb h1'
            exact ⟨hu0One.symm, hu1One.symm⟩
    ·
        rintro ⟨rfl, rfl⟩
        refine ⟨(1 : Square 2), (1 : Square 2), Submonoid.one_mem _, Submonoid.one_mem _, ?_⟩
        calc
            (1 : Square 2) ⊗ₖ (1 : Square 2) ⊗ₖ ketbra (Q.mulVec ket0) (Q.mulVec ket0) +
                    (1 : Square 2) ⊗ₖ (1 : Square 2) ⊗ₖ ketbra (Q.mulVec ket1) (Q.mulVec ket1)
                    = ((1 : Square 2) ⊗ₖ (1 : Square 2)) ⊗ₖ
                            (ketbra (Q.mulVec ket0) (Q.mulVec ket0) + ketbra (Q.mulVec ket1) (Q.mulVec ket1)) := by
                                symm
                                exact kron_add_right ((1 : Square 2) ⊗ₖ (1 : Square 2))
                                    (ketbra (Q.mulVec ket0) (Q.mulVec ket0)) (ketbra (Q.mulVec ket1) (Q.mulVec ket1))
            _ = ((1 : Square 2) ⊗ₖ (1 : Square 2)) ⊗ₖ (1 : Square 2) := by
                        rw [unitary_column_projector_sum Q hQ]
            _ = (1 : Square 8) := by
                        rw [TwoControl.one_kron_one 2 2]
                        simpa using (TwoControl.one_kron_one 4 2)
            _ = ccu (diag2 1 1) := by
                        symm
                        exact ccu_diag2_one

/-- **Lemma 4.3** (Third building block).
    Suppose `u₀, u₁` are complex numbers with `‖u₀‖ = 1` and `‖u₁‖ = 1`.
    There exist 4×4 unitaries `V₁, V₂, V₃, V₄` and 2×2 unitaries `P₀, P₁`,
    where `V₁ = |0⟩⟨0| ⊗ P₀ + |1⟩⟨1| ⊗ P₁`,
    such that `(V₁)_{AC} · (V₂)_{BC} · (V₃)_{AC} · (V₄)_{BC} = CC(Diag(u₀, u₁))`
    if and only if either `u₀ = u₁` or `u₀ * u₁ = 1`. -/
lemma section4_lemma_4_3 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (V₁ V₂ V₃ V₄ : Square 4),
      V₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      ∃ (P₀ P₁ : Square 2),
        P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        V₁ = proj0 ⊗ₖ P₀ + proj1 ⊗ₖ P₁ ∧
        acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ = ccu (diag2 u₀ u₁))
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by sorry

/-- **Lemma 4.4** (Fourth building block).
    Suppose `u₀, u₁` are complex numbers with `‖u₀‖ = 1` and `‖u₁‖ = 1`.
    There exist 4×4 unitaries `V₁, V₂, V₃, V₄` and 2×2 unitaries `P₀, P₁`,
    where `V₄ = |0⟩⟨0| ⊗ P₀ + |1⟩⟨1| ⊗ P₁`,
    such that `(V₁)_{AC} · (V₂)_{BC} · (V₃)_{AC} · (V₄)_{BC} = CC(Diag(u₀, u₁))`
    if and only if either `u₀ = u₁` or `u₀ * u₁ = 1`. -/
lemma section4_lemma_4_4 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (V₁ V₂ V₃ V₄ : Square 4),
      V₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      V₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      ∃ (P₀ P₁ : Square 2),
        P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        V₄ = proj0 ⊗ₖ P₀ + proj1 ⊗ₖ P₁ ∧
        acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ = ccu (diag2 u₀ u₁))
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by sorry

end TwoControl

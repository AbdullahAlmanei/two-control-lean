import TwoControl.BlockHelpers
import TwoControl.DiagonalizationHelpers
import TwoControl.KronHelpers
import TwoControl.SwapHelpers
import TwoControl.GateHelpers
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

private lemma diag4_one : diag4 1 1 1 1 = (1 : Square 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag4]

private lemma controlledGate_diag2_one : controlledGate (diag2 1 1) = (1 : Square 4) := by
    rw [controlledGate_diag2_eq, diag4_one]

private lemma ccu_diag2_one : ccu (diag2 1 1) = (1 : Square 8) := by
    calc
        ccu (diag2 1 1) = proj0 ⊗ₖ (1 : Square 4) + proj1 ⊗ₖ (1 : Square 4) := by
            rw [ccu, controlledGate_diag2_one]
        _ = (proj0 + proj1) ⊗ₖ (1 : Square 4) := by
            symm
            exact kron_add_left proj0 proj1 (1 : Square 4)
        _ = (1 : Square 2) ⊗ₖ (1 : Square 4) := by rw [BlockHelpers.proj0_add_proj1]
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

@[simp] private lemma finProdFinEquiv_00 : (@finProdFinEquiv 2 2 (0, 0) : Fin 4) = 0 := by
    decide

@[simp] private lemma finProdFinEquiv_01 : (@finProdFinEquiv 2 2 (0, 1) : Fin 4) = 1 := by
    decide

@[simp] private lemma finProdFinEquiv_10 : (@finProdFinEquiv 2 2 (1, 0) : Fin 4) = 2 := by
    decide

@[simp] private lemma finProdFinEquiv_11 : (@finProdFinEquiv 2 2 (1, 1) : Fin 4) = 3 := by
    decide

@[simp] private lemma finProdFinEquiv_symm_0 :
        ((@finProdFinEquiv 2 2).symm (0 : Fin 4)) = (0, 0) := by
    decide

@[simp] private lemma finProdFinEquiv_symm_1 :
        ((@finProdFinEquiv 2 2).symm (1 : Fin 4)) = (0, 1) := by
    decide

@[simp] private lemma finProdFinEquiv_symm_2 :
        ((@finProdFinEquiv 2 2).symm (2 : Fin 4)) = (1, 0) := by
    decide

@[simp] private lemma finProdFinEquiv_symm_3 :
        ((@finProdFinEquiv 2 2).symm (3 : Fin 4)) = (1, 1) := by
    decide

@[simp] private lemma finProdFinEquiv_30 : (@finProdFinEquiv 4 2 (3, 0) : Fin 8) = 6 := by
    decide

@[simp] private lemma finProdFinEquiv_31 : (@finProdFinEquiv 4 2 (3, 1) : Fin 8) = 7 := by
    decide

private lemma finProd_assoc_11 (i : Fin 2) :
        (@finProdFinEquiv 4 2 (3, i) : Fin 8) = @finProdFinEquiv 2 4 (1, @finProdFinEquiv 2 2 (1, i)) := by
    simpa [finProdFinEquiv_11] using (BlockHelpers.finProd_assoc_222 1 1 i)

private lemma ccu_diag2_last_zero_block (u₀ u₁ : ℂ) (a b : Fin 4) :
        (ccu (diag2 u₀ u₁)) (@finProdFinEquiv 4 2 (a, 0)) (@finProdFinEquiv 4 2 (b, 0)) =
            (diag4 1 1 1 u₀) a b := by
    obtain ⟨⟨a1, a2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective a
    obtain ⟨⟨b1, b2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective b
    rw [BlockHelpers.finProd_assoc_222 a1 a2 0, BlockHelpers.finProd_assoc_222 b1 b2 0]
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
    rw [BlockHelpers.finProd_assoc_222 a1 a2 1, BlockHelpers.finProd_assoc_222 b1 b2 1]
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
            simpa [dotProduct] using GateHelpers.unitary_column0_norm Q hQ
        have hβorth : star β_perp ⬝ᵥ β = 0 := by
            dsimp [β, β_perp]
            simpa [dotProduct] using GateHelpers.unitary_columns_orthogonal_left Q hQ
        by_cases ha : β 0 = 0
        · have hbNorm : star (β 1) * β 1 = 1 := by
              dsimp [β] at ha ⊢
              simpa [ha] using GateHelpers.unitary_column0_norm Q hQ
          have hβproj : ketbra β β = proj1 :=
              GateHelpers.ketbra_eq_proj1_of_first_zero ha hbNorm
          have hβperpProj : ketbra β_perp β_perp = proj0 := by
              have hsum : ketbra β β + ketbra β_perp β_perp = (1 : Square 2) := by
                  dsimp [β, β_perp]
                  simpa using GateHelpers.unitary_column_projector_sum Q hQ
              have hsum' : proj1 + ketbra β_perp β_perp = proj1 + proj0 := by
                  calc
                      proj1 + ketbra β_perp β_perp = ketbra β β + ketbra β_perp β_perp := by
                          rw [hβproj]
                      _ = (1 : Square 2) := hsum
                      _ = proj0 + proj1 := by rw [← BlockHelpers.proj0_add_proj1]
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
                simpa [hb] using GateHelpers.unitary_column0_norm Q hQ
            have hβproj : ketbra β β = proj0 :=
                GateHelpers.ketbra_eq_proj0_of_second_zero hb haNorm
            have hβperpProj : ketbra β_perp β_perp = proj1 := by
                have hsum : ketbra β β + ketbra β_perp β_perp = (1 : Square 2) := by
                    dsimp [β, β_perp]
                    simpa using GateHelpers.unitary_column_projector_sum Q hQ
                have hsum' : proj0 + ketbra β_perp β_perp = proj0 + proj1 := by
                    calc
                        proj0 + ketbra β_perp β_perp = ketbra β β + ketbra β_perp β_perp := by
                            rw [hβproj]
                        _ = (1 : Square 2) := hsum
                        _ = proj0 + proj1 := by rw [← BlockHelpers.proj0_add_proj1]
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
                    GateHelpers.ketbra_self_mulVec_of_dotProduct_eq_one hβnorm,
                    GateHelpers.ketbra_orthogonal_mulVec hβorth] using hApply
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
                                exact KronHelpers.kron_add_right ((1 : Square 2) ⊗ₖ (1 : Square 2))
                                    (ketbra (Q.mulVec ket0) (Q.mulVec ket0)) (ketbra (Q.mulVec ket1) (Q.mulVec ket1))
            _ = ((1 : Square 2) ⊗ₖ (1 : Square 2)) ⊗ₖ (1 : Square 2) := by
                        rw [GateHelpers.unitary_column_projector_sum Q hQ]
            _ = (1 : Square 8) := by
                        rw [TwoControl.one_kron_one 2 2]
                        simpa using (TwoControl.one_kron_one 4 2)
            _ = ccu (diag2 1 1) := by
                        symm
                        exact ccu_diag2_one

private lemma mul_eq_zero_of_unitary_left {n : ℕ} {U M : Square n}
        (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (h : U * M = 0) :
        M = 0 := by
    have hUleft : star U * U = 1 :=
        Matrix.mem_unitaryGroup_iff'.mp hU
    calc
        M = 1 * M := by simp
        _ = (star U * U) * M := by rw [← hUleft]
        _ = U† * (U * M) := by simp [Matrix.star_eq_conjTranspose, mul_assoc]
        _ = 0 := by rw [h]; simp

private lemma mul_eq_zero_of_unitary_right {n : ℕ} {M U : Square n}
        (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (h : M * U = 0) :
        M = 0 := by
    have hUright : U * star U = 1 :=
        Matrix.mem_unitaryGroup_iff.mp hU
    calc
        M = M * 1 := by simp
        _ = M * (U * star U) := by rw [← hUright]
        _ = (M * U) * U† := by simp [Matrix.star_eq_conjTranspose, mul_assoc]
        _ = 0 := by rw [h]; simp

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
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by
    constructor
    ·
        rintro ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, P₀, P₁, hP₀, hP₁, hV₁eq, hEq⟩
        let V3b : BlockMatrix 2 := blockify (n := 2) V₃
        let Q₀₀ : Square 2 := V3b.toBlocks₁₁
        let Q₀₁ : Square 2 := V3b.toBlocks₁₂
        let Q₁₀ : Square 2 := V3b.toBlocks₂₁
        let Q₁₁ : Square 2 := V3b.toBlocks₂₂
        have hBlocks :
                Matrix.fromBlocks
                    (((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ Q₀₀) * V₄)
                    (((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ Q₀₁) * V₄)
                    (((1 : Square 2) ⊗ₖ P₁) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₀) * V₄)
                    (((1 : Square 2) ⊗ₖ P₁) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₁) * V₄)
                = Matrix.fromBlocks (1 : Square 4) 0 0 (controlledGate (diag2 u₀ u₁)) := by
            calc
                Matrix.fromBlocks
                    (((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ Q₀₀) * V₄)
                    (((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ Q₀₁) * V₄)
                    (((1 : Square 2) ⊗ₖ P₁) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₀) * V₄)
                    (((1 : Square 2) ⊗ₖ P₁) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₁) * V₄)
                    = blockify (n := 4) (acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄) := by
                        rw [blockify_mul, blockify_mul, blockify_mul, hV₁eq, GateHelpers.blockify_acgate,
                            GateHelpers.blockify_bcgate, GateHelpers.blockify_acgate, GateHelpers.blockify_bcgate]
                        dsimp [V3b, Q₀₀, Q₀₁, Q₁₀, Q₁₁]
                        rw [blockify_add, blockify_proj0_kron, blockify_proj1_kron]
                        simp [Matrix.fromBlocks_add, Matrix.fromBlocks_multiply,
                            TwoControl.zero_kron_right, mul_assoc]
                _ = blockify (n := 4) (ccu (diag2 u₀ u₁)) := by
                        simpa using congrArg (blockify (n := 4)) hEq
                _ = Matrix.fromBlocks (1 : Square 4) 0 0 (controlledGate (diag2 u₀ u₁)) := by
                        rw [ccu, blockify_add, blockify_proj0_kron, blockify_proj1_kron]
                        simp [Matrix.fromBlocks_add]
        rcases Matrix.fromBlocks_inj.mp hBlocks with ⟨h00, h01, h10, h11⟩
        have hOneKronP₀ : ((1 : Square 2) ⊗ₖ P₀) ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
            kron_unitary_two (1 : Square 2) P₀ (Submonoid.one_mem _) hP₀
        have hOneKronP₁ : ((1 : Square 2) ⊗ₖ P₁) ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
            kron_unitary_two (1 : Square 2) P₁ (Submonoid.one_mem _) hP₁
        have hLeft₀ : ((1 : Square 2) ⊗ₖ P₀) * V₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
            exact Submonoid.mul_mem _ hOneKronP₀ hV₂
        have hLeft₁ : ((1 : Square 2) ⊗ₖ P₁) * V₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
            exact Submonoid.mul_mem _ hOneKronP₁ hV₂
        have hMid₀₁ : ((1 : Square 2) ⊗ₖ Q₀₁) * V₄ = 0 := by
            apply mul_eq_zero_of_unitary_left hLeft₀
            simpa [mul_assoc] using h01
        have hMid₁₀ : ((1 : Square 2) ⊗ₖ Q₁₀) * V₄ = 0 := by
            apply mul_eq_zero_of_unitary_left hLeft₁
            simpa [mul_assoc] using h10
        have hOneKronQ₀₁ : (1 : Square 2) ⊗ₖ Q₀₁ = 0 := by
            exact mul_eq_zero_of_unitary_right hV₄ hMid₀₁
        have hOneKronQ₁₀ : (1 : Square 2) ⊗ₖ Q₁₀ = 0 := by
            exact mul_eq_zero_of_unitary_right hV₄ hMid₁₀
        have hQ₀₁ : Q₀₁ = 0 := KronHelpers.eq_zero_of_one_kron_eq_zero Q₀₁ hOneKronQ₀₁
        have hQ₁₀ : Q₁₀ = 0 := KronHelpers.eq_zero_of_one_kron_eq_zero Q₁₀ hOneKronQ₁₀
        have hV3bBlocks : V3b = Matrix.fromBlocks Q₀₀ Q₀₁ Q₁₀ Q₁₁ := by
            symm
            exact Matrix.fromBlocks_toBlocks V3b
        have hV3diag : V3b = Matrix.fromBlocks Q₀₀ 0 0 Q₁₁ := by
            rw [hV3bBlocks, hQ₀₁, hQ₁₀]
        have hV3bUnitary : V3b ∈ Matrix.unitaryGroup (Fin 2 ⊕ Fin 2) ℂ := by
            dsimp [V3b]
            exact (blockify_mem_unitaryGroup_iff (n := 2) (U := V₃)).2 hV₃
        have hV3diagUnitary : Matrix.fromBlocks Q₀₀ 0 0 Q₁₁ ∈ Matrix.unitaryGroup (Fin 2 ⊕ Fin 2) ℂ := by
            simpa [hV3diag] using hV3bUnitary
        have ⟨hQ₀₀, hQ₁₁⟩ := BlockHelpers.block_diagonal_unitary Q₀₀ Q₁₁ hV3diagUnitary
        have hV₄right : V₄ * V₄† = 1 := by
            simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hV₄)
        have hEq₀ : ((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ Q₀₀) = V₄† := by
            calc
                ((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ Q₀₀)
                    = (((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ Q₀₀)) * 1 := by simp
                _ = (((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ Q₀₀)) * (V₄ * V₄†) := by
                    rw [← hV₄right]
                _ = ((((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ Q₀₀)) * V₄) * V₄† := by
                    simp [mul_assoc]
                _ = V₄† := by rw [h00]; simp
        have hEq₁ : ((1 : Square 2) ⊗ₖ P₁) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₁)
                = controlledGate (diag2 u₀ u₁) * V₄† := by
            calc
                ((1 : Square 2) ⊗ₖ P₁) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₁)
                    = (((1 : Square 2) ⊗ₖ P₁) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₁)) * 1 := by simp
                _ = (((1 : Square 2) ⊗ₖ P₁) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₁)) * (V₄ * V₄†) := by
                    rw [← hV₄right]
                _ = ((((1 : Square 2) ⊗ₖ P₁) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₁)) * V₄) * V₄† := by
                    simp [mul_assoc]
                _ = controlledGate (diag2 u₀ u₁) * V₄† := by rw [h11]
        let A₀ : Square 4 := ((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ Q₀₀)
        have hRel₀ : ((1 : Square 2) ⊗ₖ P₁) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₁)
                = controlledGate (diag2 u₀ u₁) * A₀ := by
            simpa [A₀, hEq₀] using hEq₁
        have hOneKronQ₀₀ : ((1 : Square 2) ⊗ₖ Q₀₀) ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
            kron_unitary_two (1 : Square 2) Q₀₀ (Submonoid.one_mem _) hQ₀₀
        have hA₀ : A₀ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
            dsimp [A₀]
            exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hOneKronP₀ hV₂) hOneKronQ₀₀
        have hA₀right : A₀ * A₀† = 1 := by
            simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hA₀)
        have hRel : (((1 : Square 2) ⊗ₖ P₁) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₁)) * A₀†
                = controlledGate (diag2 u₀ u₁) := by
            have hRel' := congrArg (fun M => M * A₀†) hRel₀
            calc
                (((1 : Square 2) ⊗ₖ P₁) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₁)) * A₀†
                    = (controlledGate (diag2 u₀ u₁) * A₀) * A₀† := by simpa [mul_assoc] using hRel'
                _ = controlledGate (diag2 u₀ u₁) := by simp [mul_assoc, hA₀right]
        have hPcombine : ((1 : Square 2) ⊗ₖ (P₀ * P₁†)) * ((1 : Square 2) ⊗ₖ P₁)
                = (1 : Square 2) ⊗ₖ P₀ := by
            have hPleft : P₁† * P₁ = 1 := by
                simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hP₁)
            rw [← kron_mul_two]
            simp [mul_assoc, hPleft]
        have hPcontrol : ((1 : Square 2) ⊗ₖ (P₀ * P₁†)) * controlledGate (diag2 u₀ u₁)
                = ((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ (Q₁₁ * Q₀₀†)) * V₂† * (((1 : Square 2) ⊗ₖ P₀)†) := by
            calc
                ((1 : Square 2) ⊗ₖ (P₀ * P₁†)) * controlledGate (diag2 u₀ u₁)
                    = ((1 : Square 2) ⊗ₖ (P₀ * P₁†)) *
                        ((((1 : Square 2) ⊗ₖ P₁) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₁)) * A₀†) := by
                            rw [hRel]
                _ = (((1 : Square 2) ⊗ₖ (P₀ * P₁†)) * ((1 : Square 2) ⊗ₖ P₁)) *
                        V₂ * ((1 : Square 2) ⊗ₖ Q₁₁) * A₀† := by simp [mul_assoc]
                _ = ((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₁) * A₀† := by rw [hPcombine]
                _ = ((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ Q₁₁) *
                        ((((1 : Square 2) ⊗ₖ Q₀₀)†) * V₂† * (((1 : Square 2) ⊗ₖ P₀)†)) := by
                            simp [A₀, Matrix.conjTranspose_mul, mul_assoc]
                _ = ((1 : Square 2) ⊗ₖ P₀) * V₂ * (((1 : Square 2) ⊗ₖ Q₁₁) * (((1 : Square 2) ⊗ₖ Q₀₀)†)) *
                        V₂† * (((1 : Square 2) ⊗ₖ P₀)†) := by simp [mul_assoc]
                _ = ((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ (Q₁₁ * Q₀₀†)) *
                        V₂† * (((1 : Square 2) ⊗ₖ P₀)†) := by
                    rw [conjTranspose_kron_two, ← kron_mul_two]
                    simp [mul_assoc]
        have hR : Q₁₁ * Q₀₀† ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
            exact Submonoid.mul_mem _ hQ₁₁ (conjTranspose_mem_unitaryGroup hQ₀₀)
        rcases unitary_diag2_exists (Q₁₁ * Q₀₀†) hR with ⟨r₀, r₁, W, hr₀, hr₁, hW, hRdiag⟩
        let U' : Square 4 := ((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ W)
        have hOneKronW : ((1 : Square 2) ⊗ₖ W) ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
            kron_unitary_two (1 : Square 2) W (Submonoid.one_mem _) hW
        have hU' : U' ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
            dsimp [U']
            exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hOneKronP₀ hV₂) hOneKronW
        have hU'dag : U'† = ((1 : Square 2) ⊗ₖ W†) * V₂† * (((1 : Square 2) ⊗ₖ P₀)†) := by
            dsimp [U']
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, conjTranspose_kron_two]
            simp [mul_assoc]
        have hRdiagKron : ((1 : Square 2) ⊗ₖ (Q₁₁ * Q₀₀†))
                = ((1 : Square 2) ⊗ₖ W) * ((1 : Square 2) ⊗ₖ diag2 r₀ r₁) * ((1 : Square 2) ⊗ₖ W†) := by
            rw [hRdiag, ← kron_mul_two, ← kron_mul_two]
            simp [mul_assoc]
        have hWitness : ((1 : Square 2) ⊗ₖ (P₀ * P₁†)) * controlledGate (diag2 u₀ u₁)
                = U' * diag4 r₀ r₁ r₀ r₁ * U'† := by
            calc
                ((1 : Square 2) ⊗ₖ (P₀ * P₁†)) * controlledGate (diag2 u₀ u₁)
                    = ((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ (Q₁₁ * Q₀₀†)) *
                        V₂† * (((1 : Square 2) ⊗ₖ P₀)†) := hPcontrol
                _ = ((1 : Square 2) ⊗ₖ P₀) * V₂ *
                        (((1 : Square 2) ⊗ₖ W) * ((1 : Square 2) ⊗ₖ diag2 r₀ r₁) * ((1 : Square 2) ⊗ₖ W†)) *
                        V₂† * (((1 : Square 2) ⊗ₖ P₀)†) := by rw [hRdiagKron]
                _ = ((1 : Square 2) ⊗ₖ P₀) * V₂ * ((1 : Square 2) ⊗ₖ W) *
                        ((1 : Square 2) ⊗ₖ diag2 r₀ r₁) * U'† := by
                    rw [hU'dag]
                    simp [mul_assoc]
                _ = U' * ((1 : Square 2) ⊗ₖ diag2 r₀ r₁) * U'† := by
                    simp [U', mul_assoc]
                _ = U' * diag4 r₀ r₁ r₀ r₁ * U'† := by rw [DiagonalizationHelpers.one_kron_diag2]
        exact (section3_lemma_3_3 u₀ u₁ hu₀ hu₁).mp <| by
            refine ⟨P₀ * P₁†, ?_, U', hU', r₀, r₁, hWitness⟩
            exact Submonoid.mul_mem _ hP₀ (conjTranspose_mem_unitaryGroup hP₁)
    ·
        intro h
        rcases (section3_lemma_3_3 u₀ u₁ hu₀ hu₁).2 h with ⟨P, hP, U, hU, c, d, hEq⟩
        have hPstar : P† ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
            conjTranspose_mem_unitaryGroup hP
        have hOneKronP : ((1 : Square 2) ⊗ₖ P) ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
            kron_unitary_two (1 : Square 2) P (Submonoid.one_mem _) hP
        have hCtrl : controlledGate (diag2 u₀ u₁) ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
            rw [controlledGate_diag2_eq]
            exact DiagonalizationHelpers.diag4_unitary 1 1 u₀ u₁ (by simp) (by simp) hu₀ hu₁
        have hM : ((1 : Square 2) ⊗ₖ P * controlledGate (diag2 u₀ u₁)) ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
            exact Submonoid.mul_mem _ hOneKronP hCtrl
        have hRep : diag4 c d c d ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
            have hconj : U† * (((1 : Square 2) ⊗ₖ P) * controlledGate (diag2 u₀ u₁)) * U = diag4 c d c d := by
                calc
                    U† * (((1 : Square 2) ⊗ₖ P) * controlledGate (diag2 u₀ u₁)) * U
                        = U† * (U * diag4 c d c d * U†) * U := by rw [hEq]
                    _ = diag4 c d c d := by
                        have hUleft : U† * U = 1 := by
                            simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hU)
                        calc
                            U† * (U * diag4 c d c d * U†) * U
                                = (U† * U) * diag4 c d c d * (U† * U) := by simp [mul_assoc]
                            _ = diag4 c d c d := by simp [hUleft]
            simpa [hconj] using unitary_conj_mem_unitaryGroup hM hU
        have ⟨hc, hd⟩ := DiagonalizationHelpers.diag4_repeat_norms_of_mem_unitaryGroup hRep
        have hDiag : diag2 c d ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
            diag2_unitary c d hc hd
        have hV₁ : controlledGate P† ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
            GateHelpers.controlledGate_unitary P† hPstar
        have hV₃ : controlledGate (diag2 c d) ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
            GateHelpers.controlledGate_unitary (diag2 c d) hDiag
        have hV₁block :
                blockify (n := 4) (acgate (controlledGate P†)) =
                    Matrix.fromBlocks (1 : Square 4) 0 0 ((1 : Square 2) ⊗ₖ P†) := by
            rw [GateHelpers.blockify_acgate]
            unfold controlledGate
            rw [blockify_add, blockify_proj0_kron, blockify_proj1_kron]
            simp [Matrix.fromBlocks_add, TwoControl.one_kron_one 2 2, TwoControl.zero_kron_right]
        have hV₃block :
                blockify (n := 4) (acgate (controlledGate (diag2 c d))) =
                    Matrix.fromBlocks (1 : Square 4) 0 0 (diag4 c d c d) := by
            rw [GateHelpers.blockify_acgate]
            unfold controlledGate
            rw [blockify_add, blockify_proj0_kron, blockify_proj1_kron]
            simp [Matrix.fromBlocks_add, TwoControl.one_kron_one 2 2, DiagonalizationHelpers.one_kron_diag2,
            TwoControl.zero_kron_right]
        have hCtrlEq :
                controlledGate (diag2 u₀ u₁) =
                    ((1 : Square 2) ⊗ₖ P†) * U * diag4 c d c d * U† := by
            have hPleft : P† * P = 1 := by
                simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hP)
            calc
                controlledGate (diag2 u₀ u₁) = (1 : Square 4) * controlledGate (diag2 u₀ u₁) := by simp
                _ = (((1 : Square 2) ⊗ₖ P†) * ((1 : Square 2) ⊗ₖ P)) * controlledGate (diag2 u₀ u₁) := by
                    rw [← kron_mul_two, hPleft]
                    simp [TwoControl.one_kron_one 2 2]
                _ = ((1 : Square 2) ⊗ₖ P†) * (((1 : Square 2) ⊗ₖ P) * controlledGate (diag2 u₀ u₁)) := by
                    simp [mul_assoc]
                _ = ((1 : Square 2) ⊗ₖ P†) * (U * diag4 c d c d * U†) := by rw [hEq]
                _ = ((1 : Square 2) ⊗ₖ P†) * U * diag4 c d c d * U† := by simp [mul_assoc]
        refine ⟨controlledGate P†, U, controlledGate (diag2 c d), U†,
            hV₁, hU, hV₃, conjTranspose_mem_unitaryGroup hU,
            1, P†, Submonoid.one_mem _, hPstar, ?_, ?_⟩
        · simp [controlledGate]
        ·
            apply (blockify_injective (n := 4))
            calc
                blockify (acgate (controlledGate P†) * bcgate U * acgate (controlledGate (diag2 c d)) * bcgate U†)
                    = Matrix.fromBlocks (1 : Square 4) 0 0 ((1 : Square 2) ⊗ₖ P†) *
                        Matrix.fromBlocks U 0 0 U *
                        Matrix.fromBlocks (1 : Square 4) 0 0 (diag4 c d c d) *
                        Matrix.fromBlocks U† 0 0 U† := by
                            rw [blockify_mul, blockify_mul, blockify_mul,
                                hV₁block, GateHelpers.blockify_bcgate, hV₃block, GateHelpers.blockify_bcgate]
                _ = Matrix.fromBlocks (1 : Square 4) 0 0 (((1 : Square 2) ⊗ₖ P†) * U * diag4 c d c d * U†) := by
                        rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
                        have hUright : U * U† = 1 := by
                            simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hU)
                        simp [hUright, mul_assoc]
                _ = Matrix.fromBlocks (1 : Square 4) 0 0 (controlledGate (diag2 u₀ u₁)) := by
                        rw [hCtrlEq]
                _ = blockify (n := 4) (ccu (diag2 u₀ u₁)) := by
                        rw [ccu, blockify_add, blockify_proj0_kron, blockify_proj1_kron]
                        simp [Matrix.fromBlocks_add]

private lemma swapab_conj_word_acbc (A B C D : Square 4) :
        swapab * (acgate A * bcgate B * acgate C * bcgate D) * swapab =
            bcgate A * acgate B * bcgate C * acgate D := by
    have hPair₁ :
            (swapab * acgate A * swapab) * (swapab * bcgate B * swapab) =
                swapab * (acgate A * bcgate B) * swapab := by
        calc
            (swapab * acgate A * swapab) * (swapab * bcgate B * swapab)
                = swapab * acgate A * (swapab * swapab) * bcgate B * swapab := by
                    simp [mul_assoc]
            _ = swapab * acgate A * bcgate B * swapab := by
                    rw [SwapHelpers.swapab_mul_swapab]
                    simp [mul_assoc]
            _ = swapab * (acgate A * bcgate B) * swapab := by
                    simp [mul_assoc]
    have hPair₂ :
            (swapab * acgate C * swapab) * (swapab * bcgate D * swapab) =
                swapab * (acgate C * bcgate D) * swapab := by
        calc
            (swapab * acgate C * swapab) * (swapab * bcgate D * swapab)
                = swapab * acgate C * (swapab * swapab) * bcgate D * swapab := by
                    simp [mul_assoc]
            _ = swapab * acgate C * bcgate D * swapab := by
                    rw [SwapHelpers.swapab_mul_swapab]
                    simp [mul_assoc]
            _ = swapab * (acgate C * bcgate D) * swapab := by
                    simp [mul_assoc]
    calc
        swapab * (acgate A * bcgate B * acgate C * bcgate D) * swapab
            = (swapab * (acgate A * bcgate B) * swapab) *
                (swapab * (acgate C * bcgate D) * swapab) := by
                    symm
                    calc
                        (swapab * (acgate A * bcgate B) * swapab) *
                                (swapab * (acgate C * bcgate D) * swapab)
                            = swapab * (acgate A * bcgate B) * (swapab * swapab) *
                                (acgate C * bcgate D) * swapab := by
                                    simp [mul_assoc]
                        _ = swapab * (acgate A * bcgate B) * (acgate C * bcgate D) * swapab := by
                                rw [SwapHelpers.swapab_mul_swapab]
                                simp [mul_assoc]
                        _ = swapab * (acgate A * bcgate B * acgate C * bcgate D) * swapab := by
                                simp [mul_assoc]
        _ = ((swapab * acgate A * swapab) * (swapab * bcgate B * swapab)) *
                ((swapab * acgate C * swapab) * (swapab * bcgate D * swapab)) := by
                    rw [← hPair₁, ← hPair₂]
        _ = bcgate A * acgate B * bcgate C * acgate D := by
                rw [GateHelpers.swapab_conj_acgate, GateHelpers.swapab_conj_bcgate,
                    GateHelpers.swapab_conj_acgate, GateHelpers.swapab_conj_bcgate]
                simp [mul_assoc]

private lemma swapab_conj_word_bcac (A B C D : Square 4) :
        swapab * (bcgate A * acgate B * bcgate C * acgate D) * swapab =
            acgate A * bcgate B * acgate C * bcgate D := by
    have hPair₁ :
            (swapab * bcgate A * swapab) * (swapab * acgate B * swapab) =
                swapab * (bcgate A * acgate B) * swapab := by
        calc
            (swapab * bcgate A * swapab) * (swapab * acgate B * swapab)
                = swapab * bcgate A * (swapab * swapab) * acgate B * swapab := by
                    simp [mul_assoc]
            _ = swapab * bcgate A * acgate B * swapab := by
                    rw [SwapHelpers.swapab_mul_swapab]
                    simp [mul_assoc]
            _ = swapab * (bcgate A * acgate B) * swapab := by
                    simp [mul_assoc]
    have hPair₂ :
            (swapab * bcgate C * swapab) * (swapab * acgate D * swapab) =
                swapab * (bcgate C * acgate D) * swapab := by
        calc
            (swapab * bcgate C * swapab) * (swapab * acgate D * swapab)
                = swapab * bcgate C * (swapab * swapab) * acgate D * swapab := by
                    simp [mul_assoc]
            _ = swapab * bcgate C * acgate D * swapab := by
                    rw [SwapHelpers.swapab_mul_swapab]
                    simp [mul_assoc]
            _ = swapab * (bcgate C * acgate D) * swapab := by
                    simp [mul_assoc]
    calc
        swapab * (bcgate A * acgate B * bcgate C * acgate D) * swapab
            = (swapab * (bcgate A * acgate B) * swapab) *
                (swapab * (bcgate C * acgate D) * swapab) := by
                    symm
                    calc
                        (swapab * (bcgate A * acgate B) * swapab) *
                                (swapab * (bcgate C * acgate D) * swapab)
                            = swapab * (bcgate A * acgate B) * (swapab * swapab) *
                                (bcgate C * acgate D) * swapab := by
                                    simp [mul_assoc]
                        _ = swapab * (bcgate A * acgate B) * (bcgate C * acgate D) * swapab := by
                                rw [SwapHelpers.swapab_mul_swapab]
                                simp [mul_assoc]
                        _ = swapab * (bcgate A * acgate B * bcgate C * acgate D) * swapab := by
                                simp [mul_assoc]
        _ = ((swapab * bcgate A * swapab) * (swapab * acgate B * swapab)) *
                ((swapab * bcgate C * swapab) * (swapab * acgate D * swapab)) := by
                    rw [← hPair₁, ← hPair₂]
        _ = acgate A * bcgate B * acgate C * bcgate D := by
                rw [GateHelpers.swapab_conj_bcgate, GateHelpers.swapab_conj_acgate,
                    GateHelpers.swapab_conj_bcgate, GateHelpers.swapab_conj_acgate]
                simp [mul_assoc]

@[simp] private lemma diag2_conjTranspose (a b : ℂ) :
        (diag2 a b)† = diag2 (star a) (star b) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2]

@[simp] private lemma diag4_conjTranspose (a b c d : ℂ) :
        (diag4 a b c d)† = diag4 (star a) (star b) (star c) (star d) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag4]

@[simp] private lemma controlledGate_diag2_conjTranspose (u₀ u₁ : ℂ) :
        (controlledGate (diag2 u₀ u₁))† = controlledGate (diag2 (star u₀) (star u₁)) := by
    rw [controlledGate_diag2_eq, controlledGate_diag2_eq]
    simp

private lemma ccu_diag2_conjTranspose (u₀ u₁ : ℂ) :
        (ccu (diag2 u₀ u₁))† = ccu (diag2 (star u₀) (star u₁)) := by
    rw [ccu, ccu, Matrix.conjTranspose_add, KronHelpers.conjTranspose_kron_reindex,
        KronHelpers.conjTranspose_kron_reindex, controlledGate_diag2_conjTranspose]
    simp

set_option maxHeartbeats 400000 in
private lemma swapab_conj_ccu_diag2 (u₀ u₁ : ℂ) :
        swapab * ccu (diag2 u₀ u₁) * swapab = ccu (diag2 u₀ u₁) := by
    have hOne4 : (1 : Square 4) = (1 : Square 2) ⊗ₖ (1 : Square 2) := by
        symm
        exact TwoControl.one_kron_one 2 2
    have hInnerOne :
            proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ (1 : Square 2) = (1 : Square 2) ⊗ₖ (1 : Square 2) := by
        rw [← BlockHelpers.proj0_add_proj1, kron_add_left, BlockHelpers.proj0_add_proj1]
    calc
        swapab * ccu (diag2 u₀ u₁) * swapab
            = swapab *
                (proj0 ⊗ₖ ((1 : Square 2) ⊗ₖ (1 : Square 2)) +
                  proj1 ⊗ₖ (proj0 ⊗ₖ (1 : Square 2)) +
                  proj1 ⊗ₖ (proj1 ⊗ₖ diag2 u₀ u₁)) * swapab := by
                    unfold ccu controlledGate
                    rw [hOne4, KronHelpers.kron_add_right]
                    simp [add_assoc]
        _ = (1 : Square 2) ⊗ₖ (proj0 ⊗ₖ (1 : Square 2)) +
                proj0 ⊗ₖ (proj1 ⊗ₖ (1 : Square 2)) +
                proj1 ⊗ₖ (proj1 ⊗ₖ diag2 u₀ u₁) := by
                    rw [mul_add, add_mul]
                    rw [mul_add, add_mul]
                    rw [SwapHelpers.swapab_conj_kron_three, SwapHelpers.swapab_conj_kron_three,
                        SwapHelpers.swapab_conj_kron_three]
        _ = proj0 ⊗ₖ ((proj0 ⊗ₖ (1 : Square 2)) + (proj1 ⊗ₖ (1 : Square 2))) +
                proj1 ⊗ₖ ((proj0 ⊗ₖ (1 : Square 2)) + (proj1 ⊗ₖ diag2 u₀ u₁)) := by
                    simpa [add_assoc] using
                        (KronHelpers.split_one_kron_terms
                            (P := proj0 ⊗ₖ (1 : Square 2))
                            (Q := proj1 ⊗ₖ (1 : Square 2))
                            (R := proj1 ⊗ₖ diag2 u₀ u₁))
        _ = proj0 ⊗ₖ ((1 : Square 2) ⊗ₖ (1 : Square 2)) +
                proj1 ⊗ₖ controlledGate (diag2 u₀ u₁) := by
                    unfold controlledGate
                    rw [hInnerOne]
        _ = ccu (diag2 u₀ u₁) := by
                    unfold ccu
                    rw [hOne4]

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
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by
    have hu₀star : ‖star u₀‖ = 1 := by simpa using hu₀
    have hu₁star : ‖star u₁‖ = 1 := by simpa using hu₁
    constructor
    ·
        rintro ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, P₀, P₁, hP₀, hP₁, hV₄eq, hEq⟩
        have hSwap : bcgate V₁ * acgate V₂ * bcgate V₃ * acgate V₄ = ccu (diag2 u₀ u₁) := by
            calc
                bcgate V₁ * acgate V₂ * bcgate V₃ * acgate V₄
                    = swapab * (acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄) * swapab := by
                        symm
                        exact swapab_conj_word_acbc V₁ V₂ V₃ V₄
                _ = swapab * ccu (diag2 u₀ u₁) * swapab := by rw [hEq]
                _ = ccu (diag2 u₀ u₁) := by rw [swapab_conj_ccu_diag2]
        have hAdj : acgate V₄† * bcgate V₃† * acgate V₂† * bcgate V₁†
                = ccu (diag2 (star u₀) (star u₁)) := by
            calc
                acgate V₄† * bcgate V₃† * acgate V₂† * bcgate V₁†
                    = (bcgate V₁ * acgate V₂ * bcgate V₃ * acgate V₄)† := by
                        simp [Matrix.conjTranspose_mul, mul_assoc]
                _ = (ccu (diag2 u₀ u₁))† := by rw [hSwap]
                _ = ccu (diag2 (star u₀) (star u₁)) := by rw [ccu_diag2_conjTranspose]
        have hV₄dagEq : V₄† = proj0 ⊗ₖ P₀† + proj1 ⊗ₖ P₁† := by
            rw [hV₄eq, Matrix.conjTranspose_add, conjTranspose_kron_two, conjTranspose_kron_two]
            simp
        have hStar : star u₀ = star u₁ ∨ star u₀ * star u₁ = 1 :=
            (section4_lemma_4_3 (star u₀) (star u₁) hu₀star hu₁star).1 <| by
                refine ⟨V₄†, V₃†, V₂†, V₁†, conjTranspose_mem_unitaryGroup hV₄,
                    conjTranspose_mem_unitaryGroup hV₃, conjTranspose_mem_unitaryGroup hV₂,
                    conjTranspose_mem_unitaryGroup hV₁, P₀†, P₁†,
                    conjTranspose_mem_unitaryGroup hP₀, conjTranspose_mem_unitaryGroup hP₁,
                    hV₄dagEq, hAdj⟩
        rcases hStar with hStarEq | hStarProd
        · left
          simpa using congrArg star hStarEq
        · right
          simpa [mul_comm] using congrArg star hStarProd
    ·
        intro h
        have hStar : star u₀ = star u₁ ∨ star u₀ * star u₁ = 1 := by
            rcases h with hEq | hProd
            · left
              simpa using congrArg star hEq
            · right
              simpa [mul_comm] using congrArg star hProd
        rcases (section4_lemma_4_3 (star u₀) (star u₁) hu₀star hu₁star).2 hStar with
            ⟨W₁, W₂, W₃, W₄, hW₁, hW₂, hW₃, hW₄, P₀, P₁, hP₀, hP₁, hW₁eq, hEq⟩
        have hW₁dagEq : W₁† = proj0 ⊗ₖ P₀† + proj1 ⊗ₖ P₁† := by
            rw [hW₁eq, Matrix.conjTranspose_add, conjTranspose_kron_two, conjTranspose_kron_two]
            simp
        have hAdj : bcgate W₄† * acgate W₃† * bcgate W₂† * acgate W₁† = ccu (diag2 u₀ u₁) := by
            calc
                bcgate W₄† * acgate W₃† * bcgate W₂† * acgate W₁†
                    = (acgate W₁ * bcgate W₂ * acgate W₃ * bcgate W₄)† := by
                        simp [Matrix.conjTranspose_mul, mul_assoc]
                _ = (ccu (diag2 (star u₀) (star u₁)))† := by rw [hEq]
                _ = ccu (diag2 u₀ u₁) := by
                    rw [ccu_diag2_conjTranspose]
                    simp
        have hFinal : acgate W₄† * bcgate W₃† * acgate W₂† * bcgate W₁† = ccu (diag2 u₀ u₁) := by
            calc
                acgate W₄† * bcgate W₃† * acgate W₂† * bcgate W₁†
                    = swapab * (bcgate W₄† * acgate W₃† * bcgate W₂† * acgate W₁†) * swapab := by
                        symm
                        exact swapab_conj_word_bcac W₄† W₃† W₂† W₁†
                _ = swapab * ccu (diag2 u₀ u₁) * swapab := by rw [hAdj]
                _ = ccu (diag2 u₀ u₁) := by rw [swapab_conj_ccu_diag2]
        refine ⟨W₄†, W₃†, W₂†, W₁†, conjTranspose_mem_unitaryGroup hW₄,
            conjTranspose_mem_unitaryGroup hW₃, conjTranspose_mem_unitaryGroup hW₂,
            conjTranspose_mem_unitaryGroup hW₁, P₀†, P₁†,
            conjTranspose_mem_unitaryGroup hP₀, conjTranspose_mem_unitaryGroup hP₁,
            hW₁dagEq, hFinal⟩

end TwoControl

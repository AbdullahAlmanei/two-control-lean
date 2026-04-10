import TwoControl.Section4

namespace TwoControl

private lemma finProd_assoc_222 (a b c : Fin 2) :
    (@finProdFinEquiv 4 2 (@finProdFinEquiv 2 2 (a, b), c) : Fin 8) =
      @finProdFinEquiv 2 4 (a, @finProdFinEquiv 2 2 (b, c)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

private lemma kron_one_assoc (A : Square 2) :
    (A ⊗ₖ (1 : Square 2)) ⊗ₖ (1 : Square 2) = A ⊗ₖ (1 : Square 4) := by
  ext i j
  obtain ⟨⟨i12, i3⟩, rfl⟩ := (@finProdFinEquiv 4 2).surjective i
  obtain ⟨⟨j12, j3⟩, rfl⟩ := (@finProdFinEquiv 4 2).surjective j
  obtain ⟨⟨i1, i2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective i12
  obtain ⟨⟨j1, j2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective j12
  rw [TwoControl.kron_apply, TwoControl.kron_apply]
  rw [finProd_assoc_222 i1 i2 i3, finProd_assoc_222 j1 j2 j3, TwoControl.kron_apply]
  rw [← TwoControl.one_kron_one 2 2, TwoControl.kron_apply]
  simp [mul_assoc]

private lemma proj0_add_proj1 : proj0 + proj1 = (1 : Square 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, proj1, ketbra, ket0, ket1]

private lemma block_one_eq (n : ℕ) :
    (1 : BlockMatrix n) = Matrix.fromBlocks (1 : Square n) 0 0 (1 : Square n) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]

@[simp] private lemma acgate_add (U W : Square 4) :
    acgate (U + W) = acgate U + acgate W := by
  unfold acgate abgate
  rw [kron_add_left, Matrix.mul_add, Matrix.add_mul]

private lemma kron_add_right (A : Square m) (B₁ B₂ : Square n) :
    A ⊗ₖ (B₁ + B₂) = A ⊗ₖ B₁ + A ⊗ₖ B₂ := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (@finProdFinEquiv m n).surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (@finProdFinEquiv m n).surjective j
  simp [TwoControl.kron_apply, mul_add]

private lemma kron_smul_right (A : Square m) (c : ℂ) (B : Square n) :
    A ⊗ₖ (c • B) = c • (A ⊗ₖ B) := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (@finProdFinEquiv m n).surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (@finProdFinEquiv m n).surjective j
  simp [TwoControl.kron_apply, mul_left_comm]

private lemma kron_mul_reindex_local {m n : ℕ}
    (A B : Square m) (C D : Square n) :
    (A * B) ⊗ₖ (C * D) = (A ⊗ₖ C) * (B ⊗ₖ D) := by
  simpa [TwoControl.kron, Matrix.reindexAlgEquiv_apply] using
    congrArg (Matrix.reindexAlgEquiv ℂ ℂ (@finProdFinEquiv m n))
      (Matrix.mul_kronecker_mul A B C D)

private lemma kron_assoc_222_local (X A B : Square 2) :
    (X ⊗ₖ A) ⊗ₖ B = X ⊗ₖ (A ⊗ₖ B) := by
  ext i j
  obtain ⟨⟨i12, i3⟩, rfl⟩ := (@finProdFinEquiv 4 2).surjective i
  obtain ⟨⟨j12, j3⟩, rfl⟩ := (@finProdFinEquiv 4 2).surjective j
  obtain ⟨⟨i1, i2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective i12
  obtain ⟨⟨j1, j2⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective j12
  rw [TwoControl.kron_apply, TwoControl.kron_apply]
  rw [finProd_assoc_222 i1 i2 i3, finProd_assoc_222 j1 j2 j3, TwoControl.kron_apply,
    TwoControl.kron_apply]
  simp [mul_assoc]

private lemma swap_index_prod (i : Fin 4) :
    ((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)) =
      Prod.swap ((@finProdFinEquiv 2 2).symm i) := by
  fin_cases i <;> decide

private lemma swap2_left_mul_apply (M : Square 4) (i j : Fin 4) :
    (swap2 * M) i j = M ((Equiv.swap (1 : Fin 4) 2) i) j := by
  fin_cases i <;>
    simp [swap2, Matrix.mul_apply, Fin.sum_univ_succ, Equiv.swap_apply_def]

private lemma swap2_right_mul_apply (M : Square 4) (i j : Fin 4) :
    (M * swap2) i j = M i ((Equiv.swap (1 : Fin 4) 2) j) := by
  fin_cases j <;>
    simp [swap2, Matrix.mul_apply, Fin.sum_univ_succ, Equiv.swap_apply_def]

private lemma swap2_conj_apply (M : Square 4) (i j : Fin 4) :
    (swap2 * M * swap2) i j = M ((Equiv.swap (1 : Fin 4) 2) i) ((Equiv.swap (1 : Fin 4) 2) j) := by
  rw [swap2_right_mul_apply, swap2_left_mul_apply]

private lemma swap2_conj_kron_right_local (A : Square 2) :
    swap2 * (A ⊗ₖ (1 : Square 2)) * swap2 = (1 : Square 2) ⊗ₖ A := by
  ext i j
  calc
    (swap2 * (A ⊗ₖ (1 : Square 2)) * swap2) i j
        = (A ⊗ₖ (1 : Square 2)) ((Equiv.swap (1 : Fin 4) 2) i) ((Equiv.swap (1 : Fin 4) 2) j) := by
            rw [swap2_conj_apply]
    _ = A (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).1)
            (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).1) *
            (1 : Square 2) (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).2)
              (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).2) := by
            simpa using
              (TwoControl.kron_apply (A := A) (B := (1 : Square 2))
                (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).1)
                (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).2)
                (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).1)
                (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).2))
    _ = A ((@finProdFinEquiv 2 2).symm i).2 ((@finProdFinEquiv 2 2).symm j).2 *
            (1 : Square 2) ((@finProdFinEquiv 2 2).symm i).1 ((@finProdFinEquiv 2 2).symm j).1 := by
            rw [swap_index_prod i, swap_index_prod j]
            rfl
    _ = ((1 : Square 2) ⊗ₖ A) i j := by
      simpa [mul_comm] using
        (TwoControl.kron_apply (A := (1 : Square 2)) (B := A)
          ((@finProdFinEquiv 2 2).symm i).1
          ((@finProdFinEquiv 2 2).symm i).2
          ((@finProdFinEquiv 2 2).symm j).1
          ((@finProdFinEquiv 2 2).symm j).2).symm

private lemma acgate_kron_two (X A : Square 2) :
    acgate (X ⊗ₖ A) = X ⊗ₖ ((1 : Square 2) ⊗ₖ A) := by
  unfold acgate swapbc abgate
  calc
    ((1 : Square 2) ⊗ₖ swap2) * ((X ⊗ₖ A) ⊗ₖ (1 : Square 2)) * ((1 : Square 2) ⊗ₖ swap2)
        = ((1 : Square 2) ⊗ₖ swap2) * (X ⊗ₖ (A ⊗ₖ (1 : Square 2))) * ((1 : Square 2) ⊗ₖ swap2) := by
            rw [kron_assoc_222_local X A (1 : Square 2)]
    _ = (((1 : Square 2) * X) ⊗ₖ (swap2 * (A ⊗ₖ (1 : Square 2)))) * ((1 : Square 2) ⊗ₖ swap2) := by
            rw [← kron_mul_reindex_local (1 : Square 2) X swap2 (A ⊗ₖ (1 : Square 2))]
    _ = (X ⊗ₖ (swap2 * (A ⊗ₖ (1 : Square 2)))) * ((1 : Square 2) ⊗ₖ swap2) := by
            simp
    _ = (X * (1 : Square 2)) ⊗ₖ ((swap2 * (A ⊗ₖ (1 : Square 2))) * swap2) := by
            rw [← kron_mul_reindex_local X (1 : Square 2) (swap2 * (A ⊗ₖ (1 : Square 2))) swap2]
    _ = X ⊗ₖ ((swap2 * (A ⊗ₖ (1 : Square 2))) * swap2) := by
            simp
    _ = X ⊗ₖ ((1 : Square 2) ⊗ₖ A) := by
            rw [swap2_conj_kron_right_local]

private lemma blockify_bcgate (U : Square 4) :
    blockify (n := 4) (bcgate U) = Matrix.fromBlocks U 0 0 U := by
  unfold bcgate
  rw [← proj0_add_proj1, kron_add_left, blockify_add, blockify_proj0_kron, blockify_proj1_kron]
  simp [Matrix.fromBlocks_add]

private lemma blockify_acgate (U : Square 4) :
    blockify (n := 4) (acgate U) =
      Matrix.fromBlocks
        ((1 : Square 2) ⊗ₖ (blockify (n := 2) U).toBlocks₁₁)
        ((1 : Square 2) ⊗ₖ (blockify (n := 2) U).toBlocks₁₂)
        ((1 : Square 2) ⊗ₖ (blockify (n := 2) U).toBlocks₂₁)
        ((1 : Square 2) ⊗ₖ (blockify (n := 2) U).toBlocks₂₂) := by
  let Ub : BlockMatrix 2 := blockify (n := 2) U
  let A : Square 2 := Ub.toBlocks₁₁
  let B : Square 2 := Ub.toBlocks₁₂
  let C : Square 2 := Ub.toBlocks₂₁
  let D : Square 2 := Ub.toBlocks₂₂
  have hUdecomp : U = proj0 ⊗ₖ A + proj01 ⊗ₖ B + proj10 ⊗ₖ C + proj1 ⊗ₖ D := by
    dsimp [A, B, C, D, Ub]
    simpa using (blockDecomposition (n := 2) U)
  have hBlocks :
      blockify (n := 4) (acgate U) =
        Matrix.fromBlocks ((1 : Square 2) ⊗ₖ A) ((1 : Square 2) ⊗ₖ B)
          ((1 : Square 2) ⊗ₖ C) ((1 : Square 2) ⊗ₖ D) := by
    rw [hUdecomp]
    repeat rw [acgate_add]
    repeat rw [acgate_kron_two]
    simpa using
      (blockify_blockExpansion
        ((1 : Square 2) ⊗ₖ A)
        ((1 : Square 2) ⊗ₖ B)
        ((1 : Square 2) ⊗ₖ C)
        ((1 : Square 2) ⊗ₖ D))
  dsimp [A, B, C, D, Ub] at hBlocks ⊢
  exact hBlocks

private lemma blockify_abgate (U : Square 4) :
    blockify (n := 4) (abgate U) =
      Matrix.fromBlocks
        ((blockify (n := 2) U).toBlocks₁₁ ⊗ₖ (1 : Square 2))
        ((blockify (n := 2) U).toBlocks₁₂ ⊗ₖ (1 : Square 2))
        ((blockify (n := 2) U).toBlocks₂₁ ⊗ₖ (1 : Square 2))
        ((blockify (n := 2) U).toBlocks₂₂ ⊗ₖ (1 : Square 2)) := by
  let Ub : BlockMatrix 2 := blockify (n := 2) U
  let A : Square 2 := Ub.toBlocks₁₁
  let B : Square 2 := Ub.toBlocks₁₂
  let C : Square 2 := Ub.toBlocks₂₁
  let D : Square 2 := Ub.toBlocks₂₂
  have hUdecomp : U = proj0 ⊗ₖ A + proj01 ⊗ₖ B + proj10 ⊗ₖ C + proj1 ⊗ₖ D := by
    dsimp [A, B, C, D, Ub]
    simpa using (blockDecomposition (n := 2) U)
  have hBlocks :
      blockify (n := 4) (abgate U) =
        Matrix.fromBlocks (A ⊗ₖ (1 : Square 2)) (B ⊗ₖ (1 : Square 2))
          (C ⊗ₖ (1 : Square 2)) (D ⊗ₖ (1 : Square 2)) := by
    rw [hUdecomp]
    unfold abgate
    repeat rw [kron_add_left]
    repeat rw [kron_assoc_222_local]
    simpa using
      (blockify_blockExpansion (A ⊗ₖ (1 : Square 2)) (B ⊗ₖ (1 : Square 2))
        (C ⊗ₖ (1 : Square 2)) (D ⊗ₖ (1 : Square 2)))
  dsimp [A, B, C, D, Ub] at hBlocks ⊢
  exact hBlocks

private lemma blockify_controlledGate (P : Square 2) :
    blockify (n := 2) (controlledGate P) = Matrix.fromBlocks (1 : Square 2) 0 0 P := by
  unfold controlledGate
  rw [blockify_add, blockify_proj0_kron, blockify_proj1_kron]
  simp [Matrix.fromBlocks_add]

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

private lemma block_diagonal_unitary {n : ℕ} (A D : Square n)
    (h : Matrix.fromBlocks A 0 0 D ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ) :
    A ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ D ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hleft' : (Matrix.fromBlocks A 0 0 D)† * Matrix.fromBlocks A 0 0 D = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp h)
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at hleft'
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero] at hleft'
  rw [block_one_eq] at hleft'
  have hright' : Matrix.fromBlocks A 0 0 D * (Matrix.fromBlocks A 0 0 D)† = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp h)
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at hright'
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero] at hright'
  rw [block_one_eq] at hright'
  rcases Matrix.fromBlocks_inj.mp hleft' with ⟨hAleft, _, _, hDleft⟩
  rcases Matrix.fromBlocks_inj.mp hright' with ⟨hAright, _, _, hDright⟩
  exact ⟨⟨by simpa using hAleft, by simpa using hAright⟩,
    ⟨by simpa using hDleft, by simpa using hDright⟩⟩

private lemma fromBlocks_diagonal_unitary {n : ℕ} (A D : Square n)
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hD : D ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix.fromBlocks A 0 0 D ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
  have hAleft : A† * A = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hA)
  have hAright : A * A† = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hA)
  have hDleft : D† * D = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hD)
  have hDright : D * D† = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hD)
  constructor
  ·
      rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, block_one_eq]
      simp [hAleft, hDleft]
  ·
      rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, block_one_eq]
      simp [hAright, hDright]

private lemma nonzero_of_unitary {U : Square 4}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) : U ≠ 0 := by
  intro hZero
  have hleft : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [hZero] at hleft
  have h00 := congrFun (congrFun hleft 0) 0
  norm_num at h00

private lemma exists_nonzero_entry_of_ne_zero (M : Square 2) (hM : M ≠ 0) :
    ∃ i j, M i j ≠ 0 := by
  by_cases h00 : M 0 0 = 0
  · by_cases h01 : M 0 1 = 0
    · by_cases h10 : M 1 0 = 0
      · by_cases h11 : M 1 1 = 0
        · exfalso
          apply hM
          ext i j
          fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
        · exact ⟨1, 1, h11⟩
      · exact ⟨1, 0, h10⟩
    · exact ⟨0, 1, h01⟩
  · exact ⟨0, 0, h00⟩

private lemma eq_zero_of_kron_right_entry_ne_zero
    (X A : Square 2) (i j : Fin 2) (hA : A i j ≠ 0)
    (h : X ⊗ₖ A = 0) :
    X = 0 := by
  ext p q
  have hpq := congrFun (congrFun h (@finProdFinEquiv 2 2 (p, i))) (@finProdFinEquiv 2 2 (q, j))
  have hmul : X p q * A i j = 0 := by
    rw [show (X ⊗ₖ A) (@finProdFinEquiv 2 2 (p, i)) (@finProdFinEquiv 2 2 (q, j)) = X p q * A i j by
      simpa using (TwoControl.kron_apply (A := X) (B := A) p i q j)] at hpq
    simpa using hpq
  exact (mul_eq_zero.mp hmul).resolve_right hA

private lemma scalar_of_kron_sum_zero
    (A B F H : Square 2) (hA : A ≠ 0) (hH : H ≠ 0)
    (h : F ⊗ₖ A + H ⊗ₖ B = 0) :
    ∃ c : ℂ, B = c • A ∧ F = (-c) • H := by
  rcases exists_nonzero_entry_of_ne_zero H hH with ⟨iH, jH, hHij⟩
  let c : ℂ := -F iH jH / H iH jH
  have hB : B = c • A := by
    ext r s
    apply mul_left_cancel₀ hHij
    have hEntry := congrFun (congrFun h (@finProdFinEquiv 2 2 (iH, r))) (@finProdFinEquiv 2 2 (jH, s))
    have hFA : (F ⊗ₖ A) (@finProdFinEquiv 2 2 (iH, r)) (@finProdFinEquiv 2 2 (jH, s)) =
        F iH jH * A r s := by
      simpa using (TwoControl.kron_apply (A := F) (B := A) iH r jH s)
    have hHB : (H ⊗ₖ B) (@finProdFinEquiv 2 2 (iH, r)) (@finProdFinEquiv 2 2 (jH, s)) =
        H iH jH * B r s := by
      simpa using (TwoControl.kron_apply (A := H) (B := B) iH r jH s)
    have hEntry0 : F iH jH * A r s + H iH jH * B r s = 0 := by
      rw [← hFA, ← hHB]
      simpa [Matrix.add_apply] using hEntry
    have hEntry' : H iH jH * B r s = -(F iH jH * A r s) := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa [add_comm, add_left_comm, add_assoc] using hEntry0
    calc
      H iH jH * B r s = -(F iH jH * A r s) := hEntry'
      _ = H iH jH * (c * A r s) := by
        unfold c
        field_simp [hHij]
      _ = H iH jH * ((c • A) r s) := by simp
  have hFplus : (F + c • H) ⊗ₖ A = 0 := by
    calc
      (F + c • H) ⊗ₖ A = F ⊗ₖ A + (c • H) ⊗ₖ A := by rw [kron_add_left, kron_smul_left]
      _ = F ⊗ₖ A + H ⊗ₖ (c • A) := by rw [kron_smul_left, kron_smul_right]
      _ = F ⊗ₖ A + H ⊗ₖ B := by rw [hB]
      _ = 0 := h
  rcases exists_nonzero_entry_of_ne_zero A hA with ⟨iA, jA, hAij⟩
  have hFzero : F + c • H = 0 :=
    eq_zero_of_kron_right_entry_ne_zero (F + c • H) A iA jA hAij hFplus
  refine ⟨c, hB, ?_⟩
  calc
    F = -(c • H) := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa [add_comm] using hFzero
    _ = (-c) • H := by simp

private lemma tensor_decomp_of_offdiag_zero
    (E F G H A B C D : Square 2)
    (hOff : F ⊗ₖ A + H ⊗ₖ B = 0)
    (hW00 : E ⊗ₖ A + G ⊗ₖ B ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hW11 : F ⊗ₖ C + H ⊗ₖ D ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ X₀ Y₀ X₁ Y₁ : Square 2,
      E ⊗ₖ A + G ⊗ₖ B = X₀ ⊗ₖ Y₀ ∧
      F ⊗ₖ C + H ⊗ₖ D = X₁ ⊗ₖ Y₁ := by
  have hW00nz : E ⊗ₖ A + G ⊗ₖ B ≠ 0 := nonzero_of_unitary hW00
  have hW11nz : F ⊗ₖ C + H ⊗ₖ D ≠ 0 := nonzero_of_unitary hW11
  by_cases hA0 : A = 0
  · have hHB : H ⊗ₖ B = 0 := by simpa [hA0, TwoControl.zero_kron_right, zero_add] using hOff
    have hB0 : B ≠ 0 := by
      intro hB0
      apply hW00nz
      simp [hA0, hB0, TwoControl.zero_kron_right]
    rcases exists_nonzero_entry_of_ne_zero B hB0 with ⟨iB, jB, hBij⟩
    have hH0 : H = 0 := eq_zero_of_kron_right_entry_ne_zero H B iB jB hBij hHB
    refine ⟨G, B, F, C, ?_, ?_⟩
    · simp [hA0, TwoControl.zero_kron_right]
    · simp [hH0, TwoControl.zero_kron_left]
  · by_cases hB0 : B = 0
    · have hFA : F ⊗ₖ A = 0 := by simpa [hB0, TwoControl.zero_kron_right, add_zero] using hOff
      rcases exists_nonzero_entry_of_ne_zero A hA0 with ⟨iA, jA, hAij⟩
      have hF0 : F = 0 := eq_zero_of_kron_right_entry_ne_zero F A iA jA hAij hFA
      refine ⟨E, A, H, D, ?_, ?_⟩
      · simp [hB0, TwoControl.zero_kron_right]
      · simp [hF0, TwoControl.zero_kron_left]
    · by_cases hH0 : H = 0
      · have hFA : F ⊗ₖ A = 0 := by simpa [hH0, TwoControl.zero_kron_left, add_zero] using hOff
        rcases exists_nonzero_entry_of_ne_zero A hA0 with ⟨iA, jA, hAij⟩
        have hF0 : F = 0 := eq_zero_of_kron_right_entry_ne_zero F A iA jA hAij hFA
        exfalso
        apply hW11nz
        simp [hF0, hH0, TwoControl.zero_kron_left]
      · have hF0_or : F = 0 ∨ F ≠ 0 := em (F = 0)
        cases hF0_or with
        | inl hF0 =>
            have hHB : H ⊗ₖ B = 0 := by simpa [hF0, TwoControl.zero_kron_left, zero_add] using hOff
            rcases exists_nonzero_entry_of_ne_zero B hB0 with ⟨iB, jB, hBij⟩
            have hH0' : H = 0 := eq_zero_of_kron_right_entry_ne_zero H B iB jB hBij hHB
            exfalso
            exact hH0 hH0'
        | inr hF0 =>
            rcases scalar_of_kron_sum_zero A B F H hA0 hH0 hOff with ⟨c, hB, hF⟩
            refine ⟨E + c • G, A, H, D - c • C, ?_, ?_⟩
            · calc
                E ⊗ₖ A + G ⊗ₖ B = E ⊗ₖ A + G ⊗ₖ (c • A) := by rw [hB]
                _ = E ⊗ₖ A + (c • G) ⊗ₖ A := by rw [kron_smul_right, kron_smul_left]
                _ = (E + c • G) ⊗ₖ A := by rw [kron_add_left]
            · calc
                F ⊗ₖ C + H ⊗ₖ D = ((-c) • H) ⊗ₖ C + H ⊗ₖ D := by rw [hF]
                _ = H ⊗ₖ ((-c) • C) + H ⊗ₖ D := by rw [kron_smul_left, kron_smul_right]
                _ = H ⊗ₖ (((-c) • C) + D) := by rw [← kron_add_right]
                _ = H ⊗ₖ (D - c • C) := by simp [sub_eq_add_neg, add_comm]

private lemma controlledGate_unitary (P : Square 2)
    (hP : P ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    controlledGate P ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  apply (blockify_mem_unitaryGroup_iff (n := 2) (U := controlledGate P)).1
  unfold controlledGate
  rw [blockify_add, blockify_proj0_kron, blockify_proj1_kron]
  have hBlocks : Matrix.fromBlocks (1 : Square 2) 0 0 P ∈ Matrix.unitaryGroup (Fin 2 ⊕ Fin 2) ℂ :=
    fromBlocks_diagonal_unitary (1 : Square 2) P (Submonoid.one_mem _) hP
  simpa [Matrix.fromBlocks_add] using hBlocks

private lemma unitary_factors_of_kron_unitary (X A : Square 2)
    (h : X ⊗ₖ A ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ P Q : Square 2,
      P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      P ⊗ₖ Q = X ⊗ₖ A := by
  let XX : Square 2 := X† * X
  let AA : Square 2 := A† * A
  have hProd : XX ⊗ₖ AA = (1 : Square 4) := by
    dsimp [XX, AA]
    calc
      (X† * X) ⊗ₖ (A† * A) = (X† ⊗ₖ A†) * (X ⊗ₖ A) := by rw [kron_mul_two]
      _ = star (X ⊗ₖ A) * (X ⊗ₖ A) := by rw [Matrix.star_eq_conjTranspose, conjTranspose_kron_two]
      _ = 1 := Matrix.mem_unitaryGroup_iff'.mp h
  let r2 : ℝ := Complex.normSq (X 0 0) + Complex.normSq (X 1 0)
  let s2 : ℝ := Complex.normSq (A 0 0) + Complex.normSq (A 1 0)
  have hXX00 : XX 0 0 = (r2 : ℂ) := by
    dsimp [XX, r2]
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Complex.normSq_eq_conj_mul_self]
  have hAA00 : AA 0 0 = (s2 : ℂ) := by
    dsimp [AA, s2]
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Complex.normSq_eq_conj_mul_self]
  have h00 : XX 0 0 * AA 0 0 = 1 := by
    have hEntry := congrFun (congrFun hProd (@finProdFinEquiv 2 2 (0, 0))) (@finProdFinEquiv 2 2 (0, 0))
    simpa [TwoControl.kron_apply] using hEntry
  have hrs : (r2 : ℂ) * (s2 : ℂ) = 1 := by simpa [hXX00, hAA00] using h00
  have hs00_ne : AA 0 0 ≠ 0 := by
    intro hZero
    simp [hZero] at h00
  have hx00_ne : XX 0 0 ≠ 0 := by
    intro hZero
    simp [hZero] at h00
  have hXX01 : XX 0 1 = 0 := by
    have hEntry := congrFun (congrFun hProd (@finProdFinEquiv 2 2 (0, 0))) (@finProdFinEquiv 2 2 (1, 0))
    have hMul : XX 0 1 * AA 0 0 = 0 := by
      rw [show (XX ⊗ₖ AA) (@finProdFinEquiv 2 2 (0, 0)) (@finProdFinEquiv 2 2 (1, 0)) = XX 0 1 * AA 0 0 by
        simpa using (TwoControl.kron_apply (A := XX) (B := AA) 0 0 1 0)] at hEntry
      simpa using hEntry
    exact (mul_eq_zero.mp hMul).resolve_right hs00_ne
  have hXX10 : XX 1 0 = 0 := by
    have hEntry := congrFun (congrFun hProd (@finProdFinEquiv 2 2 (1, 0))) (@finProdFinEquiv 2 2 (0, 0))
    have hMul : XX 1 0 * AA 0 0 = 0 := by
      rw [show (XX ⊗ₖ AA) (@finProdFinEquiv 2 2 (1, 0)) (@finProdFinEquiv 2 2 (0, 0)) = XX 1 0 * AA 0 0 by
        simpa using (TwoControl.kron_apply (A := XX) (B := AA) 1 0 0 0)] at hEntry
      simpa using hEntry
    exact (mul_eq_zero.mp hMul).resolve_right hs00_ne
  have hXX11 : XX 1 1 = (r2 : ℂ) := by
    have hEntry : XX 1 1 * AA 0 0 = 1 := by
      have hRaw := congrFun (congrFun hProd (@finProdFinEquiv 2 2 (1, 0))) (@finProdFinEquiv 2 2 (1, 0))
      simpa [TwoControl.kron_apply] using hRaw
    apply mul_right_cancel₀ hs00_ne
    calc
      XX 1 1 * AA 0 0 = 1 := hEntry
      _ = (r2 : ℂ) * AA 0 0 := by rw [← h00, hXX00]
  have hAA11 : AA 1 1 = (s2 : ℂ) := by
    have hEntry : XX 0 0 * AA 1 1 = 1 := by
      have hRaw := congrFun (congrFun hProd (@finProdFinEquiv 2 2 (0, 1))) (@finProdFinEquiv 2 2 (0, 1))
      simpa [TwoControl.kron_apply] using hRaw
    apply mul_left_cancel₀ hx00_ne
    calc
      XX 0 0 * AA 1 1 = 1 := hEntry
      _ = XX 0 0 * (s2 : ℂ) := by rw [← h00, hAA00]
  have hAA01 : AA 0 1 = 0 := by
    have hEntry := congrFun (congrFun hProd (@finProdFinEquiv 2 2 (0, 0))) (@finProdFinEquiv 2 2 (0, 1))
    have hMul : XX 0 0 * AA 0 1 = 0 := by
      rw [show (XX ⊗ₖ AA) (@finProdFinEquiv 2 2 (0, 0)) (@finProdFinEquiv 2 2 (0, 1)) = XX 0 0 * AA 0 1 by
        simpa using (TwoControl.kron_apply (A := XX) (B := AA) 0 0 0 1)] at hEntry
      simpa using hEntry
    exact (mul_eq_zero.mp hMul).resolve_left hx00_ne
  have hAA10 : AA 1 0 = 0 := by
    have hEntry := congrFun (congrFun hProd (@finProdFinEquiv 2 2 (0, 1))) (@finProdFinEquiv 2 2 (0, 0))
    have hMul : XX 0 0 * AA 1 0 = 0 := by
      rw [show (XX ⊗ₖ AA) (@finProdFinEquiv 2 2 (0, 1)) (@finProdFinEquiv 2 2 (0, 0)) = XX 0 0 * AA 1 0 by
        simpa using (TwoControl.kron_apply (A := XX) (B := AA) 0 1 0 0)] at hEntry
      simpa using hEntry
    exact (mul_eq_zero.mp hMul).resolve_left hx00_ne
  have hXX : XX = (r2 : ℂ) • (1 : Square 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hXX00, hXX01, hXX10, hXX11]
  have hAA : AA = (s2 : ℂ) • (1 : Square 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hAA00, hAA01, hAA10, hAA11]
  have hr2_nonneg : 0 ≤ r2 := by
    dsimp [r2]
    simpa [Complex.normSq_eq_norm_sq] using add_nonneg (sq_nonneg ‖X 0 0‖) (sq_nonneg ‖X 1 0‖)
  have hr2_ne : r2 ≠ 0 := by
    intro hr0
    simp [hr0] at hrs
  have hr2_pos : 0 < r2 := lt_of_le_of_ne hr2_nonneg (by simpa using hr2_ne.symm)
  let t : ℝ := Real.sqrt r2
  have ht_sq_real : t ^ 2 = r2 := by
    dsimp [t]
    exact Real.sq_sqrt hr2_nonneg
  have ht_sq : ((t : ℂ) * (t : ℂ)) = (r2 : ℂ) := by
    have hcast : ((t : ℂ) ^ 2) = (r2 : ℂ) := by exact_mod_cast ht_sq_real
    simpa [pow_two] using hcast
  have ht_ne : (t : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hr2_pos).ne'
  have ht0 : t ≠ 0 := by
    exact_mod_cast ht_ne
  let P : Square 2 := ((t : ℂ)⁻¹) • X
  let Q : Square 2 := (t : ℂ) • A
  have hCoeffP : (((t : ℂ)⁻¹ * (t : ℂ)⁻¹) * (r2 : ℂ)) = 1 := by
    rw [← ht_sq]
    field_simp [ht_ne]
  have hPmul : P† * P = (1 : Square 2) := by
    dsimp [P]
    calc
      ((((t : ℂ)⁻¹) • X)† * (((t : ℂ)⁻¹) • X))
          = (((t : ℂ)⁻¹ * (t : ℂ)⁻¹) : ℂ) • (X† * X) := by
              rw [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
              simp
      _ = ((((t : ℂ)⁻¹ * (t : ℂ)⁻¹) : ℂ) * (r2 : ℂ)) • (1 : Square 2) := by
              rw [show X† * X = (r2 : ℂ) • (1 : Square 2) by simpa [XX] using hXX, smul_smul]
      _ = 1 := by
              ext i j
              fin_cases i <;> fin_cases j <;> simp [hCoeffP]
  have hP : P ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    simpa [Matrix.mem_unitaryGroup_iff'] using hPmul
  have hCoeffQ : (((t : ℂ) * (t : ℂ)) * (s2 : ℂ)) = 1 := by
    rw [ht_sq]
    exact hrs
  have hQmul : Q† * Q = (1 : Square 2) := by
    dsimp [Q]
    calc
      (((t : ℂ) • A)† * ((t : ℂ) • A))
          = (((t : ℂ) * (t : ℂ)) : ℂ) • (A† * A) := by
              rw [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
              simp
      _ = ((((t : ℂ) * (t : ℂ)) : ℂ) * (s2 : ℂ)) • (1 : Square 2) := by
              rw [show A† * A = (s2 : ℂ) • (1 : Square 2) by simpa [AA] using hAA, smul_smul]
      _ = 1 := by
              ext i j
              fin_cases i <;> fin_cases j <;> simp [hCoeffQ]
  have hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    simpa [Matrix.mem_unitaryGroup_iff'] using hQmul
  refine ⟨P, Q, hP, hQ, ?_⟩
  dsimp [P, Q]
  calc
    (((t : ℂ)⁻¹) • X) ⊗ₖ ((t : ℂ) • A)
        = ((t : ℂ)⁻¹) • (X ⊗ₖ ((t : ℂ) • A)) := by rw [kron_smul_left]
    _ = ((t : ℂ)⁻¹) • ((t : ℂ) • (X ⊗ₖ A)) := by rw [kron_smul_right]
    _ = (((t : ℂ)⁻¹) * (t : ℂ)) • (X ⊗ₖ A) := by rw [smul_smul]
    _ = X ⊗ₖ A := by
        have hCoeff : ((t : ℂ)⁻¹) * (t : ℂ) = 1 := by
          field_simp [ht_ne]
        simp [hCoeff]

private lemma unit_vector_extends_to_unitary (β : Vec 2) (hβ : star β ⬝ᵥ β = 1) :
    ∃ Q : Square 2,
      Q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ Q.mulVec ket0 = β := by
  let βperp : Vec 2 := ![- star (β 1), star (β 0)]
  let Q : Square 2 := fun i j => if j = 0 then β i else βperp i
  have hβperp_norm : star βperp ⬝ᵥ βperp = 1 := by
    simp [βperp, dotProduct]
    simpa [add_comm, mul_comm] using hβ
  have hβperp_orth : star βperp ⬝ᵥ β = 0 := by
    simp [βperp, dotProduct]
    ring_nf
  have hβ_orth_perp : star β ⬝ᵥ βperp = 0 := by
    simp [βperp, dotProduct]
    ring_nf
  have hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Q, Matrix.mul_apply, Fin.sum_univ_succ] using hβ
    · simp [Q, βperp, Matrix.mul_apply, Fin.sum_univ_succ]
      ring
    · simp [Q, βperp, Matrix.mul_apply, Fin.sum_univ_succ]
      ring
    · simp [Q, βperp, Matrix.mul_apply, Fin.sum_univ_succ]
      simpa [βperp, dotProduct, add_comm, mul_comm] using hβperp_norm
  refine ⟨Q, hQ, ?_⟩
  ext i
  rw [show ket0 = Pi.single 0 1 by
    ext j
    fin_cases j <;> simp [ket0]]
  rw [Matrix.mulVec_single_one]
  simp [Q]

private lemma diag2_one_right_kron (u : ℂ) :
    diag2 1 u ⊗ₖ (1 : Square 2) = diag4 1 1 u u := by
  rw [← diag2_one_one]
  simpa using diag2_kron_diag2 1 u 1 1

private def notc : Square 4 :=
  Matrix.of ![![1, 0, 0, 0],
              ![0, 0, 0, 1],
              ![0, 0, 1, 0],
              ![0, 1, 0, 0]]

private lemma notc_conjTranspose : notc† = notc := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [notc]

private lemma notc_mul_notc : notc * notc = (1 : Square 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [notc]

private lemma notc_unitary : notc ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, show star notc = notc by
    simpa [Matrix.star_eq_conjTranspose] using notc_conjTranspose, notc_mul_notc]

private lemma diag4_unitary (a b c d : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
    diag4 a b c d ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag4, Complex.conj_mul', ha, hb, hc, hd]

private lemma notc_conj_diag4 (a b c d : ℂ) :
    notc * diag4 a b c d * notc† = diag4 a d c b := by
  rw [notc_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ, notc, diag4]

private lemma eq_witness_of_eq (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ (U₁ U₂ U₃ U₄ : Square 4),
      U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      bcgate U₁ * acgate U₂ * abgate U₃ * bcgate U₄ = ccu (diag2 u u) := by
  refine ⟨1, 1, controlledGate (diag2 1 u), 1, Submonoid.one_mem _, Submonoid.one_mem _, ?_,
    Submonoid.one_mem _, ?_⟩
  · exact controlledGate_unitary (diag2 1 u) (diag2_unitary 1 u (by simp) hu)
  · apply (blockify_injective (n := 4))
    have hOneBlock : blockify (n := 2) (1 : Square 4) = Matrix.fromBlocks (1 : Square 2) 0 0 (1 : Square 2) := by
      rw [show blockify (n := 2) (1 : Square 4) = (1 : BlockMatrix 2) by simp]
      exact block_one_eq 2
    have hOne11 : (blockify (n := 2) (1 : Square 4)).toBlocks₁₁ = (1 : Square 2) := by
      exact congrArg Matrix.toBlocks₁₁ hOneBlock
    have hOne12 : (blockify (n := 2) (1 : Square 4)).toBlocks₁₂ = 0 := by
      exact congrArg Matrix.toBlocks₁₂ hOneBlock
    have hOne21 : (blockify (n := 2) (1 : Square 4)).toBlocks₂₁ = 0 := by
      exact congrArg Matrix.toBlocks₂₁ hOneBlock
    have hOne22 : (blockify (n := 2) (1 : Square 4)).toBlocks₂₂ = (1 : Square 2) := by
      exact congrArg Matrix.toBlocks₂₂ hOneBlock
    have hCtrlBlock : blockify (n := 2) (controlledGate (diag2 1 u)) =
        Matrix.fromBlocks (1 : Square 2) 0 0 (diag2 1 u) := by
      simpa using blockify_controlledGate (diag2 1 u)
    have hCtrl11 : (blockify (n := 2) (controlledGate (diag2 1 u))).toBlocks₁₁ = (1 : Square 2) := by
      simpa using congrArg Matrix.toBlocks₁₁ hCtrlBlock
    have hCtrl12 : (blockify (n := 2) (controlledGate (diag2 1 u))).toBlocks₁₂ = 0 := by
      simpa using congrArg Matrix.toBlocks₁₂ hCtrlBlock
    have hCtrl21 : (blockify (n := 2) (controlledGate (diag2 1 u))).toBlocks₂₁ = 0 := by
      simpa using congrArg Matrix.toBlocks₂₁ hCtrlBlock
    have hCtrl22 : (blockify (n := 2) (controlledGate (diag2 1 u))).toBlocks₂₂ = diag2 1 u := by
      simpa using congrArg Matrix.toBlocks₂₂ hCtrlBlock
    have hBc1 : blockify (n := 4) (bcgate (1 : Square 4)) = Matrix.fromBlocks (1 : Square 4) 0 0 (1 : Square 4) := by
      simpa using blockify_bcgate (1 : Square 4)
    have hAc1 : blockify (n := 4) (acgate (1 : Square 4)) = Matrix.fromBlocks (1 : Square 4) 0 0 (1 : Square 4) := by
      rw [blockify_acgate, hOne11, hOne12, hOne21, hOne22]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [TwoControl.one_kron_one, TwoControl.zero_kron_right]
    have hAbCtrl : blockify (n := 4) (abgate (controlledGate (diag2 1 u))) =
        Matrix.fromBlocks (1 : Square 4) 0 0 (diag2 1 u ⊗ₖ (1 : Square 2)) := by
      rw [blockify_abgate, hCtrl11, hCtrl12, hCtrl21, hCtrl22]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [TwoControl.one_kron_one, TwoControl.zero_kron_left]
    calc
      blockify (n := 4)
          (bcgate (1 : Square 4) * acgate (1 : Square 4) * abgate (controlledGate (diag2 1 u)) *
            bcgate (1 : Square 4))
          = Matrix.fromBlocks (1 : Square 4) 0 0 (diag2 1 u ⊗ₖ (1 : Square 2)) := by
              rw [blockify_mul, blockify_mul, blockify_mul]
              rw [hAc1, hAbCtrl]
              rw [hBc1]
              rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
              simp
      _ = Matrix.fromBlocks (1 : Square 4) 0 0 (controlledGate (diag2 u u)) := by
            rw [controlledGate_diag2_eq, diag2_one_right_kron]
      _ = blockify (n := 4) (ccu (diag2 u u)) := by
            symm
            rw [ccu, blockify_add, blockify_proj0_kron, blockify_proj1_kron]
            simp [Matrix.fromBlocks_add]

private lemma prod_one_witness
    (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) (h : u₀ * u₁ = 1) :
    ∃ (U₁ U₂ U₃ U₄ : Square 4),
      U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      bcgate U₁ * acgate U₂ * abgate U₃ * bcgate U₄ = ccu (diag2 u₀ u₁) := by
  let U₂ : Square 4 := proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ diag2 1 u₁
  let U₃ : Square 4 := proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ diag2 1 u₀
  refine ⟨notc, U₂, U₃, notc, notc_unitary, ?_, ?_, notc_unitary, ?_⟩
  · exact controlledGate_unitary (diag2 1 u₁) (diag2_unitary 1 u₁ (by simp) hu₁)
  · exact controlledGate_unitary (diag2 1 u₀) (diag2_unitary 1 u₀ (by simp) hu₀)
  · apply (blockify_injective (n := 4))
    have hU₂block : blockify (n := 2) U₂ = Matrix.fromBlocks (1 : Square 2) 0 0 (diag2 1 u₁) := by
      unfold U₂
      simpa using blockify_controlledGate (diag2 1 u₁)
    have hU₃block : blockify (n := 2) U₃ = Matrix.fromBlocks (1 : Square 2) 0 0 (diag2 1 u₀) := by
      unfold U₃
      simpa using blockify_controlledGate (diag2 1 u₀)
    have hU₂11 : (blockify (n := 2) U₂).toBlocks₁₁ = (1 : Square 2) := by
      simpa using congrArg Matrix.toBlocks₁₁ hU₂block
    have hU₂12 : (blockify (n := 2) U₂).toBlocks₁₂ = 0 := by
      simpa using congrArg Matrix.toBlocks₁₂ hU₂block
    have hU₂21 : (blockify (n := 2) U₂).toBlocks₂₁ = 0 := by
      simpa using congrArg Matrix.toBlocks₂₁ hU₂block
    have hU₂22 : (blockify (n := 2) U₂).toBlocks₂₂ = diag2 1 u₁ := by
      simpa using congrArg Matrix.toBlocks₂₂ hU₂block
    have hU₃11 : (blockify (n := 2) U₃).toBlocks₁₁ = (1 : Square 2) := by
      simpa using congrArg Matrix.toBlocks₁₁ hU₃block
    have hU₃12 : (blockify (n := 2) U₃).toBlocks₁₂ = 0 := by
      simpa using congrArg Matrix.toBlocks₁₂ hU₃block
    have hU₃21 : (blockify (n := 2) U₃).toBlocks₂₁ = 0 := by
      simpa using congrArg Matrix.toBlocks₂₁ hU₃block
    have hU₃22 : (blockify (n := 2) U₃).toBlocks₂₂ = diag2 1 u₀ := by
      simpa using congrArg Matrix.toBlocks₂₂ hU₃block
    have hAcU₂ : blockify (n := 4) (acgate U₂) =
        Matrix.fromBlocks (1 : Square 4) 0 0 ((1 : Square 2) ⊗ₖ diag2 1 u₁) := by
      rw [blockify_acgate, hU₂11, hU₂12, hU₂21, hU₂22]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [TwoControl.one_kron_one, TwoControl.zero_kron_right]
    have hAbU₃ : blockify (n := 4) (abgate U₃) =
        Matrix.fromBlocks (1 : Square 4) 0 0 (diag2 1 u₀ ⊗ₖ (1 : Square 2)) := by
      rw [blockify_abgate, hU₃11, hU₃12, hU₃21, hU₃22]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [TwoControl.one_kron_one, TwoControl.zero_kron_left]
    have hBcNotc : blockify (n := 4) (bcgate notc) = Matrix.fromBlocks notc 0 0 notc := by
      simpa using blockify_bcgate notc
    have hMid : blockify (n := 4) (acgate U₂ * abgate U₃) =
        Matrix.fromBlocks (1 : Square 4) 0 0 (diag4 1 u₁ u₀ 1) := by
      rw [blockify_mul, hAcU₂, hAbU₃, Matrix.fromBlocks_multiply]
      refine Matrix.fromBlocks_inj.2 ?_
      constructor
      · simp
      constructor
      · simp
      constructor
      · simp
      · have hDiag :
            (1 : Square 2) ⊗ₖ diag2 1 u₁ * (diag2 1 u₀ ⊗ₖ (1 : Square 2)) = diag4 1 u₁ u₀ 1 := by
            calc
              (1 : Square 2) ⊗ₖ diag2 1 u₁ * (diag2 1 u₀ ⊗ₖ (1 : Square 2))
                  = ((1 : Square 2) * diag2 1 u₀) ⊗ₖ (diag2 1 u₁ * (1 : Square 2)) := by
                      rw [← kron_mul_reindex_local (1 : Square 2) (diag2 1 u₀) (diag2 1 u₁)
                        (1 : Square 2)]
              _ = diag4 1 u₁ u₀ 1 := by
                    simp [diag2_kron_diag2, h]
        simpa [TwoControl.zero_kron_left, TwoControl.zero_kron_right] using hDiag
    calc
      blockify (n := 4) (bcgate notc * acgate U₂ * abgate U₃ * bcgate notc)
          = blockify (n := 4) (bcgate notc * (acgate U₂ * abgate U₃) * bcgate notc) := by
              simp [mul_assoc]
      _
          = Matrix.fromBlocks (1 : Square 4) 0 0 (diag4 1 1 u₀ u₁) := by
              rw [blockify_mul, blockify_mul]
              rw [hBcNotc, hMid]
              rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
              simp [notc_mul_notc, mul_assoc]
              simpa [notc_conjTranspose, mul_assoc] using notc_conj_diag4 1 u₁ u₀ 1
      _ = blockify (n := 4) (ccu (diag2 u₀ u₁)) := by
            symm
            rw [ccu, blockify_add, blockify_proj0_kron, blockify_proj1_kron, controlledGate_diag2_eq]
            simp [Matrix.fromBlocks_add]

/-- **Lemma 5.1** (The first main lemma).
    Suppose `u₀, u₁` are complex numbers with `‖u₀‖ = 1` and `‖u₁‖ = 1`.
    There exist 2-qubit unitaries `U₁, U₂, U₃, U₄` such that
    `U₁^{BC} U₂^{AC} U₃^{AB} U₄^{BC} = CC(Diag(u₀, u₁))`
    if and only if either `u₀ = u₁` or `u₀ * u₁ = 1`. -/
lemma section5_lemma_5_1 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (U₁ U₂ U₃ U₄ : Square 4),
      U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      bcgate U₁ * acgate U₂ * abgate U₃ * bcgate U₄ = ccu (diag2 u₀ u₁))
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by
  constructor
  · rintro ⟨U₁, U₂, U₃, U₄, hU₁, hU₂, hU₃, hU₄, hEq⟩
    let U2b : BlockMatrix 2 := blockify (n := 2) U₂
    let U3b : BlockMatrix 2 := blockify (n := 2) U₃
    let A2 : Square 2 := U2b.toBlocks₁₁
    let B2 : Square 2 := U2b.toBlocks₁₂
    let C2 : Square 2 := U2b.toBlocks₂₁
    let D2 : Square 2 := U2b.toBlocks₂₂
    let E3 : Square 2 := U3b.toBlocks₁₁
    let F3 : Square 2 := U3b.toBlocks₁₂
    let G3 : Square 2 := U3b.toBlocks₂₁
    let H3 : Square 2 := U3b.toBlocks₂₂
    let W00 : Square 4 := E3 ⊗ₖ A2 + G3 ⊗ₖ B2
    let W01 : Square 4 := F3 ⊗ₖ A2 + H3 ⊗ₖ B2
    let W10 : Square 4 := E3 ⊗ₖ C2 + G3 ⊗ₖ D2
    let W11 : Square 4 := F3 ⊗ₖ C2 + H3 ⊗ₖ D2
    have hMidBlocks :
        blockify (n := 4) (acgate U₂ * abgate U₃) =
          Matrix.fromBlocks W00 W01 W10 W11 := by
      dsimp [W00, W01, W10, W11, A2, B2, C2, D2, E3, F3, G3, H3, U2b, U3b]
      rw [blockify_mul, blockify_acgate, blockify_abgate, Matrix.fromBlocks_multiply]
      refine Matrix.fromBlocks_inj.2 ?_
      constructor
      · calc
          (1 : Square 2) ⊗ₖ Matrix.toBlocks₁₁ (blockify (n := 2) U₂) *
              (Matrix.toBlocks₁₁ (blockify (n := 2) U₃) ⊗ₖ (1 : Square 2)) +
            (1 : Square 2) ⊗ₖ Matrix.toBlocks₁₂ (blockify (n := 2) U₂) *
              (Matrix.toBlocks₂₁ (blockify (n := 2) U₃) ⊗ₖ (1 : Square 2))
              = ((1 : Square 2) * Matrix.toBlocks₁₁ (blockify (n := 2) U₃)) ⊗ₖ
                  (Matrix.toBlocks₁₁ (blockify (n := 2) U₂) * (1 : Square 2)) +
                ((1 : Square 2) * Matrix.toBlocks₂₁ (blockify (n := 2) U₃)) ⊗ₖ
                  (Matrix.toBlocks₁₂ (blockify (n := 2) U₂) * (1 : Square 2)) := by
                    rw [← kron_mul_reindex_local (1 : Square 2)
                      (Matrix.toBlocks₁₁ (blockify (n := 2) U₃))
                      (Matrix.toBlocks₁₁ (blockify (n := 2) U₂)) (1 : Square 2),
                      ← kron_mul_reindex_local (1 : Square 2)
                      (Matrix.toBlocks₂₁ (blockify (n := 2) U₃))
                      (Matrix.toBlocks₁₂ (blockify (n := 2) U₂)) (1 : Square 2)]
          _ = _ := by simp
      constructor
      · calc
          (1 : Square 2) ⊗ₖ Matrix.toBlocks₁₁ (blockify (n := 2) U₂) *
              (Matrix.toBlocks₁₂ (blockify (n := 2) U₃) ⊗ₖ (1 : Square 2)) +
            (1 : Square 2) ⊗ₖ Matrix.toBlocks₁₂ (blockify (n := 2) U₂) *
              (Matrix.toBlocks₂₂ (blockify (n := 2) U₃) ⊗ₖ (1 : Square 2))
              = ((1 : Square 2) * Matrix.toBlocks₁₂ (blockify (n := 2) U₃)) ⊗ₖ
                  (Matrix.toBlocks₁₁ (blockify (n := 2) U₂) * (1 : Square 2)) +
                ((1 : Square 2) * Matrix.toBlocks₂₂ (blockify (n := 2) U₃)) ⊗ₖ
                  (Matrix.toBlocks₁₂ (blockify (n := 2) U₂) * (1 : Square 2)) := by
                    rw [← kron_mul_reindex_local (1 : Square 2)
                      (Matrix.toBlocks₁₂ (blockify (n := 2) U₃))
                      (Matrix.toBlocks₁₁ (blockify (n := 2) U₂)) (1 : Square 2),
                      ← kron_mul_reindex_local (1 : Square 2)
                      (Matrix.toBlocks₂₂ (blockify (n := 2) U₃))
                      (Matrix.toBlocks₁₂ (blockify (n := 2) U₂)) (1 : Square 2)]
          _ = _ := by simp
      constructor
      · calc
          (1 : Square 2) ⊗ₖ Matrix.toBlocks₂₁ (blockify (n := 2) U₂) *
              (Matrix.toBlocks₁₁ (blockify (n := 2) U₃) ⊗ₖ (1 : Square 2)) +
            (1 : Square 2) ⊗ₖ Matrix.toBlocks₂₂ (blockify (n := 2) U₂) *
              (Matrix.toBlocks₂₁ (blockify (n := 2) U₃) ⊗ₖ (1 : Square 2))
              = ((1 : Square 2) * Matrix.toBlocks₁₁ (blockify (n := 2) U₃)) ⊗ₖ
                  (Matrix.toBlocks₂₁ (blockify (n := 2) U₂) * (1 : Square 2)) +
                ((1 : Square 2) * Matrix.toBlocks₂₁ (blockify (n := 2) U₃)) ⊗ₖ
                  (Matrix.toBlocks₂₂ (blockify (n := 2) U₂) * (1 : Square 2)) := by
                    rw [← kron_mul_reindex_local (1 : Square 2)
                      (Matrix.toBlocks₁₁ (blockify (n := 2) U₃))
                      (Matrix.toBlocks₂₁ (blockify (n := 2) U₂)) (1 : Square 2),
                      ← kron_mul_reindex_local (1 : Square 2)
                      (Matrix.toBlocks₂₁ (blockify (n := 2) U₃))
                      (Matrix.toBlocks₂₂ (blockify (n := 2) U₂)) (1 : Square 2)]
          _ = _ := by simp
      · calc
          (1 : Square 2) ⊗ₖ Matrix.toBlocks₂₁ (blockify (n := 2) U₂) *
              (Matrix.toBlocks₁₂ (blockify (n := 2) U₃) ⊗ₖ (1 : Square 2)) +
            (1 : Square 2) ⊗ₖ Matrix.toBlocks₂₂ (blockify (n := 2) U₂) *
              (Matrix.toBlocks₂₂ (blockify (n := 2) U₃) ⊗ₖ (1 : Square 2))
              = ((1 : Square 2) * Matrix.toBlocks₁₂ (blockify (n := 2) U₃)) ⊗ₖ
                  (Matrix.toBlocks₂₁ (blockify (n := 2) U₂) * (1 : Square 2)) +
                ((1 : Square 2) * Matrix.toBlocks₂₂ (blockify (n := 2) U₃)) ⊗ₖ
                  (Matrix.toBlocks₂₂ (blockify (n := 2) U₂) * (1 : Square 2)) := by
                    rw [← kron_mul_reindex_local (1 : Square 2)
                      (Matrix.toBlocks₁₂ (blockify (n := 2) U₃))
                      (Matrix.toBlocks₂₁ (blockify (n := 2) U₂)) (1 : Square 2),
                      ← kron_mul_reindex_local (1 : Square 2)
                      (Matrix.toBlocks₂₂ (blockify (n := 2) U₃))
                      (Matrix.toBlocks₂₂ (blockify (n := 2) U₂)) (1 : Square 2)]
          _ = _ := by simp
    have hEq' : bcgate U₁ * (acgate U₂ * abgate U₃) * bcgate U₄ = ccu (diag2 u₀ u₁) := by
      simpa [mul_assoc] using hEq
    have hRhsBlocks :
        blockify (n := 4) (ccu (diag2 u₀ u₁)) =
          Matrix.fromBlocks (1 : Square 4) 0 0 (controlledGate (diag2 u₀ u₁)) := by
      rw [ccu, blockify_add, blockify_proj0_kron, blockify_proj1_kron]
      simp [Matrix.fromBlocks_add]
    have hBlocks :
        Matrix.fromBlocks (U₁ * W00 * U₄) (U₁ * W01 * U₄) (U₁ * W10 * U₄) (U₁ * W11 * U₄) =
          Matrix.fromBlocks (1 : Square 4) 0 0 (controlledGate (diag2 u₀ u₁)) := by
      calc
        Matrix.fromBlocks (U₁ * W00 * U₄) (U₁ * W01 * U₄) (U₁ * W10 * U₄) (U₁ * W11 * U₄)
            = blockify (n := 4) (bcgate U₁ * (acgate U₂ * abgate U₃) * bcgate U₄) := by
                rw [blockify_mul, blockify_mul, blockify_bcgate, hMidBlocks, blockify_bcgate,
                  Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
                simp [mul_assoc]
        _ = blockify (n := 4) (ccu (diag2 u₀ u₁)) := by
              simpa using congrArg (blockify (n := 4)) hEq'
        _ = Matrix.fromBlocks (1 : Square 4) 0 0 (controlledGate (diag2 u₀ u₁)) := hRhsBlocks
    rcases Matrix.fromBlocks_inj.mp hBlocks with ⟨h00, h01, h10, h11⟩
    have hW01_zero : W01 = 0 := by
      have h01' : U₁ * (W01 * U₄) = 0 := by simpa [mul_assoc] using h01
      have h01'' : W01 * U₄ = 0 := mul_eq_zero_of_unitary_left hU₁ h01'
      exact mul_eq_zero_of_unitary_right hU₄ h01''
    have hU₁left : U₁† * U₁ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hU₁)
    have hU₄right : U₄ * U₄† = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hU₄)
    have hCtrl : controlledGate (diag2 u₀ u₁) ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
      controlledGate_unitary (diag2 u₀ u₁) (diag2_unitary u₀ u₁ hu₀ hu₁)
    have hW00_eq : W00 = U₁† * U₄† := by
      calc
        W00 = (U₁† * U₁) * W00 * (U₄ * U₄†) := by
          rw [hU₁left, hU₄right]
          simp
        _ = U₁† * (U₁ * W00 * U₄) * U₄† := by simp [mul_assoc]
        _ = U₁† * U₄† := by rw [h00]; simp
    have hW11_eq : W11 = U₁† * controlledGate (diag2 u₀ u₁) * U₄† := by
      calc
        W11 = (U₁† * U₁) * W11 * (U₄ * U₄†) := by
          rw [hU₁left, hU₄right]
          simp
        _ = U₁† * (U₁ * W11 * U₄) * U₄† := by simp [mul_assoc]
        _ = U₁† * controlledGate (diag2 u₀ u₁) * U₄† := by rw [h11]
    have hW00_unitary : W00 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
      rw [hW00_eq]
      exact Submonoid.mul_mem _ (conjTranspose_mem_unitaryGroup hU₁)
        (conjTranspose_mem_unitaryGroup hU₄)
    have hW11_unitary : W11 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
      rw [hW11_eq]
      exact Submonoid.mul_mem _
        (Submonoid.mul_mem _ (conjTranspose_mem_unitaryGroup hU₁) hCtrl)
        (conjTranspose_mem_unitaryGroup hU₄)
    rcases tensor_decomp_of_offdiag_zero E3 F3 G3 H3 A2 B2 C2 D2 hW01_zero hW00_unitary
      hW11_unitary with
      ⟨X₀, Y₀, X₁, Y₁, hW00_tensor, hW11_tensor⟩
    have hX₀Y₀_unitary : X₀ ⊗ₖ Y₀ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
      rw [← hW00_tensor]
      exact hW00_unitary
    have hX₁Y₁_unitary : X₁ ⊗ₖ Y₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
      rw [← hW11_tensor]
      exact hW11_unitary
    rcases unitary_factors_of_kron_unitary X₀ Y₀ hX₀Y₀_unitary with
      ⟨P₀, Q₀, hP₀, hQ₀, hP₀Q₀⟩
    rcases unitary_factors_of_kron_unitary X₁ Y₁ hX₁Y₁_unitary with
      ⟨P₁, Q₁, hP₁, hQ₁, hP₁Q₁⟩
    have hP₀Q₀W00 : P₀ ⊗ₖ Q₀ = W00 := by
      rw [hP₀Q₀, ← hW00_tensor]
    have hP₁Q₁W11 : P₁ ⊗ₖ Q₁ = W11 := by
      rw [hP₁Q₁, ← hW11_tensor]
    exact (section4_lemma_4_1 u₀ u₁ hu₀ hu₁).mp <| by
      refine ⟨U₁, U₄, P₀, P₁, Q₀, Q₁, hU₁, hU₄, hP₀, hP₁, hQ₀, hQ₁, ?_⟩
      apply (blockify_injective (n := 4))
      calc
        blockify (n := 4)
            (proj0 ⊗ₖ (U₁ * (P₀ ⊗ₖ Q₀) * U₄) + proj1 ⊗ₖ (U₁ * (P₁ ⊗ₖ Q₁) * U₄))
            = Matrix.fromBlocks (U₁ * (P₀ ⊗ₖ Q₀) * U₄) 0 0 (U₁ * (P₁ ⊗ₖ Q₁) * U₄) := by
                rw [blockify_add, blockify_proj0_kron, blockify_proj1_kron]
                simp [Matrix.fromBlocks_add]
        _ = Matrix.fromBlocks (U₁ * W00 * U₄) 0 0 (U₁ * W11 * U₄) := by
              rw [hP₀Q₀W00, hP₁Q₁W11]
        _ = Matrix.fromBlocks (1 : Square 4) 0 0 (controlledGate (diag2 u₀ u₁)) := by
              rw [h00, h11]
        _ = blockify (n := 4) (ccu (diag2 u₀ u₁)) := by
              symm
              exact hRhsBlocks
  · intro h
    rcases h with hEq | hProd
    · simpa [hEq] using (eq_witness_of_eq u₀ hu₀)
    · exact prod_one_witness u₀ u₁ hu₀ hu₁ hProd

end TwoControl

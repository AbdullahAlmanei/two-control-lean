import TwoControl.Section6

open scoped Matrix ComplexOrder
open Matrix

namespace TwoControl

private def diag8 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ℂ) : Square 8 :=
  Matrix.diagonal ![a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇]

@[simp] private lemma diag8_mul
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    diag8 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ * diag8 b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ =
      diag8 (a₀ * b₀) (a₁ * b₁) (a₂ * b₂) (a₃ * b₃)
        (a₄ * b₄) (a₅ * b₅) (a₆ * b₆) (a₇ * b₇) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag8, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma diag4_unitary (a b c d : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
    diag4 a b c d ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag4, Complex.conj_mul', ha, hb, hc, hd]

@[simp] private lemma abgate_mul (U W : Square 4) :
    abgate (U * W) = abgate U * abgate W := by
  unfold abgate
  simpa [TwoControl.kron, Matrix.reindexAlgEquiv_apply] using
    congrArg (Matrix.reindexAlgEquiv ℂ ℂ (@finProdFinEquiv 4 2))
      (Matrix.mul_kronecker_mul U W (1 : Square 2) (1 : Square 2))

private lemma ccu_diag2_eq (u₀ u₁ : ℂ) :
    ccu (diag2 u₀ u₁) = diag8 1 1 1 1 1 1 u₀ u₁ := by
  rw [ccu, controlledGate_diag2_eq]
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (@finProdFinEquiv 2 4).surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (@finProdFinEquiv 2 4).surjective j
  rw [Matrix.add_apply, TwoControl.kron_apply, TwoControl.kron_apply]
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [diag8, diag4, proj0, proj1, ketbra, ket0, ket1, finProdFinEquiv]

private lemma abgate_controlledGate_diag2_eq (u : ℂ) :
    abgate (controlledGate (diag2 1 u)) = diag8 1 1 1 1 1 1 u u := by
  rw [controlledGate_diag2_eq]
  unfold abgate
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (@finProdFinEquiv 4 2).surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (@finProdFinEquiv 4 2).surjective j
  rw [TwoControl.kron_apply]
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [diag4, diag8, finProdFinEquiv]

private lemma abgate_controlled_mul_ccu (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) :
    abgate (controlledGate (diag2 1 (starRingEnd ℂ u₀))) * ccu (diag2 u₀ u₁) =
      ccu (diag2 1 (starRingEnd ℂ u₀ * u₁)) := by
  have hu₀' : starRingEnd ℂ u₀ * u₀ = 1 := by
    simp [Complex.conj_mul', hu₀]
  rw [abgate_controlledGate_diag2_eq, ccu_diag2_eq, ccu_diag2_eq, diag8_mul]
  simp [hu₀']

/-- **Lemma 7.1** (Change a diagonal element to one.)
If `CC(Diag(u₀, u₁)) = W^{AB} · U` for a 2-qubit unitary `W` and a 3-qubit unitary `U`,
then there exists a 2-qubit unitary `V` such that `CC(Diag(1, u₀⋆ u₁)) = V^{AB} · U`. -/
lemma section7_lemma_7_1 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (_hu₁ : ‖u₁‖ = 1)
    (W : Square 4) (hW : W ∈ unitaryGroup (Fin 4) ℂ)
  (U : Square 8) (_hU : U ∈ unitaryGroup (Fin 8) ℂ)
    (h : ccu (diag2 u₀ u₁) = abgate W * U) :
    ∃ V : Square 4, V ∈ unitaryGroup (Fin 4) ℂ ∧
      ccu (diag2 1 (starRingEnd ℂ u₀ * u₁)) = abgate V * U := by
  let C : Square 4 := controlledGate (diag2 1 (starRingEnd ℂ u₀))
  let V : Square 4 := C * W
  have hC : C ∈ unitaryGroup (Fin 4) ℂ := by
    dsimp [C]
    rw [controlledGate_diag2_eq]
    exact diag4_unitary 1 1 1 (starRingEnd ℂ u₀) (by simp) (by simp) (by simp)
      (by simpa using hu₀)
  refine ⟨V, Submonoid.mul_mem _ hC hW, ?_⟩
  calc
    ccu (diag2 1 (starRingEnd ℂ u₀ * u₁))
        = abgate C * ccu (diag2 u₀ u₁) := by
            symm
            exact abgate_controlled_mul_ccu u₀ u₁ hu₀
    _ = abgate C * (abgate W * U) := by rw [h]
    _ = (abgate C * abgate W) * U := by simp [mul_assoc]
    _ = abgate (C * W) * U := by rw [← abgate_mul]
    _ = abgate V * U := by rfl

private lemma section7_lemma_7_1_left (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1)
    (W : Square 4) (hW : W ∈ unitaryGroup (Fin 4) ℂ)
    (U : Square 8)
    (h : ccu (diag2 u₀ u₁) = abgate W * U) :
    ∃ V : Square 4, V ∈ unitaryGroup (Fin 4) ℂ ∧
      ccu (diag2 1 (starRingEnd ℂ u₀ * u₁)) = abgate V * U := by
  let C : Square 4 := controlledGate (diag2 1 (starRingEnd ℂ u₀))
  let V : Square 4 := C * W
  have hC : C ∈ unitaryGroup (Fin 4) ℂ := by
    dsimp [C]
    rw [controlledGate_diag2_eq]
    exact diag4_unitary 1 1 1 (starRingEnd ℂ u₀) (by simp) (by simp) (by simp)
      (by simpa using hu₀)
  refine ⟨V, Submonoid.mul_mem _ hC hW, ?_⟩
  calc
    ccu (diag2 1 (starRingEnd ℂ u₀ * u₁))
        = abgate C * ccu (diag2 u₀ u₁) := by
            symm
            exact abgate_controlled_mul_ccu u₀ u₁ hu₀
    _ = abgate C * (abgate W * U) := by rw [h]
    _ = (abgate C * abgate W) * U := by simp [mul_assoc]
    _ = abgate (C * W) * U := by rw [← abgate_mul]
    _ = abgate V * U := by rfl

set_option maxHeartbeats 2000000 in
private lemma ccu_mul_abgate_controlled (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) :
    ccu (diag2 u₀ u₁) * abgate (controlledGate (diag2 1 (starRingEnd ℂ u₀))) =
      ccu (diag2 1 (starRingEnd ℂ u₀ * u₁)) := by
  have hu₀conj : starRingEnd ℂ u₀ * u₀ = 1 := by
    simp [Complex.conj_mul', hu₀]
  have hu₀' : u₀ * starRingEnd ℂ u₀ = 1 := by
    simpa [mul_comm] using hu₀conj
  rw [abgate_controlledGate_diag2_eq, ccu_diag2_eq, ccu_diag2_eq, diag8_mul]
  simp [hu₀', mul_comm]

private lemma section7_lemma_7_1_right (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1)
    (W : Square 4) (hW : W ∈ unitaryGroup (Fin 4) ℂ)
    (U : Square 8)
    (h : ccu (diag2 u₀ u₁) = U * abgate W) :
    ∃ V : Square 4, V ∈ unitaryGroup (Fin 4) ℂ ∧
      ccu (diag2 1 (starRingEnd ℂ u₀ * u₁)) = U * abgate V := by
  let C : Square 4 := controlledGate (diag2 1 (starRingEnd ℂ u₀))
  let V : Square 4 := W * C
  have hC : C ∈ unitaryGroup (Fin 4) ℂ := by
    dsimp [C]
    rw [controlledGate_diag2_eq]
    exact diag4_unitary 1 1 1 (starRingEnd ℂ u₀) (by simp) (by simp) (by simp)
      (by simpa using hu₀)
  refine ⟨V, Submonoid.mul_mem _ hW hC, ?_⟩
  calc
    ccu (diag2 1 (starRingEnd ℂ u₀ * u₁))
        = ccu (diag2 u₀ u₁) * abgate C := by
            symm
            exact ccu_mul_abgate_controlled u₀ u₁ hu₀
    _ = (U * abgate W) * abgate C := by rw [h]
    _ = U * (abgate W * abgate C) := by simp [mul_assoc]
    _ = U * abgate (W * C) := by rw [← abgate_mul]
    _ = U * abgate V := by rfl

private lemma finProd_assoc_222 (a b c : Fin 2) :
    (@finProdFinEquiv 4 2 (@finProdFinEquiv 2 2 (a, b), c) : Fin 8) =
      @finProdFinEquiv 2 4 (a, @finProdFinEquiv 2 2 (b, c)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

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

@[simp] private lemma bcgate_add (U W : Square 4) :
    bcgate (U + W) = bcgate U + bcgate W := by
  unfold bcgate
  exact kron_add_right (1 : Square 2) U W

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

private lemma proj0_add_proj1 : proj0 + proj1 = (1 : Square 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, proj1, ketbra, ket0, ket1]

private lemma split_one_kron_terms {n : ℕ} (P Q R : Square n) :
    (1 : Square 2) ⊗ₖ P + proj0 ⊗ₖ Q + proj1 ⊗ₖ R =
      proj0 ⊗ₖ (P + Q) + proj1 ⊗ₖ (P + R) := by
  rw [← proj0_add_proj1, kron_add_left]
  calc
    proj0 ⊗ₖ P + proj1 ⊗ₖ P + proj0 ⊗ₖ Q + proj1 ⊗ₖ R
        = (proj0 ⊗ₖ P + proj0 ⊗ₖ Q) + (proj1 ⊗ₖ P + proj1 ⊗ₖ R) := by
            ac_rfl
    _ = proj0 ⊗ₖ (P + Q) + proj1 ⊗ₖ (P + R) := by
          rw [← kron_add_right, ← kron_add_right]

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

private lemma swap2_mul_swap2_local : swap2 * swap2 = (1 : Square 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2, Matrix.mul_apply, Fin.sum_univ_succ]

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

private lemma swap2_conj_kron_left_local (A : Square 2) :
    swap2 * ((1 : Square 2) ⊗ₖ A) * swap2 = A ⊗ₖ (1 : Square 2) := by
  calc
    swap2 * ((1 : Square 2) ⊗ₖ A) * swap2
        = swap2 * (swap2 * (A ⊗ₖ (1 : Square 2)) * swap2) * swap2 := by
            rw [swap2_conj_kron_right_local]
    _ = (swap2 * (swap2 * (A ⊗ₖ (1 : Square 2)))) * (swap2 * swap2) := by
          simp [mul_assoc]
    _ = (swap2 * (swap2 * (A ⊗ₖ (1 : Square 2)))) * 1 := by
          rw [swap2_mul_swap2_local]
    _ = (swap2 * swap2) * (A ⊗ₖ (1 : Square 2)) := by
          simp [mul_assoc]
    _ = A ⊗ₖ (1 : Square 2) := by
          rw [swap2_mul_swap2_local]
          simp

private lemma swap2_conj_kron_local (X Y : Square 2) :
    swap2 * (X ⊗ₖ Y) * swap2 = Y ⊗ₖ X := by
  ext i j
  calc
    (swap2 * (X ⊗ₖ Y) * swap2) i j
        = (X ⊗ₖ Y) ((Equiv.swap (1 : Fin 4) 2) i) ((Equiv.swap (1 : Fin 4) 2) j) := by
            rw [swap2_conj_apply]
    _ = X (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).1)
            (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).1) *
          Y (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).2)
            (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).2) := by
              simpa using
                (TwoControl.kron_apply (A := X) (B := Y)
                  (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).1)
                  (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) i)).2)
                  (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).1)
                  (((@finProdFinEquiv 2 2).symm ((Equiv.swap (1 : Fin 4) 2) j)).2))
    _ = Y ((@finProdFinEquiv 2 2).symm i).1 ((@finProdFinEquiv 2 2).symm j).1 *
          X ((@finProdFinEquiv 2 2).symm i).2 ((@finProdFinEquiv 2 2).symm j).2 := by
            rw [swap_index_prod i, swap_index_prod j]
            simp [Prod.swap, mul_comm]
    _ = (Y ⊗ₖ X) i j := by
        simpa using
          (TwoControl.kron_apply (A := Y) (B := X)
            ((@finProdFinEquiv 2 2).symm i).1
            ((@finProdFinEquiv 2 2).symm i).2
            ((@finProdFinEquiv 2 2).symm j).1
            ((@finProdFinEquiv 2 2).symm j).2).symm

private lemma swapab_conj_kron_three (X Y Z : Square 2) :
    swapab * (X ⊗ₖ (Y ⊗ₖ Z)) * swapab = Y ⊗ₖ (X ⊗ₖ Z) := by
  unfold swapab
  calc
    (swap2 ⊗ₖ (1 : Square 2)) * (X ⊗ₖ (Y ⊗ₖ Z)) * (swap2 ⊗ₖ (1 : Square 2))
        = (swap2 ⊗ₖ (1 : Square 2)) * ((X ⊗ₖ Y) ⊗ₖ Z) * (swap2 ⊗ₖ (1 : Square 2)) := by
            rw [← kron_assoc_222_local X Y Z]
    _ = ((swap2 * (X ⊗ₖ Y)) ⊗ₖ Z) * (swap2 ⊗ₖ (1 : Square 2)) := by
          rw [← kron_mul_reindex_local swap2 (X ⊗ₖ Y) (1 : Square 2) Z]
          simp
    _ = ((swap2 * (X ⊗ₖ Y)) * swap2) ⊗ₖ (Z * (1 : Square 2)) := by
          rw [← kron_mul_reindex_local (swap2 * (X ⊗ₖ Y)) swap2 Z (1 : Square 2)]
    _ = (Y ⊗ₖ X) ⊗ₖ Z := by
          rw [swap2_conj_kron_local]
          simp
    _ = Y ⊗ₖ (X ⊗ₖ Z) := by
          rw [kron_assoc_222_local Y X Z]

private lemma bcgate_kron_two (X A : Square 2) :
    bcgate (X ⊗ₖ A) = ((1 : Square 2) ⊗ₖ X) ⊗ₖ A := by
  unfold bcgate
  exact (kron_assoc_222_local (1 : Square 2) X A).symm

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
          rw [swap2_conj_kron_local]

private lemma swapab_conj_bcgate_kron_two (X A : Square 2) :
    swapab * bcgate (X ⊗ₖ A) * swapab = acgate (X ⊗ₖ A) := by
  unfold swapab
  rw [bcgate_kron_two, acgate_kron_two]
  calc
    (swap2 ⊗ₖ (1 : Square 2)) * (((1 : Square 2) ⊗ₖ X) ⊗ₖ A) * (swap2 ⊗ₖ (1 : Square 2))
        = ((swap2 * ((1 : Square 2) ⊗ₖ X)) ⊗ₖ A) * (swap2 ⊗ₖ (1 : Square 2)) := by
            rw [← kron_mul_reindex_local swap2 ((1 : Square 2) ⊗ₖ X) (1 : Square 2) A]
            simp
    _ = ((swap2 * ((1 : Square 2) ⊗ₖ X)) * swap2) ⊗ₖ (A * (1 : Square 2)) := by
          rw [← kron_mul_reindex_local (swap2 * ((1 : Square 2) ⊗ₖ X)) swap2 A (1 : Square 2)]
    _ = (X ⊗ₖ (1 : Square 2)) ⊗ₖ A := by
          rw [swap2_conj_kron_left_local]
          simp
    _ = X ⊗ₖ ((1 : Square 2) ⊗ₖ A) := by
          rw [kron_assoc_222_local X (1 : Square 2) A]

private lemma swapab_conj_acgate_kron_two (X A : Square 2) :
    swapab * acgate (X ⊗ₖ A) * swapab = bcgate (X ⊗ₖ A) := by
  unfold swapab
  rw [acgate_kron_two, bcgate_kron_two]
  calc
    (swap2 ⊗ₖ (1 : Square 2)) * (X ⊗ₖ ((1 : Square 2) ⊗ₖ A)) * (swap2 ⊗ₖ (1 : Square 2))
        = (swap2 ⊗ₖ (1 : Square 2)) * ((X ⊗ₖ (1 : Square 2)) ⊗ₖ A) * (swap2 ⊗ₖ (1 : Square 2)) := by
            rw [← kron_assoc_222_local X (1 : Square 2) A]
    _ = ((swap2 * (X ⊗ₖ (1 : Square 2))) ⊗ₖ A) * (swap2 ⊗ₖ (1 : Square 2)) := by
          rw [← kron_mul_reindex_local swap2 (X ⊗ₖ (1 : Square 2)) (1 : Square 2) A]
          simp
    _ = ((swap2 * (X ⊗ₖ (1 : Square 2))) * swap2) ⊗ₖ (A * (1 : Square 2)) := by
          rw [← kron_mul_reindex_local (swap2 * (X ⊗ₖ (1 : Square 2))) swap2 A (1 : Square 2)]
    _ = ((1 : Square 2) ⊗ₖ X) ⊗ₖ A := by
          rw [swap2_conj_kron_right_local]
          simp

private lemma swap2_conjTranspose_local : swap2† = swap2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2]

private lemma swap2_mul_swap2_aux : swap2 * swap2 = (1 : Square 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma swap2_mem_unitaryGroup : swap2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  calc
    swap2† * swap2 = swap2 * swap2 := by rw [swap2_conjTranspose_local]
    _ = (1 : Square 4) := swap2_mul_swap2_aux

@[simp] private lemma bcgate_mul (U W : Square 4) :
    bcgate (U * W) = bcgate U * bcgate W := by
  unfold bcgate
  simpa [TwoControl.kron, Matrix.reindexAlgEquiv_apply] using
    congrArg (Matrix.reindexAlgEquiv ℂ ℂ (@finProdFinEquiv 2 4))
      (Matrix.mul_kronecker_mul (1 : Square 2) (1 : Square 2) U W)

private lemma swapab_mul_swapab : swapab * swapab = (1 : Square 8) := by
  unfold swapab
  rw [← kron_mul_reindex_local swap2 swap2 (1 : Square 2) (1 : Square 2)]
  simpa [swap2_mul_swap2_aux] using (TwoControl.one_kron_one 4 2)

private lemma swapbc_mul_swapbc : swapbc * swapbc = (1 : Square 8) := by
  unfold swapbc
  calc
    ((1 : Square 2) ⊗ₖ swap2) * ((1 : Square 2) ⊗ₖ swap2)
        = ((1 : Square 2) * (1 : Square 2)) ⊗ₖ (swap2 * swap2) := by
            rw [← kron_mul_reindex_local (1 : Square 2) (1 : Square 2) swap2 swap2]
    _ = (1 : Square 2) ⊗ₖ (1 : Square 4) := by rw [swap2_mul_swap2_aux]; simp
    _ = (1 : Square 8) := by simpa using (TwoControl.one_kron_one 2 4)

private noncomputable def swapac : Square 8 := swapbc * swapab * swapbc

private lemma swapac_mul_swapac : swapac * swapac = (1 : Square 8) := by
  unfold swapac
  calc
    swapbc * swapab * swapbc * (swapbc * swapab * swapbc)
        = swapbc * swapab * (swapbc * swapbc) * swapab * swapbc := by simp [mul_assoc]
    _ = swapbc * swapab * swapab * swapbc := by rw [swapbc_mul_swapbc]; simp [mul_assoc]
    _ = swapbc * (swapab * swapab) * swapbc := by simp [mul_assoc]
    _ = swapbc * swapbc := by rw [swapab_mul_swapab]; simp
    _ = (1 : Square 8) := swapbc_mul_swapbc

@[simp] private lemma abgate_one : abgate (1 : Square 4) = (1 : Square 8) := by
  unfold abgate
  simpa using (TwoControl.one_kron_one 4 2)

@[simp] private lemma bcgate_one : bcgate (1 : Square 4) = (1 : Square 8) := by
  unfold bcgate
  simpa using (TwoControl.one_kron_one 2 4)

@[simp] private lemma acgate_mul (U W : Square 4) :
    acgate (U * W) = acgate U * acgate W := by
  unfold acgate
  rw [abgate_mul]
  calc
    swapbc * (abgate U * abgate W) * swapbc
        = swapbc * abgate U * abgate W * swapbc := by simp [mul_assoc]
    _ = swapbc * abgate U * (swapbc * swapbc) * abgate W * swapbc := by
          rw [swapbc_mul_swapbc]
          simp [mul_assoc]
    _ = (swapbc * abgate U * swapbc) * (swapbc * abgate W * swapbc) := by
          simp [mul_assoc]
    _ = acgate U * acgate W := by rfl

@[simp] private lemma acgate_one : acgate (1 : Square 4) = (1 : Square 8) := by
  unfold acgate
  rw [abgate_one]
  simp [swapbc_mul_swapbc]

@[simp] private lemma bcgate_swap2_eq : bcgate swap2 = swapbc := by
  rfl

@[simp] private lemma abgate_swap2_eq : abgate swap2 = swapab := by
  rfl

@[simp] private lemma acgate_swap2_eq : acgate swap2 = swapac := by
  rfl

private lemma swapab_conj_abgate (U : Square 4) :
    swapab * abgate U * swapab = abgate (swap2 * U * swap2) := by
  unfold swapab abgate
  calc
    (swap2 ⊗ₖ (1 : Square 2)) * (U ⊗ₖ (1 : Square 2)) * (swap2 ⊗ₖ (1 : Square 2))
        = (((swap2 * U) ⊗ₖ ((1 : Square 2) * (1 : Square 2)))) * (swap2 ⊗ₖ (1 : Square 2)) := by
            rw [← kron_mul_reindex_local swap2 U (1 : Square 2) (1 : Square 2)]
    _ = ((swap2 * U) ⊗ₖ (1 : Square 2)) * (swap2 ⊗ₖ (1 : Square 2)) := by
          simp
    _ = ((swap2 * U) * swap2) ⊗ₖ ((1 : Square 2) * (1 : Square 2)) := by
          rw [← kron_mul_reindex_local (swap2 * U) swap2 (1 : Square 2) (1 : Square 2)]
    _ = abgate (swap2 * U * swap2) := by simp [mul_assoc, abgate]

@[simp] private lemma swapbc_conj_ab (U : Square 4) :
    swapbc * abgate U * swapbc = acgate U := by
  rfl

private lemma swapbc_conj_ac (U : Square 4) :
    swapbc * acgate U * swapbc = abgate U := by
  unfold acgate
  calc
    swapbc * (swapbc * abgate U * swapbc) * swapbc
        = (swapbc * swapbc) * abgate U * (swapbc * swapbc) := by simp [mul_assoc]
  _ = abgate U := by rw [swapbc_mul_swapbc]; simp

private lemma swapbc_conj_bcgate (U : Square 4) :
    swapbc * bcgate U * swapbc = bcgate (swap2 * U * swap2) := by
  unfold swapbc bcgate
  calc
    ((1 : Square 2) ⊗ₖ swap2) * ((1 : Square 2) ⊗ₖ U) * ((1 : Square 2) ⊗ₖ swap2)
        = (((1 : Square 2) * (1 : Square 2)) ⊗ₖ (swap2 * U)) * ((1 : Square 2) ⊗ₖ swap2) := by
            rw [← kron_mul_reindex_local (1 : Square 2) (1 : Square 2) swap2 U]
    _ = (((1 : Square 2) * (1 : Square 2)) * (1 : Square 2)) ⊗ₖ ((swap2 * U) * swap2) := by
          rw [← kron_mul_reindex_local ((1 : Square 2) * (1 : Square 2)) (1 : Square 2) (swap2 * U) swap2]
    _ = bcgate (swap2 * U * swap2) := by simp [mul_assoc, bcgate]

private lemma swapab_conj_acgate (U : Square 4) :
    swapab * acgate U * swapab = bcgate U := by
  let Ub : BlockMatrix 2 := blockify (n := 2) U
  let A : Square 2 := Ub.toBlocks₁₁
  let B : Square 2 := Ub.toBlocks₁₂
  let C : Square 2 := Ub.toBlocks₂₁
  let D : Square 2 := Ub.toBlocks₂₂
  have hUdecomp : U = proj0 ⊗ₖ A + proj01 ⊗ₖ B + proj10 ⊗ₖ C + proj1 ⊗ₖ D := by
    dsimp [A, B, C, D, Ub]
    simpa using (blockDecomposition (n := 2) U)
  rw [hUdecomp]
  repeat rw [acgate_add]
  repeat rw [bcgate_add]
  simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm, swapab_conj_acgate_kron_two]

set_option maxHeartbeats 400000 in
private lemma swapab_conj_bcgate (U : Square 4) :
    swapab * bcgate U * swapab = acgate U := by
  let Ub : BlockMatrix 2 := blockify (n := 2) U
  let A : Square 2 := Ub.toBlocks₁₁
  let B : Square 2 := Ub.toBlocks₁₂
  let C : Square 2 := Ub.toBlocks₂₁
  let D : Square 2 := Ub.toBlocks₂₂
  have hUdecomp : U = proj0 ⊗ₖ A + proj01 ⊗ₖ B + proj10 ⊗ₖ C + proj1 ⊗ₖ D := by
    dsimp [A, B, C, D, Ub]
    simpa using (blockDecomposition (n := 2) U)
  rw [hUdecomp]
  repeat rw [bcgate_add]
  repeat rw [acgate_add]
  simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm, swapab_conj_bcgate_kron_two]

private lemma swapac_conj_ab (U : Square 4) :
    swapac * abgate U * swapac = bcgate (swap2 * U * swap2) := by
  unfold swapac
  calc
    swapbc * swapab * swapbc * abgate U * (swapbc * swapab * swapbc)
        = swapbc * (swapab * (swapbc * abgate U * swapbc) * swapab) * swapbc := by
            simp [mul_assoc]
    _ = swapbc * (swapab * acgate U * swapab) * swapbc := by rw [swapbc_conj_ab]
    _ = swapbc * bcgate U * swapbc := by rw [swapab_conj_acgate]
    _ = bcgate (swap2 * U * swap2) := by rw [swapbc_conj_bcgate]

private lemma swapac_conj_ac (U : Square 4) :
    swapac * acgate U * swapac = acgate (swap2 * U * swap2) := by
  unfold swapac
  calc
    swapbc * swapab * swapbc * acgate U * (swapbc * swapab * swapbc)
        = swapbc * (swapab * (swapbc * acgate U * swapbc) * swapab) * swapbc := by
            simp [mul_assoc]
    _ = swapbc * (swapab * abgate U * swapab) * swapbc := by rw [swapbc_conj_ac]
    _ = swapbc * abgate (swap2 * U * swap2) * swapbc := by rw [swapab_conj_abgate]
    _ = acgate (swap2 * U * swap2) := by rw [swapbc_conj_ab]

private lemma swapac_conj_bc (U : Square 4) :
    swapac * bcgate U * swapac = abgate (swap2 * U * swap2) := by
  unfold swapac
  calc
    swapbc * swapab * swapbc * bcgate U * (swapbc * swapab * swapbc)
        = swapbc * (swapab * (swapbc * bcgate U * swapbc) * swapab) * swapbc := by
            simp [mul_assoc]
    _ = swapbc * (swapab * bcgate (swap2 * U * swap2) * swapab) * swapbc := by
          rw [swapbc_conj_bcgate]
    _ = swapbc * acgate (swap2 * U * swap2) * swapbc := by rw [swapab_conj_bcgate]
    _ = abgate (swap2 * U * swap2) := by rw [swapbc_conj_ac]

set_option maxHeartbeats 1200000 in
private lemma swapab_conj_ccu_diag2 (u₀ u₁ : ℂ) :
    swapab * ccu (diag2 u₀ u₁) * swapab = ccu (diag2 u₀ u₁) := by
  have hOne4 : (1 : Square 4) = (1 : Square 2) ⊗ₖ (1 : Square 2) := by
    symm
    exact TwoControl.one_kron_one 2 2
  have hInnerOne :
      proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ (1 : Square 2) = (1 : Square 2) ⊗ₖ (1 : Square 2) := by
    rw [← proj0_add_proj1, kron_add_left, proj0_add_proj1]
  calc
    swapab * ccu (diag2 u₀ u₁) * swapab
        = swapab *
            (proj0 ⊗ₖ ((1 : Square 2) ⊗ₖ (1 : Square 2)) +
              proj1 ⊗ₖ (proj0 ⊗ₖ (1 : Square 2)) +
              proj1 ⊗ₖ (proj1 ⊗ₖ diag2 u₀ u₁)) * swapab := by
                unfold ccu controlledGate
                rw [hOne4, kron_add_right]
                simp [add_assoc]
    _ = (1 : Square 2) ⊗ₖ (proj0 ⊗ₖ (1 : Square 2)) +
          proj0 ⊗ₖ (proj1 ⊗ₖ (1 : Square 2)) +
          proj1 ⊗ₖ (proj1 ⊗ₖ diag2 u₀ u₁) := by
            rw [mul_add, add_mul]
            rw [mul_add, add_mul]
            rw [swapab_conj_kron_three, swapab_conj_kron_three, swapab_conj_kron_three]
    _ = proj0 ⊗ₖ ((proj0 ⊗ₖ (1 : Square 2)) + (proj1 ⊗ₖ (1 : Square 2))) +
          proj1 ⊗ₖ ((proj0 ⊗ₖ (1 : Square 2)) + (proj1 ⊗ₖ diag2 u₀ u₁)) := by
            simpa [add_assoc] using
              (split_one_kron_terms
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

private lemma swapbc_conj_kron (A : Square 2) (B : Square 4) :
    swapbc * (A ⊗ₖ B) * swapbc = A ⊗ₖ (swap2 * B * swap2) := by
  unfold swapbc
  calc
    ((1 : Square 2) ⊗ₖ swap2) * (A ⊗ₖ B) * ((1 : Square 2) ⊗ₖ swap2)
        = (((1 : Square 2) * A) ⊗ₖ (swap2 * B)) * ((1 : Square 2) ⊗ₖ swap2) := by
            rw [← kron_mul_reindex_local (1 : Square 2) A swap2 B]
    _ = (((1 : Square 2) * A) * (1 : Square 2)) ⊗ₖ ((swap2 * B) * swap2) := by
          rw [← kron_mul_reindex_local ((1 : Square 2) * A) (1 : Square 2) (swap2 * B) swap2]
    _ = A ⊗ₖ (swap2 * B * swap2) := by
          simp [mul_assoc]

private lemma swap2_conj_diag4_one (u : ℂ) :
    swap2 * diag4 1 1 1 u * swap2 = diag4 1 1 1 u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag4, swap2, Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ]

private lemma swapbc_conj_mul2 (X Y : Square 8) :
    swapbc * (X * Y) * swapbc = (swapbc * X * swapbc) * (swapbc * Y * swapbc) := by
  calc
    swapbc * (X * Y) * swapbc
        = swapbc * X * (swapbc * swapbc) * Y * swapbc := by
            simp [mul_assoc, swapbc_mul_swapbc]
    _ = (swapbc * X * swapbc) * (swapbc * Y * swapbc) := by
          simp [mul_assoc]

private lemma swapbc_conj_ccu_diag2_one (u : ℂ) :
    swapbc * ccu (diag2 1 u) * swapbc = ccu (diag2 1 u) := by
  rw [ccu, controlledGate_diag2_eq]
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [swapbc_conj_kron proj0 (1 : Square 4), swapbc_conj_kron proj1 (diag4 1 1 1 u)]
  simp [swap2_mul_swap2_aux, swap2_conj_diag4_one]

private lemma swapac_conj_ccu_diag2_one (u : ℂ) :
    swapac * ccu (diag2 1 u) * swapac = ccu (diag2 1 u) := by
  unfold swapac
  calc
    swapbc * swapab * swapbc * ccu (diag2 1 u) * (swapbc * swapab * swapbc)
        = swapbc * (swapab * (swapbc * ccu (diag2 1 u) * swapbc) * swapab) * swapbc := by
            simp [mul_assoc]
    _ = swapbc * (swapab * ccu (diag2 1 u) * swapab) * swapbc := by
          rw [swapbc_conj_ccu_diag2_one]
    _ = swapbc * ccu (diag2 1 u) * swapbc := by rw [swapab_conj_ccu_diag2]
    _ = ccu (diag2 1 u) := by rw [swapbc_conj_ccu_diag2_one]

private lemma swap2_conj_unitary {U : Square 4}
    (hU : U ∈ unitaryGroup (Fin 4) ℂ) :
    swap2 * U * swap2 ∈ unitaryGroup (Fin 4) ℂ := by
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ swap2_mem_unitaryGroup hU) swap2_mem_unitaryGroup

private lemma swapab_twoQubitGate (U : Square 8) (hU : TwoQubitGate U) :
    TwoQubitGate (swapab * U * swapab) := by
  rcases hU with ⟨V, hV, hEq | hEq | hEq⟩
  · refine ⟨swap2 * V * swap2, swap2_conj_unitary hV, ?_⟩
    left
    rw [hEq]
    exact swapab_conj_abgate V
  · refine ⟨V, hV, ?_⟩
    right
    right
    rw [hEq]
    exact swapab_conj_acgate V
  · refine ⟨V, hV, ?_⟩
    right
    left
    rw [hEq]
    exact swapab_conj_bcgate V

private lemma swapac_twoQubitGate (U : Square 8) (hU : TwoQubitGate U) :
    TwoQubitGate (swapac * U * swapac) := by
  rcases hU with ⟨V, hV, hEq | hEq | hEq⟩
  · refine ⟨swap2 * V * swap2, swap2_conj_unitary hV, ?_⟩
    right
    right
    rw [hEq]
    exact swapac_conj_ab V
  · refine ⟨swap2 * V * swap2, swap2_conj_unitary hV, ?_⟩
    right
    left
    rw [hEq]
    exact swapac_conj_ac V
  · refine ⟨swap2 * V * swap2, swap2_conj_unitary hV, ?_⟩
    left
    rw [hEq]
    exact swapac_conj_bc V

private lemma canonicalPair_first_norm (u₀ u₁ u₂ u₃ : ℂ)
    (hu₀ : ‖u₀‖ = 1) (hPair : inCanonicalPair u₀ u₁ u₂ u₃) :
    ‖u₂‖ = 1 := by
  rcases hPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hu₀]

private lemma canonicalPair_step (u₀ u₁ u₂ u₃ : ℂ)
    (hPair : inCanonicalPair u₀ u₁ u₂ u₃) :
    inCanonicalPair u₀ u₁ 1 (starRingEnd ℂ u₂ * u₃) := by
  rcases hPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · right
    simp
  · right
    simp

private lemma one4_unitary : (1 : Square 4) ∈ unitaryGroup (Fin 4) ℂ := by
  simp

private lemma unitary_mul2 {U W : Square 4}
    (hU : U ∈ unitaryGroup (Fin 4) ℂ) (hW : W ∈ unitaryGroup (Fin 4) ℂ) :
    U * W ∈ unitaryGroup (Fin 4) ℂ := by
  exact Submonoid.mul_mem _ hU hW

private lemma unitary_mul3 {U W X : Square 4}
    (hU : U ∈ unitaryGroup (Fin 4) ℂ) (hW : W ∈ unitaryGroup (Fin 4) ℂ)
    (hX : X ∈ unitaryGroup (Fin 4) ℂ) :
    U * W * X ∈ unitaryGroup (Fin 4) ℂ := by
  exact Submonoid.mul_mem _ (unitary_mul2 hU hW) hX

private lemma unitary_mul4 {U W X Y : Square 4}
    (hU : U ∈ unitaryGroup (Fin 4) ℂ) (hW : W ∈ unitaryGroup (Fin 4) ℂ)
    (hX : X ∈ unitaryGroup (Fin 4) ℂ) (hY : Y ∈ unitaryGroup (Fin 4) ℂ) :
    U * W * X * Y ∈ unitaryGroup (Fin 4) ℂ := by
  exact Submonoid.mul_mem _ (unitary_mul3 hU hW hX) hY

private lemma unitary_mul_swap2_right {U : Square 4}
    (hU : U ∈ unitaryGroup (Fin 4) ℂ) :
    U * swap2 ∈ unitaryGroup (Fin 4) ℂ := by
  exact Submonoid.mul_mem _ hU swap2_mem_unitaryGroup

private lemma unitary_mul_swap2_left {U : Square 4}
    (hU : U ∈ unitaryGroup (Fin 4) ℂ) :
    swap2 * U ∈ unitaryGroup (Fin 4) ℂ := by
  exact Submonoid.mul_mem _ swap2_mem_unitaryGroup hU

private lemma swapbc_conj_word_acab (B C : Square 4) :
    swapbc * (acgate B * abgate C) * swapbc = abgate B * acgate C := by
  calc
    swapbc * (acgate B * abgate C) * swapbc
        = swapbc * acgate B * (swapbc * swapbc) * abgate C * swapbc := by
            simp [mul_assoc, swapbc_mul_swapbc]
    _ = (swapbc * acgate B * swapbc) * (swapbc * abgate C * swapbc) := by
          simp [mul_assoc]
    _ = abgate B * acgate C := by
          rw [swapbc_conj_ac, swapbc_conj_ab]

private lemma normalize_word_acabac (A B C D : Square 4) :
    acgate A * abgate B * acgate C * bcgate D =
      acgate (A * swap2) * bcgate (swap2 * B * swap2) * acgate (swap2 * C) * bcgate D := by
  symm
  calc
    acgate (A * swap2) * bcgate (swap2 * B * swap2) * acgate (swap2 * C) * bcgate D
        = acgate A * (acgate swap2 * bcgate (swap2 * B * swap2) * acgate swap2) * acgate C * bcgate D := by
            simp [mul_assoc]
    _ = acgate A * abgate (swap2 * (swap2 * B * swap2) * swap2) * acgate C * bcgate D := by
        rw [acgate_swap2_eq, swapac_conj_bc]
    _ = acgate A * abgate B * acgate C * bcgate D := by
        have hs : swap2 * (swap2 * B * swap2) * swap2 = B := by
          calc
            swap2 * (swap2 * B * swap2) * swap2
                = ((swap2 * swap2) * B) * (swap2 * swap2) := by simp [mul_assoc]
            _ = B := by simp [swap2_mul_swap2_aux]
        rw [hs]

private lemma normalize_word_acbcab (A B C D : Square 4) :
    acgate A * bcgate B * abgate C * bcgate D =
      acgate A * bcgate (B * swap2) * acgate C * bcgate (swap2 * D) := by
  symm
  calc
    acgate A * bcgate (B * swap2) * acgate C * bcgate (swap2 * D)
        = acgate A * bcgate B * (bcgate swap2 * acgate C * bcgate swap2) * bcgate D := by
            simp [mul_assoc]
    _ = acgate A * bcgate B * abgate C * bcgate D := by
          rw [bcgate_swap2_eq, swapbc_conj_ac]

private lemma normalize_word_bcabac (A B C D : Square 4) :
    bcgate A * abgate B * acgate C * bcgate D =
      bcgate (A * swap2) * acgate B * abgate C * bcgate (swap2 * D) := by
  symm
  calc
    bcgate (A * swap2) * acgate B * abgate C * bcgate (swap2 * D)
        = bcgate A * (bcgate swap2 * (acgate B * abgate C) * bcgate swap2) * bcgate D := by
            simp [mul_assoc]
    _ = bcgate A * abgate B * acgate C * bcgate D := by
          rw [bcgate_swap2_eq, swapbc_conj_word_acab]
          simp [mul_assoc]

private lemma swapbc_conj_word_abacbc (A B D : Square 4) :
    swapbc * (abgate A * acgate B * bcgate D) * swapbc =
      acgate A * bcgate swap2 * acgate B * bcgate (D * swap2) := by
  calc
    swapbc * (abgate A * acgate B * bcgate D) * swapbc
    = (swapbc * abgate A * swapbc) * (swapbc * (acgate B * bcgate D) * swapbc) := by
      simpa [mul_assoc] using swapbc_conj_mul2 (abgate A) (acgate B * bcgate D)
    _ = acgate A * bcgate swap2 * acgate B * bcgate (D * swap2) := by
          rw [swapbc_conj_ab]
          simp [bcgate_swap2_eq, mul_assoc]

private lemma swapbc_conj_word_abacabbc (A B C D : Square 4) :
    swapbc * (abgate A * acgate B * abgate C * bcgate D) * swapbc =
      acgate A * abgate B * acgate C * bcgate (swap2 * D * swap2) := by
  calc
    swapbc * (abgate A * acgate B * abgate C * bcgate D) * swapbc
        = (swapbc * (abgate A * acgate B) * swapbc) * (swapbc * (abgate C * bcgate D) * swapbc) := by
            simpa [mul_assoc] using swapbc_conj_mul2 (abgate A * acgate B) (abgate C * bcgate D)
    _ = (swapbc * abgate A * swapbc) * (swapbc * acgate B * swapbc) *
          (swapbc * abgate C * swapbc) * (swapbc * bcgate D * swapbc) := by
          rw [swapbc_conj_mul2, swapbc_conj_mul2]
          simp [mul_assoc]
    _ = acgate A * abgate B * acgate C * bcgate (swap2 * D * swap2) := by
          rw [swapbc_conj_ab, swapbc_conj_ac, swapbc_conj_ab, swapbc_conj_bcgate]

private lemma swapbc_conj_word_abbabbc (A B C D : Square 4) :
    swapbc * (abgate A * bcgate B * abgate C * bcgate D) * swapbc =
      acgate A * bcgate (swap2 * B * swap2) * acgate C * bcgate (swap2 * D * swap2) := by
  calc
    swapbc * (abgate A * bcgate B * abgate C * bcgate D) * swapbc
        = (swapbc * (abgate A * bcgate B) * swapbc) * (swapbc * (abgate C * bcgate D) * swapbc) := by
            simpa [mul_assoc] using swapbc_conj_mul2 (abgate A * bcgate B) (abgate C * bcgate D)
    _ = (swapbc * abgate A * swapbc) * (swapbc * bcgate B * swapbc) *
          (swapbc * abgate C * swapbc) * (swapbc * bcgate D * swapbc) := by
          rw [swapbc_conj_mul2, swapbc_conj_mul2]
          simp [mul_assoc]
    _ = acgate A * bcgate (swap2 * B * swap2) * acgate C * bcgate (swap2 * D * swap2) := by
          rw [swapbc_conj_ab, swapbc_conj_bcgate, swapbc_conj_ab, swapbc_conj_bcgate]

private lemma swapbc_conj_word_abbcacbc (A B C D : Square 4) :
    swapbc * (abgate A * bcgate B * acgate C * bcgate D) * swapbc =
      acgate A * bcgate (swap2 * B * swap2) * abgate C * bcgate (swap2 * D * swap2) := by
  calc
    swapbc * (abgate A * bcgate B * acgate C * bcgate D) * swapbc
        = (swapbc * (abgate A * bcgate B) * swapbc) * (swapbc * (acgate C * bcgate D) * swapbc) := by
            simpa [mul_assoc] using swapbc_conj_mul2 (abgate A * bcgate B) (acgate C * bcgate D)
    _ = (swapbc * abgate A * swapbc) * (swapbc * bcgate B * swapbc) *
          (swapbc * acgate C * swapbc) * (swapbc * bcgate D * swapbc) := by
          rw [swapbc_conj_mul2, swapbc_conj_mul2]
          simp [mul_assoc]
    _ = acgate A * bcgate (swap2 * B * swap2) * abgate C * bcgate (swap2 * D * swap2) := by
          rw [swapbc_conj_ab, swapbc_conj_bcgate, swapbc_conj_ac, swapbc_conj_bcgate]

private lemma section7_lemma_7_2_step3
    (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1)
    (V₁ V₂ V₃ V₄ : Square 8)
    (hV₁ : TwoQubitGate V₁) (hV₂ : TwoQubitGate V₂)
    (hV₃ : TwoQubitGate V₃) (hV₄ : TwoQubitGate V₄)
    (h : V₁ * V₂ * V₃ * V₄ = ccu (diag2 u₀ u₁)) :
    ∃ u₂ u₃ : ℂ, ∃ W₁ W₂ W₃ : Square 8, ∃ W₄ : Square 4,
      inCanonicalPair u₀ u₁ u₂ u₃ ∧
      TwoQubitGate W₁ ∧
      TwoQubitGate W₂ ∧
      TwoQubitGate W₃ ∧
      W₄ ∈ unitaryGroup (Fin 4) ℂ ∧
      W₁ * W₂ * W₃ * bcgate W₄ = ccu (diag2 u₂ u₃) := by
  rcases hV₄ with ⟨X₄, hX₄, hX₄ab | hX₄ac | hX₄bc⟩
  · have hRight : ccu (diag2 u₀ u₁) = (V₁ * V₂ * V₃) * abgate X₄ := by
      calc
        ccu (diag2 u₀ u₁) = V₁ * V₂ * V₃ * V₄ := by simpa using h.symm
        _ = (V₁ * V₂ * V₃) * abgate X₄ := by simp [hX₄ab, mul_assoc]
    rcases section7_lemma_7_1_right u₀ u₁ hu₀ X₄ hX₄ (V₁ * V₂ * V₃) hRight with
      ⟨Y₄, hY₄, hYeq⟩
    refine ⟨1, starRingEnd ℂ u₀ * u₁,
      swapac * V₁ * swapac, swapac * V₂ * swapac, swapac * V₃ * swapac,
      swap2 * Y₄ * swap2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · right
      simp
    · exact swapac_twoQubitGate V₁ hV₁
    · exact swapac_twoQubitGate V₂ hV₂
    · exact swapac_twoQubitGate V₃ hV₃
    · exact swap2_conj_unitary hY₄
    · calc
        (swapac * V₁ * swapac) * (swapac * V₂ * swapac) * (swapac * V₃ * swapac) *
            bcgate (swap2 * Y₄ * swap2)
            = (swapac * V₁ * swapac) * (swapac * V₂ * swapac) * (swapac * V₃ * swapac) *
                (swapac * abgate Y₄ * swapac) := by rw [← swapac_conj_ab]
        _ = swapac * V₁ * (swapac * swapac) * V₂ * (swapac * swapac) * V₃ *
            (swapac * swapac) * abgate Y₄ * swapac := by simp [mul_assoc]
        _ = swapac * ((V₁ * V₂ * V₃) * abgate Y₄) * swapac := by simp [swapac_mul_swapac, mul_assoc]
        _ = swapac * ccu (diag2 1 (starRingEnd ℂ u₀ * u₁)) * swapac := by rw [hYeq]
        _ = ccu (diag2 1 (starRingEnd ℂ u₀ * u₁)) := by rw [swapac_conj_ccu_diag2_one]
  · have hEq' : V₁ * V₂ * V₃ * acgate X₄ = ccu (diag2 u₀ u₁) := by
      simpa [hX₄ac, mul_assoc] using h
    refine ⟨u₀, u₁,
      swapab * V₁ * swapab, swapab * V₂ * swapab, swapab * V₃ * swapab, X₄,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · left
      simp
    · exact swapab_twoQubitGate V₁ hV₁
    · exact swapab_twoQubitGate V₂ hV₂
    · exact swapab_twoQubitGate V₃ hV₃
    · exact hX₄
    · calc
        (swapab * V₁ * swapab) * (swapab * V₂ * swapab) * (swapab * V₃ * swapab) * bcgate X₄
            = (swapab * V₁ * swapab) * (swapab * V₂ * swapab) * (swapab * V₃ * swapab) *
                (swapab * acgate X₄ * swapab) := by rw [← swapab_conj_acgate]
        _ = swapab * V₁ * (swapab * swapab) * V₂ * (swapab * swapab) * V₃ *
            (swapab * swapab) * acgate X₄ * swapab := by simp [mul_assoc]
        _ = swapab * (V₁ * V₂ * V₃ * acgate X₄) * swapab := by simp [swapab_mul_swapab, mul_assoc]
        _ = swapab * ccu (diag2 u₀ u₁) * swapab := by rw [hEq']
        _ = ccu (diag2 u₀ u₁) := by rw [swapab_conj_ccu_diag2]
  · refine ⟨u₀, u₁, V₁, V₂, V₃, X₄, ?_, hV₁, hV₂, hV₃, hX₄, ?_⟩
    · left
      simp
    · simpa [hX₄bc, mul_assoc] using h

set_option maxHeartbeats 4000000

/-- **Lemma 7.2** (Reduction to canonical forms.)
If a product of four `TwoQubitGate`s equals `CC(Diag(u₀, u₁))`, then there exist
2-qubit unitaries and parameters `(u₂, u₃) ∈ R(u₀, u₁)` achieving one of two
canonical gate-ordering patterns. -/
lemma section7_lemma_7_2 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (_hu₁ : ‖u₁‖ = 1)
    (V₁ V₂ V₃ V₄ : Square 8)
    (hV₁ : TwoQubitGate V₁) (hV₂ : TwoQubitGate V₂)
    (hV₃ : TwoQubitGate V₃) (hV₄ : TwoQubitGate V₄)
    (h : V₁ * V₂ * V₃ * V₄ = ccu (diag2 u₀ u₁)) :
    ∃ u₂ u₃ : ℂ, ∃ U₁ U₂ U₃ U₄ : Square 4,
      inCanonicalPair u₀ u₁ u₂ u₃ ∧
      U₁ ∈ unitaryGroup (Fin 4) ℂ ∧
      U₂ ∈ unitaryGroup (Fin 4) ℂ ∧
      U₃ ∈ unitaryGroup (Fin 4) ℂ ∧
      U₄ ∈ unitaryGroup (Fin 4) ℂ ∧
      (bcgate U₁ * acgate U₂ * abgate U₃ * bcgate U₄ = ccu (diag2 u₂ u₃) ∨
       acgate U₁ * bcgate U₂ * acgate U₃ * bcgate U₄ = ccu (diag2 u₂ u₃)) := by
  rcases section7_lemma_7_2_step3 u₀ u₁ hu₀ V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ h with
    ⟨u₂, u₃, W₁, W₂, W₃, W₄, hPair, hW₁, hW₂, hW₃, hW₄, hEq⟩
  have hu₂ : ‖u₂‖ = 1 := canonicalPair_first_norm u₀ u₁ u₂ u₃ hu₀ hPair
  have hPairStep : inCanonicalPair u₀ u₁ 1 (starRingEnd ℂ u₂ * u₃) :=
    canonicalPair_step u₀ u₁ u₂ u₃ hPair
  rcases hW₁ with ⟨A, hA, hW₁ab | hW₁ac | hW₁bc⟩
  · rcases hW₂ with ⟨B, hB, hW₂ab | hW₂ac | hW₂bc⟩
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · refine ⟨u₂, u₃, 1, 1, A * B * C, W₄, hPair, one4_unitary, one4_unitary,
          unitary_mul3 hA hB hC, hW₄, Or.inl ?_⟩
        simpa [hW₁ab, hW₂ab, hW₃ab, mul_assoc] using hEq
      · have hStart :
          ccu (diag2 u₂ u₃) = abgate (A * B) * (acgate C * bcgate W₄) := by
            calc
              ccu (diag2 u₂ u₃) = W₁ * W₂ * W₃ * bcgate W₄ := by simpa using hEq.symm
              _ = abgate A * abgate B * acgate C * bcgate W₄ := by
                    rw [hW₁ab, hW₂ab, hW₃ac]
              _ = abgate (A * B) * (acgate C * bcgate W₄) := by
                    simp [mul_assoc]
        rcases section7_lemma_7_1_left u₂ u₃ hu₂ (A * B) (unitary_mul2 hA hB)
          (acgate C * bcgate W₄) hStart with ⟨V, hV, hVeq⟩
        have hWord :
            abgate V * acgate C * bcgate W₄ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by
          simpa [mul_assoc] using hVeq.symm
        refine ⟨1, starRingEnd ℂ u₂ * u₃, V, swap2, C, W₄ * swap2, hPairStep,
          hV, swap2_mem_unitaryGroup, hC, unitary_mul_swap2_right hW₄, Or.inr ?_⟩
        calc
          acgate V * bcgate swap2 * acgate C * bcgate (W₄ * swap2)
              = swapbc * (abgate V * acgate C * bcgate W₄) * swapbc := by
                  symm
                  exact swapbc_conj_word_abacbc V C W₄
          _ = swapbc * ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) * swapbc := by rw [hWord]
          _ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by rw [swapbc_conj_ccu_diag2_one]
      · refine ⟨u₂, u₃, 1, 1, A * B, C * W₄, hPair, one4_unitary, one4_unitary,
          unitary_mul2 hA hB, unitary_mul2 hC hW₄, Or.inl ?_⟩
        simpa [hW₁ab, hW₂ab, hW₃bc, mul_assoc] using hEq
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · have hStart :
          ccu (diag2 u₂ u₃) = abgate A * (acgate B * abgate C * bcgate W₄) := by
            calc
              ccu (diag2 u₂ u₃) = W₁ * W₂ * W₃ * bcgate W₄ := by simpa using hEq.symm
              _ = abgate A * acgate B * abgate C * bcgate W₄ := by rw [hW₁ab, hW₂ac, hW₃ab]
              _ = abgate A * (acgate B * abgate C * bcgate W₄) := by simp [mul_assoc]
        rcases section7_lemma_7_1_left u₂ u₃ hu₂ A hA
          (acgate B * abgate C * bcgate W₄) hStart with ⟨V, hV, hVeq⟩
        have hWord :
            abgate V * acgate B * abgate C * bcgate W₄ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by
          simpa [mul_assoc] using hVeq.symm
        have hConj :
            acgate V * abgate B * acgate C * bcgate (swap2 * W₄ * swap2) =
              ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by
          calc
            acgate V * abgate B * acgate C * bcgate (swap2 * W₄ * swap2)
                = swapbc * (abgate V * acgate B * abgate C * bcgate W₄) * swapbc := by
                    symm
                    exact swapbc_conj_word_abacabbc V B C W₄
            _ = swapbc * ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) * swapbc := by rw [hWord]
            _ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by rw [swapbc_conj_ccu_diag2_one]
        refine ⟨1, starRingEnd ℂ u₂ * u₃, V * swap2, swap2 * B * swap2, swap2 * C,
          swap2 * W₄ * swap2, hPairStep, unitary_mul_swap2_right hV,
          swap2_conj_unitary hB, unitary_mul_swap2_left hC, swap2_conj_unitary hW₄,
          Or.inr ?_⟩
        calc
          acgate (V * swap2) * bcgate (swap2 * B * swap2) * acgate (swap2 * C) *
              bcgate (swap2 * W₄ * swap2)
              = acgate V * abgate B * acgate C * bcgate (swap2 * W₄ * swap2) := by
                  symm
                  exact normalize_word_acabac V B C (swap2 * W₄ * swap2)
          _ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := hConj
      · have hStart :
          ccu (diag2 u₂ u₃) = abgate A * (acgate (B * C) * bcgate W₄) := by
            calc
              ccu (diag2 u₂ u₃) = W₁ * W₂ * W₃ * bcgate W₄ := by simpa using hEq.symm
              _ = abgate A * acgate B * acgate C * bcgate W₄ := by rw [hW₁ab, hW₂ac, hW₃ac]
              _ = abgate A * (acgate (B * C) * bcgate W₄) := by simp [mul_assoc]
        rcases section7_lemma_7_1_left u₂ u₃ hu₂ A hA
          (acgate (B * C) * bcgate W₄) hStart with ⟨V, hV, hVeq⟩
        have hWord :
            abgate V * acgate (B * C) * bcgate W₄ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by
          simpa [mul_assoc] using hVeq.symm
        refine ⟨1, starRingEnd ℂ u₂ * u₃, V, swap2, B * C, W₄ * swap2, hPairStep,
          hV, swap2_mem_unitaryGroup, unitary_mul2 hB hC, unitary_mul_swap2_right hW₄,
          Or.inr ?_⟩
        calc
          acgate V * bcgate swap2 * acgate (B * C) * bcgate (W₄ * swap2)
              = swapbc * (abgate V * acgate (B * C) * bcgate W₄) * swapbc := by
                  symm
                  exact swapbc_conj_word_abacbc V (B * C) W₄
          _ = swapbc * ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) * swapbc := by rw [hWord]
          _ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by rw [swapbc_conj_ccu_diag2_one]
      · have hStart :
          ccu (diag2 u₂ u₃) = abgate A * (acgate B * bcgate (C * W₄)) := by
            calc
              ccu (diag2 u₂ u₃) = W₁ * W₂ * W₃ * bcgate W₄ := by simpa using hEq.symm
              _ = abgate A * acgate B * bcgate C * bcgate W₄ := by rw [hW₁ab, hW₂ac, hW₃bc]
              _ = abgate A * (acgate B * bcgate (C * W₄)) := by simp [mul_assoc]
        rcases section7_lemma_7_1_left u₂ u₃ hu₂ A hA
          (acgate B * bcgate (C * W₄)) hStart with ⟨V, hV, hVeq⟩
        have hWord :
            abgate V * acgate B * bcgate (C * W₄) = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by
          simpa [mul_assoc] using hVeq.symm
        refine ⟨1, starRingEnd ℂ u₂ * u₃, V, swap2, B, (C * W₄) * swap2, hPairStep,
          hV, swap2_mem_unitaryGroup, hB,
          unitary_mul_swap2_right (unitary_mul2 hC hW₄), Or.inr ?_⟩
        calc
          acgate V * bcgate swap2 * acgate B * bcgate ((C * W₄) * swap2)
              = swapbc * (abgate V * acgate B * bcgate (C * W₄)) * swapbc := by
                  symm
                  exact swapbc_conj_word_abacbc V B (C * W₄)
          _ = swapbc * ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) * swapbc := by rw [hWord]
          _ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by rw [swapbc_conj_ccu_diag2_one]
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · have hStart :
          ccu (diag2 u₂ u₃) = abgate A * (bcgate B * abgate C * bcgate W₄) := by
            calc
              ccu (diag2 u₂ u₃) = W₁ * W₂ * W₃ * bcgate W₄ := by simpa using hEq.symm
              _ = abgate A * bcgate B * abgate C * bcgate W₄ := by rw [hW₁ab, hW₂bc, hW₃ab]
              _ = abgate A * (bcgate B * abgate C * bcgate W₄) := by simp [mul_assoc]
        rcases section7_lemma_7_1_left u₂ u₃ hu₂ A hA
          (bcgate B * abgate C * bcgate W₄) hStart with ⟨V, hV, hVeq⟩
        have hWord :
            abgate V * bcgate B * abgate C * bcgate W₄ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by
          simpa [mul_assoc] using hVeq.symm
        refine ⟨1, starRingEnd ℂ u₂ * u₃, V, swap2 * B * swap2, C, swap2 * W₄ * swap2,
          hPairStep, hV, swap2_conj_unitary hB, hC, swap2_conj_unitary hW₄, Or.inr ?_⟩
        calc
          acgate V * bcgate (swap2 * B * swap2) * acgate C * bcgate (swap2 * W₄ * swap2)
              = swapbc * (abgate V * bcgate B * abgate C * bcgate W₄) * swapbc := by
                  symm
                  exact swapbc_conj_word_abbabbc V B C W₄
          _ = swapbc * ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) * swapbc := by rw [hWord]
          _ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by rw [swapbc_conj_ccu_diag2_one]
      · have hStart :
          ccu (diag2 u₂ u₃) = abgate A * (bcgate B * acgate C * bcgate W₄) := by
            calc
              ccu (diag2 u₂ u₃) = W₁ * W₂ * W₃ * bcgate W₄ := by simpa using hEq.symm
              _ = abgate A * bcgate B * acgate C * bcgate W₄ := by rw [hW₁ab, hW₂bc, hW₃ac]
              _ = abgate A * (bcgate B * acgate C * bcgate W₄) := by simp [mul_assoc]
        rcases section7_lemma_7_1_left u₂ u₃ hu₂ A hA
          (bcgate B * acgate C * bcgate W₄) hStart with ⟨V, hV, hVeq⟩
        have hWord :
            abgate V * bcgate B * acgate C * bcgate W₄ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by
          simpa [mul_assoc] using hVeq.symm
        have hConj :
            acgate V * bcgate (swap2 * B * swap2) * abgate C * bcgate (swap2 * W₄ * swap2) =
              ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by
          calc
            acgate V * bcgate (swap2 * B * swap2) * abgate C * bcgate (swap2 * W₄ * swap2)
                = swapbc * (abgate V * bcgate B * acgate C * bcgate W₄) * swapbc := by
                    symm
                    exact swapbc_conj_word_abbcacbc V B C W₄
            _ = swapbc * ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) * swapbc := by rw [hWord]
            _ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by rw [swapbc_conj_ccu_diag2_one]
        refine ⟨1, starRingEnd ℂ u₂ * u₃, V, swap2 * B, C, W₄ * swap2, hPairStep,
          hV, unitary_mul_swap2_left hB, hC, unitary_mul_swap2_right hW₄, Or.inr ?_⟩
        have hNorm :
            acgate V * bcgate (swap2 * B * swap2) * abgate C * bcgate (swap2 * W₄ * swap2) =
              acgate V * bcgate (swap2 * B) * acgate C * bcgate (W₄ * swap2) := by
          calc
            acgate V * bcgate (swap2 * B * swap2) * abgate C * bcgate (swap2 * W₄ * swap2)
                = acgate V * bcgate ((swap2 * B * swap2) * swap2) * acgate C *
                    bcgate (swap2 * (swap2 * W₄ * swap2)) := by
                      simpa [mul_assoc] using
                        normalize_word_acbcab V (swap2 * B * swap2) C (swap2 * W₄ * swap2)
            _ = acgate V * bcgate (swap2 * B) * acgate C * bcgate (W₄ * swap2) := by
              have hBnorm : ((swap2 * B * swap2) * swap2) = swap2 * B := by
                simp [mul_assoc, swap2_mul_swap2_aux]
              have hWnorm : swap2 * (swap2 * W₄ * swap2) = W₄ * swap2 := by
                calc
                  swap2 * (swap2 * W₄ * swap2) = (swap2 * swap2) * (W₄ * swap2) := by
                      simp [mul_assoc]
                  _ = W₄ * swap2 := by
                        rw [swap2_mul_swap2_aux]
                        simp
              rw [hBnorm, hWnorm]
        calc
          acgate V * bcgate (swap2 * B) * acgate C * bcgate (W₄ * swap2)
              = acgate V * bcgate (swap2 * B * swap2) * abgate C * bcgate (swap2 * W₄ * swap2) :=
                  hNorm.symm
          _ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := hConj
      · refine ⟨u₂, u₃, 1, 1, A, B * C * W₄, hPair, one4_unitary, one4_unitary,
          hA, unitary_mul3 hB hC hW₄, Or.inl ?_⟩
        simpa [hW₁ab, hW₂bc, hW₃bc, mul_assoc] using hEq
  · rcases hW₂ with ⟨B, hB, hW₂ab | hW₂ac | hW₂bc⟩
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · refine ⟨u₂, u₃, 1, A, B * C, W₄, hPair, one4_unitary, hA, unitary_mul2 hB hC,
          hW₄, Or.inl ?_⟩
        simpa [hW₁ac, hW₂ab, hW₃ab, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A * swap2, swap2 * B * swap2, swap2 * C, W₄, hPair,
          unitary_mul_swap2_right hA, swap2_conj_unitary hB, unitary_mul_swap2_left hC,
          hW₄, Or.inr ?_⟩
        calc
          acgate (A * swap2) * bcgate (swap2 * B * swap2) * acgate (swap2 * C) * bcgate W₄
              = acgate A * abgate B * acgate C * bcgate W₄ := by
                  symm
                  exact normalize_word_acabac A B C W₄
          _ = ccu (diag2 u₂ u₃) := by simpa [hW₁ac, hW₂ab, hW₃ac, mul_assoc] using hEq
      · refine ⟨u₂, u₃, 1, A, B, C * W₄, hPair, one4_unitary, hA, hB,
          unitary_mul2 hC hW₄, Or.inl ?_⟩
        simpa [hW₁ac, hW₂ab, hW₃bc, mul_assoc] using hEq
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · refine ⟨u₂, u₃, 1, A * B, C, W₄, hPair, one4_unitary, unitary_mul2 hA hB, hC,
          hW₄, Or.inl ?_⟩
        simpa [hW₁ac, hW₂ac, hW₃ab, mul_assoc] using hEq
      · refine ⟨u₂, u₃, 1, A * B * C, 1, W₄, hPair, one4_unitary, unitary_mul3 hA hB hC,
          one4_unitary, hW₄, Or.inl ?_⟩
        simpa [hW₁ac, hW₂ac, hW₃ac, mul_assoc] using hEq
      · refine ⟨u₂, u₃, 1, A * B, 1, C * W₄, hPair, one4_unitary, unitary_mul2 hA hB,
          one4_unitary, unitary_mul2 hC hW₄, Or.inl ?_⟩
        simpa [hW₁ac, hW₂ac, hW₃bc, mul_assoc] using hEq
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · refine ⟨u₂, u₃, A, B * swap2, C, swap2 * W₄, hPair, hA,
          unitary_mul_swap2_right hB, hC, unitary_mul_swap2_left hW₄, Or.inr ?_⟩
        calc
          acgate A * bcgate (B * swap2) * acgate C * bcgate (swap2 * W₄)
              = acgate A * bcgate B * abgate C * bcgate W₄ := by
                  symm
                  exact normalize_word_acbcab A B C W₄
          _ = ccu (diag2 u₂ u₃) := by simpa [hW₁ac, hW₂bc, hW₃ab, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A, B, C, W₄, hPair, hA, hB, hC, hW₄, Or.inr ?_⟩
        simpa [hW₁ac, hW₂bc, hW₃ac, mul_assoc] using hEq
      · refine ⟨u₂, u₃, 1, A, 1, B * C * W₄, hPair, one4_unitary, hA, one4_unitary,
          unitary_mul3 hB hC hW₄, Or.inl ?_⟩
        simpa [hW₁ac, hW₂bc, hW₃bc, mul_assoc] using hEq
  · rcases hW₂ with ⟨B, hB, hW₂ab | hW₂ac | hW₂bc⟩
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · refine ⟨u₂, u₃, A, 1, B * C, W₄, hPair, hA, one4_unitary, unitary_mul2 hB hC,
          hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂ab, hW₃ab, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A * swap2, B, C, swap2 * W₄, hPair, unitary_mul_swap2_right hA,
          hB, hC, unitary_mul_swap2_left hW₄, Or.inl ?_⟩
        calc
          bcgate (A * swap2) * acgate B * abgate C * bcgate (swap2 * W₄)
              = bcgate A * abgate B * acgate C * bcgate W₄ := by
                  symm
                  exact normalize_word_bcabac A B C W₄
          _ = ccu (diag2 u₂ u₃) := by simpa [hW₁bc, hW₂ab, hW₃ac, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A, 1, B, C * W₄, hPair, hA, one4_unitary, hB,
          unitary_mul2 hC hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂ab, hW₃bc, mul_assoc] using hEq
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · refine ⟨u₂, u₃, A, B, C, W₄, hPair, hA, hB, hC, hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂ac, hW₃ab, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A, B * C, 1, W₄, hPair, hA, unitary_mul2 hB hC,
          one4_unitary, hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂ac, hW₃ac, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A, B, 1, C * W₄, hPair, hA, hB, one4_unitary,
          unitary_mul2 hC hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂ac, hW₃bc, mul_assoc] using hEq
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · refine ⟨u₂, u₃, A * B, 1, C, W₄, hPair, unitary_mul2 hA hB, one4_unitary,
          hC, hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂bc, hW₃ab, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A * B, C, 1, W₄, hPair, unitary_mul2 hA hB, hC,
          one4_unitary, hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂bc, hW₃ac, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A * B * C, 1, 1, W₄, hPair, unitary_mul3 hA hB hC,
          one4_unitary, one4_unitary, hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂bc, hW₃bc, mul_assoc] using hEq

/-- **Lemma 7.3** (Lifting the eigenvalue condition through `R`.)
If `(u₂, u₃) ∈ R(u₀, u₁)` and `u₂ = u₃ ∨ u₂ u₃ = 1`,
then `u₀ = u₁ ∨ u₀ u₁ = 1`. -/
lemma section7_lemma_7_3 (u₀ u₁ u₂ u₃ : ℂ)
    (hu₀ : ‖u₀‖ = 1) (_hu₁ : ‖u₁‖ = 1)
    (hR : inCanonicalPair u₀ u₁ u₂ u₃)
    (h : u₂ = u₃ ∨ u₂ * u₃ = 1) :
    u₀ = u₁ ∨ u₀ * u₁ = 1 := by
  rcases hR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa using h
  · rcases h with hEq | hMul
    · left
      have hu₀conj : starRingEnd ℂ u₀ * u₀ = 1 := by
        simp [Complex.conj_mul', hu₀]
      have hu₀' : u₀ * starRingEnd ℂ u₀ = 1 := by
        simpa [mul_comm] using hu₀conj
      calc
        u₀ = u₀ * 1 := by simp
        _ = u₀ * (starRingEnd ℂ u₀ * u₁) := by rw [hEq]
        _ = (u₀ * starRingEnd ℂ u₀) * u₁ := by simp [mul_assoc]
        _ = u₁ := by simp [hu₀']
    · left
      have hConj : starRingEnd ℂ u₀ * u₁ = 1 := by
        simpa using hMul
      have hu₀conj : starRingEnd ℂ u₀ * u₀ = 1 := by
        simp [Complex.conj_mul', hu₀]
      have hu₀' : u₀ * starRingEnd ℂ u₀ = 1 := by
        simpa [mul_comm] using hu₀conj
      calc
        u₀ = u₀ * 1 := by simp
        _ = u₀ * (starRingEnd ℂ u₀ * u₁) := by rw [hConj]
        _ = (u₀ * starRingEnd ℂ u₀) * u₁ := by simp [mul_assoc]
        _ = u₁ := by simp [hu₀']

/-- **Theorem 7.4** (Main result for a diagonal matrix.)
A product of four `TwoQubitGate`s equals `CC(Diag(u₀, u₁))`
if and only if `u₀ = u₁` or `u₀ u₁ = 1`. -/
theorem section7_theorem_7_4 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ V₁ V₂ V₃ V₄ : Square 8,
      TwoQubitGate V₁ ∧ TwoQubitGate V₂ ∧ TwoQubitGate V₃ ∧ TwoQubitGate V₄ ∧
      V₁ * V₂ * V₃ * V₄ = ccu (diag2 u₀ u₁)) ↔
    (u₀ = u₁ ∨ u₀ * u₁ = 1) := by
  constructor
  · rintro ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, hEq⟩
    rcases section7_lemma_7_2 u₀ u₁ hu₀ hu₁ V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ hEq with
      ⟨u₂, u₃, U₁, U₂, U₃, U₄, hPair, hU₁, hU₂, hU₃, hU₄, hCanon⟩
    have hu₂ : ‖u₂‖ = 1 := canonicalPair_first_norm u₀ u₁ u₂ u₃ hu₀ hPair
    have hu₃ : ‖u₃‖ = 1 := by
      rcases hPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa using hu₁
      · calc
          ‖starRingEnd ℂ u₀ * u₁‖ = ‖starRingEnd ℂ u₀‖ * ‖u₁‖ := norm_mul _ _
          _ = 1 := by simp [hu₀, hu₁]
    rcases hCanon with hLeft | hRight
    · have hScalar : u₂ = u₃ ∨ u₂ * u₃ = 1 :=
        (section5_lemma_5_1 u₂ u₃ hu₂ hu₃).1 <| by
          exact ⟨U₁, U₂, U₃, U₄, hU₁, hU₂, hU₃, hU₄, hLeft⟩
      exact section7_lemma_7_3 u₀ u₁ u₂ u₃ hu₀ hu₁ hPair hScalar
    · have hScalar : u₂ = u₃ ∨ u₂ * u₃ = 1 :=
        (section6_lemma_6_4 u₂ u₃ hu₂ hu₃).1 <| by
          exact ⟨U₁, U₂, U₃, U₄, hU₁, hU₂, hU₃, hU₄, hRight⟩
      exact section7_lemma_7_3 u₀ u₁ u₂ u₃ hu₀ hu₁ hPair hScalar
  · intro h
    rcases (section5_lemma_5_1 u₀ u₁ hu₀ hu₁).2 h with
      ⟨U₁, U₂, U₃, U₄, hU₁, hU₂, hU₃, hU₄, hEq⟩
    refine ⟨bcgate U₁, acgate U₂, abgate U₃, bcgate U₄, ?_, ?_, ?_, ?_, hEq⟩
    · exact ⟨U₁, hU₁, Or.inr <| Or.inr rfl⟩
    · exact ⟨U₂, hU₂, Or.inr <| Or.inl rfl⟩
    · exact ⟨U₃, hU₃, Or.inl rfl⟩
    · exact ⟨U₄, hU₄, Or.inr <| Or.inr rfl⟩

private lemma bcgate_localC_eq (R : Square 2) :
    bcgate ((1 : Square 2) ⊗ₖ R) = (1 : Square 4) ⊗ₖ R := by
  rw [bcgate_kron_two]
  simpa using congrArg (fun M => M ⊗ₖ R) (TwoControl.one_kron_one 2 2)

private lemma abgate_commute_localC (A : Square 4) (R : Square 2) :
    abgate A * bcgate ((1 : Square 2) ⊗ₖ R) =
      bcgate ((1 : Square 2) ⊗ₖ R) * abgate A := by
  calc
    abgate A * bcgate ((1 : Square 2) ⊗ₖ R)
        = (A ⊗ₖ (1 : Square 2)) * ((1 : Square 4) ⊗ₖ R) := by
            rw [abgate, bcgate_localC_eq]
    _ = (A * (1 : Square 4)) ⊗ₖ ((1 : Square 2) * R) := by
          rw [← kron_mul_reindex_local A (1 : Square 4) (1 : Square 2) R]
    _ = A ⊗ₖ R := by simp
    _ = ((1 : Square 4) * A) ⊗ₖ (R * (1 : Square 2)) := by simp
    _ = ((1 : Square 4) ⊗ₖ R) * (A ⊗ₖ (1 : Square 2)) := by
          rw [kron_mul_reindex_local (1 : Square 4) A R (1 : Square 2)]
    _ = bcgate ((1 : Square 2) ⊗ₖ R) * abgate A := by
          conv_rhs => rw [bcgate_localC_eq, abgate]

private lemma acgate_localC_eq (R : Square 2) :
    acgate ((1 : Square 2) ⊗ₖ R) = bcgate ((1 : Square 2) ⊗ₖ R) := by
  rw [acgate_kron_two, bcgate_kron_two, ← kron_assoc_222_local (1 : Square 2) (1 : Square 2) R]

private lemma localC_cancel_right (V : Square 2) (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ((1 : Square 2) ⊗ₖ V) * ((1 : Square 2) ⊗ₖ V†) = (1 : Square 4) := by
  have hVright : V * V† = (1 : Square 2) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hV)
  calc
    ((1 : Square 2) ⊗ₖ V) * ((1 : Square 2) ⊗ₖ V†)
        = ((1 : Square 2) * (1 : Square 2)) ⊗ₖ (V * V†) := by
            rw [← kron_mul_two]
    _ = (1 : Square 2) ⊗ₖ (1 : Square 2) := by simp [hVright]
    _ = (1 : Square 4) := by simpa using TwoControl.one_kron_one 2 2

private lemma localC_cancel_left (V : Square 2) (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ((1 : Square 2) ⊗ₖ V†) * ((1 : Square 2) ⊗ₖ V) = (1 : Square 4) := by
  have hVleft : V† * V = (1 : Square 2) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hV)
  calc
    ((1 : Square 2) ⊗ₖ V†) * ((1 : Square 2) ⊗ₖ V)
        = ((1 : Square 2) * (1 : Square 2)) ⊗ₖ (V† * V) := by
            rw [← kron_mul_two]
    _ = (1 : Square 2) ⊗ₖ (1 : Square 2) := by simp [hVleft]
    _ = (1 : Square 4) := by simpa using TwoControl.one_kron_one 2 2

private lemma bcgate_localC_cancel_right (V : Square 2) (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    bcgate ((1 : Square 2) ⊗ₖ V) * bcgate ((1 : Square 2) ⊗ₖ V†) = (1 : Square 8) := by
  rw [← bcgate_mul, localC_cancel_right V hV, bcgate_one]

private lemma bcgate_localC_cancel_left (V : Square 2) (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    bcgate ((1 : Square 2) ⊗ₖ V†) * bcgate ((1 : Square 2) ⊗ₖ V) = (1 : Square 8) := by
  rw [← bcgate_mul, localC_cancel_left V hV, bcgate_one]

private lemma bcgate_localC_conj_kron (P : Square 2) (B : Square 4) (V : Square 2) :
    bcgate ((1 : Square 2) ⊗ₖ V) * (P ⊗ₖ B) * bcgate ((1 : Square 2) ⊗ₖ V†) =
      P ⊗ₖ (((1 : Square 2) ⊗ₖ V) * B * ((1 : Square 2) ⊗ₖ V†)) := by
  unfold bcgate
  calc
    ((1 : Square 2) ⊗ₖ ((1 : Square 2) ⊗ₖ V)) * (P ⊗ₖ B) *
        ((1 : Square 2) ⊗ₖ ((1 : Square 2) ⊗ₖ V†))
        = (((1 : Square 2) * P) ⊗ₖ (((1 : Square 2) ⊗ₖ V) * B)) *
            ((1 : Square 2) ⊗ₖ ((1 : Square 2) ⊗ₖ V†)) := by
              rw [← kron_mul_reindex_local (1 : Square 2) P ((1 : Square 2) ⊗ₖ V) B]
    _ = ((((1 : Square 2) * P) * (1 : Square 2)) ⊗ₖ
          ((((1 : Square 2) ⊗ₖ V) * B) * ((1 : Square 2) ⊗ₖ V†))) := by
            rw [← kron_mul_reindex_local ((1 : Square 2) * P) (1 : Square 2)
              (((1 : Square 2) ⊗ₖ V) * B) ((1 : Square 2) ⊗ₖ V†)]
    _ = P ⊗ₖ (((1 : Square 2) ⊗ₖ V) * B * ((1 : Square 2) ⊗ₖ V†)) := by
          simp [mul_assoc]

private lemma controlledGate_conj_local_target (V U : Square 2)
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ((1 : Square 2) ⊗ₖ V) * controlledGate U * ((1 : Square 2) ⊗ₖ V†) =
      controlledGate (V * U * V†) := by
  have hVright : V * V† = (1 : Square 2) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hV)
  calc
    ((1 : Square 2) ⊗ₖ V) * controlledGate U * ((1 : Square 2) ⊗ₖ V†)
        = ((1 : Square 2) ⊗ₖ V) * (proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ U) *
            ((1 : Square 2) ⊗ₖ V†) := by rw [controlledGate]
    _ = ((1 : Square 2) ⊗ₖ V) * (proj0 ⊗ₖ (1 : Square 2)) * ((1 : Square 2) ⊗ₖ V†) +
          ((1 : Square 2) ⊗ₖ V) * (proj1 ⊗ₖ U) * ((1 : Square 2) ⊗ₖ V†) := by
            rw [Matrix.mul_add, Matrix.add_mul]
    _ = proj0 ⊗ₖ (V * (1 : Square 2) * V†) + proj1 ⊗ₖ (V * U * V†) := by
          congr
          · calc
              ((1 : Square 2) ⊗ₖ V) * (proj0 ⊗ₖ (1 : Square 2)) * ((1 : Square 2) ⊗ₖ V†)
                  = (((1 : Square 2) * proj0) ⊗ₖ (V * (1 : Square 2))) * ((1 : Square 2) ⊗ₖ V†) := by
                      rw [← kron_mul_reindex_local (1 : Square 2) proj0 V (1 : Square 2)]
              _ = ((((1 : Square 2) * proj0) * (1 : Square 2)) ⊗ₖ ((V * (1 : Square 2)) * V†)) := by
                    rw [← kron_mul_reindex_local ((1 : Square 2) * proj0) (1 : Square 2)
                      (V * (1 : Square 2)) V†]
              _ = proj0 ⊗ₖ (V * (1 : Square 2) * V†) := by simp
          · calc
              ((1 : Square 2) ⊗ₖ V) * (proj1 ⊗ₖ U) * ((1 : Square 2) ⊗ₖ V†)
                  = (((1 : Square 2) * proj1) ⊗ₖ (V * U)) * ((1 : Square 2) ⊗ₖ V†) := by
                      rw [← kron_mul_reindex_local (1 : Square 2) proj1 V U]
              _ = ((((1 : Square 2) * proj1) * (1 : Square 2)) ⊗ₖ ((V * U) * V†)) := by
                    rw [← kron_mul_reindex_local ((1 : Square 2) * proj1) (1 : Square 2)
                      (V * U) V†]
              _ = proj1 ⊗ₖ (V * U * V†) := by simp [mul_assoc]
    _ = proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ (V * U * V†) := by
          simp [hVright, mul_assoc]
    _ = controlledGate (V * U * V†) := by rw [controlledGate]

private lemma ccu_conj_local_target (V U : Square 2)
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    bcgate ((1 : Square 2) ⊗ₖ V) * ccu U * bcgate ((1 : Square 2) ⊗ₖ V†) =
      ccu (V * U * V†) := by
  calc
    bcgate ((1 : Square 2) ⊗ₖ V) * ccu U * bcgate ((1 : Square 2) ⊗ₖ V†)
        = bcgate ((1 : Square 2) ⊗ₖ V) *
            (proj0 ⊗ₖ (1 : Square 4) + proj1 ⊗ₖ controlledGate U) *
            bcgate ((1 : Square 2) ⊗ₖ V†) := by rw [ccu]
    _ = bcgate ((1 : Square 2) ⊗ₖ V) * (proj0 ⊗ₖ (1 : Square 4)) *
          bcgate ((1 : Square 2) ⊗ₖ V†) +
          bcgate ((1 : Square 2) ⊗ₖ V) * (proj1 ⊗ₖ controlledGate U) *
          bcgate ((1 : Square 2) ⊗ₖ V†) := by
            rw [Matrix.mul_add, Matrix.add_mul]
    _ = proj0 ⊗ₖ (((1 : Square 2) ⊗ₖ V) * (1 : Square 4) * ((1 : Square 2) ⊗ₖ V†)) +
          proj1 ⊗ₖ (((1 : Square 2) ⊗ₖ V) * controlledGate U * ((1 : Square 2) ⊗ₖ V†)) := by
            rw [bcgate_localC_conj_kron proj0 (1 : Square 4) V,
              bcgate_localC_conj_kron proj1 (controlledGate U) V]
    _ = proj0 ⊗ₖ (1 : Square 4) + proj1 ⊗ₖ controlledGate (V * U * V†) := by
          rw [controlledGate_conj_local_target V U hV]
          simp [localC_cancel_right V hV, mul_assoc]
    _ = ccu (V * U * V†) := by rw [ccu]

private lemma conj_local_target_twoQubitGate (V : Square 2)
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (X : Square 8) (hX : TwoQubitGate X) :
    TwoQubitGate (bcgate ((1 : Square 2) ⊗ₖ V) * X * bcgate ((1 : Square 2) ⊗ₖ V†)) := by
  have hVdag : V† ∈ Matrix.unitaryGroup (Fin 2) ℂ := conjTranspose_mem_unitaryGroup hV
  have hLocal : ((1 : Square 2) ⊗ₖ V) ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
    kron_unitary_two (1 : Square 2) V (Submonoid.one_mem _) hV
  have hLocalDag : ((1 : Square 2) ⊗ₖ V†) ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    exact kron_unitary_two (1 : Square 2) V† (Submonoid.one_mem _) hVdag
  rcases hX with ⟨A, hA, hEq | hEq | hEq⟩
  · refine ⟨A, hA, Or.inl ?_⟩
    rw [hEq]
    calc
      bcgate ((1 : Square 2) ⊗ₖ V) * abgate A * bcgate ((1 : Square 2) ⊗ₖ V†)
          = abgate A * (bcgate ((1 : Square 2) ⊗ₖ V) * bcgate ((1 : Square 2) ⊗ₖ V†)) := by
              rw [← abgate_commute_localC A V]
              simp [mul_assoc]
      _ = abgate A := by rw [bcgate_localC_cancel_right V hV]; simp
  · refine ⟨((1 : Square 2) ⊗ₖ V) * A * ((1 : Square 2) ⊗ₖ V†),
      unitary_mul3 hLocal hA hLocalDag, Or.inr <| Or.inl ?_⟩
    rw [hEq]
    calc
      bcgate ((1 : Square 2) ⊗ₖ V) * acgate A * bcgate ((1 : Square 2) ⊗ₖ V†)
          = acgate ((1 : Square 2) ⊗ₖ V) * acgate A * acgate ((1 : Square 2) ⊗ₖ V†) := by
              rw [← acgate_localC_eq, ← acgate_localC_eq]
      _ = acgate (((1 : Square 2) ⊗ₖ V) * A) * acgate ((1 : Square 2) ⊗ₖ V†) := by
            rw [← acgate_mul]
      _ = acgate (((1 : Square 2) ⊗ₖ V) * A * ((1 : Square 2) ⊗ₖ V†)) := by
            rw [← acgate_mul]
  · refine ⟨((1 : Square 2) ⊗ₖ V) * A * ((1 : Square 2) ⊗ₖ V†),
      unitary_mul3 hLocal hA hLocalDag, Or.inr <| Or.inr ?_⟩
    rw [hEq]
    calc
      bcgate ((1 : Square 2) ⊗ₖ V) * bcgate A * bcgate ((1 : Square 2) ⊗ₖ V†)
          = bcgate (((1 : Square 2) ⊗ₖ V) * A) * bcgate ((1 : Square 2) ⊗ₖ V†) := by
              rw [← bcgate_mul]
      _ = bcgate (((1 : Square 2) ⊗ₖ V) * A * ((1 : Square 2) ⊗ₖ V†)) := by
            rw [← bcgate_mul]

private lemma conj_local_target_product_four (V : Square 2)
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (X₁ X₂ X₃ X₄ : Square 8) :
    (bcgate ((1 : Square 2) ⊗ₖ V) * X₁ * bcgate ((1 : Square 2) ⊗ₖ V†)) *
        (bcgate ((1 : Square 2) ⊗ₖ V) * X₂ * bcgate ((1 : Square 2) ⊗ₖ V†)) *
        (bcgate ((1 : Square 2) ⊗ₖ V) * X₃ * bcgate ((1 : Square 2) ⊗ₖ V†)) *
        (bcgate ((1 : Square 2) ⊗ₖ V) * X₄ * bcgate ((1 : Square 2) ⊗ₖ V†)) =
      bcgate ((1 : Square 2) ⊗ₖ V) * (X₁ * X₂ * X₃ * X₄) * bcgate ((1 : Square 2) ⊗ₖ V†) := by
  calc
    (bcgate ((1 : Square 2) ⊗ₖ V) * X₁ * bcgate ((1 : Square 2) ⊗ₖ V†)) *
        (bcgate ((1 : Square 2) ⊗ₖ V) * X₂ * bcgate ((1 : Square 2) ⊗ₖ V†)) *
        (bcgate ((1 : Square 2) ⊗ₖ V) * X₃ * bcgate ((1 : Square 2) ⊗ₖ V†)) *
        (bcgate ((1 : Square 2) ⊗ₖ V) * X₄ * bcgate ((1 : Square 2) ⊗ₖ V†))
        = bcgate ((1 : Square 2) ⊗ₖ V) * X₁ *
            (bcgate ((1 : Square 2) ⊗ₖ V†) * bcgate ((1 : Square 2) ⊗ₖ V)) * X₂ *
            (bcgate ((1 : Square 2) ⊗ₖ V†) * bcgate ((1 : Square 2) ⊗ₖ V)) * X₃ *
            (bcgate ((1 : Square 2) ⊗ₖ V†) * bcgate ((1 : Square 2) ⊗ₖ V)) * X₄ *
            bcgate ((1 : Square 2) ⊗ₖ V†) := by
              simp [mul_assoc]
    _ = bcgate ((1 : Square 2) ⊗ₖ V) * X₁ * X₂ * X₃ * X₄ * bcgate ((1 : Square 2) ⊗ₖ V†) := by
          simp [bcgate_localC_cancel_left V hV, mul_assoc]
    _ = bcgate ((1 : Square 2) ⊗ₖ V) * (X₁ * X₂ * X₃ * X₄) * bcgate ((1 : Square 2) ⊗ₖ V†) := by
          simp [mul_assoc]

private lemma diag2_same_eq_smul_one_local (a : ℂ) :
    diag2 a a = a • (1 : Square 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2]

private lemma det_of_unitary_diag2_decomp_local {A : Square 2} {a b : ℂ} {W : Square 2}
    (hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hA : A = W * diag2 a b * W†) :
    A.det = a * b := by
  have hdetW : W.det * star W.det = 1 := by
    exact (Unitary.mem_iff_self_mul_star).mp (Matrix.det_of_mem_unitary hW)
  calc
    A.det = (W * diag2 a b * W†).det := by rw [hA]
    _ = W.det * (diag2 a b).det * star W.det := by
          rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    _ = (W.det * star W.det) * (a * b) := by
          simp [diag2, Matrix.det_diagonal]
          ring
    _ = a * b := by rw [hdetW, one_mul]

/-- **Corollary 7.5** (Main result for a gate with two controls.)
A product of four `TwoQubitGate`s equals `CC(U)` for a 1-qubit unitary `U`
if and only if `U` is a scalar matrix or `det U = 1`. -/
theorem section7_corollary_7_5 (U : Square 2) (hU : U ∈ unitaryGroup (Fin 2) ℂ) :
    (∃ V₁ V₂ V₃ V₄ : Square 8,
      TwoQubitGate V₁ ∧ TwoQubitGate V₂ ∧ TwoQubitGate V₃ ∧ TwoQubitGate V₄ ∧
      V₁ * V₂ * V₃ * V₄ = ccu U) ↔
    ((∃ c : ℂ, U = c • (1 : Square 2)) ∨ det U = 1) := by
  rcases unitary_diag2_exists U hU with ⟨u₀, u₁, V, hu₀, hu₁, hV, hdiag⟩
  have hVdag : V† ∈ Matrix.unitaryGroup (Fin 2) ℂ := conjTranspose_mem_unitaryGroup hV
  have hVright : V * V† = (1 : Square 2) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hV)
  have hVleft : V† * V = (1 : Square 2) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hV)
  have hconjDiag : V† * U * V = diag2 u₀ u₁ := by
    calc
      V† * U * V = V† * (V * diag2 u₀ u₁ * V†) * V := by rw [hdiag]
      _ = (V† * V) * diag2 u₀ u₁ * (V† * V) := by simp [mul_assoc]
      _ = diag2 u₀ u₁ := by simp [hVleft]
  constructor
  · rintro ⟨X₁, X₂, X₃, X₄, hX₁, hX₂, hX₃, hX₄, hEq⟩
    have hDiagDecomp :
        ∃ W₁ W₂ W₃ W₄ : Square 8,
          TwoQubitGate W₁ ∧ TwoQubitGate W₂ ∧ TwoQubitGate W₃ ∧ TwoQubitGate W₄ ∧
          W₁ * W₂ * W₃ * W₄ = ccu (diag2 u₀ u₁) := by
      refine ⟨
        bcgate ((1 : Square 2) ⊗ₖ V†) * X₁ * bcgate ((1 : Square 2) ⊗ₖ V),
        bcgate ((1 : Square 2) ⊗ₖ V†) * X₂ * bcgate ((1 : Square 2) ⊗ₖ V),
        bcgate ((1 : Square 2) ⊗ₖ V†) * X₃ * bcgate ((1 : Square 2) ⊗ₖ V),
        bcgate ((1 : Square 2) ⊗ₖ V†) * X₄ * bcgate ((1 : Square 2) ⊗ₖ V),
        ?_, ?_, ?_, ?_, ?_⟩
      · simpa using (conj_local_target_twoQubitGate V† hVdag X₁ hX₁)
      · simpa using (conj_local_target_twoQubitGate V† hVdag X₂ hX₂)
      · simpa using (conj_local_target_twoQubitGate V† hVdag X₃ hX₃)
      · simpa using (conj_local_target_twoQubitGate V† hVdag X₄ hX₄)
      · calc
          (bcgate ((1 : Square 2) ⊗ₖ V†) * X₁ * bcgate ((1 : Square 2) ⊗ₖ V)) *
              (bcgate ((1 : Square 2) ⊗ₖ V†) * X₂ * bcgate ((1 : Square 2) ⊗ₖ V)) *
              (bcgate ((1 : Square 2) ⊗ₖ V†) * X₃ * bcgate ((1 : Square 2) ⊗ₖ V)) *
              (bcgate ((1 : Square 2) ⊗ₖ V†) * X₄ * bcgate ((1 : Square 2) ⊗ₖ V))
              = bcgate ((1 : Square 2) ⊗ₖ V†) * (X₁ * X₂ * X₃ * X₄) *
                  bcgate ((1 : Square 2) ⊗ₖ V) := by
                    simpa using (conj_local_target_product_four V† hVdag X₁ X₂ X₃ X₄)
          _ = bcgate ((1 : Square 2) ⊗ₖ V†) * ccu U * bcgate ((1 : Square 2) ⊗ₖ V) := by
                rw [hEq]
          _ = ccu (diag2 u₀ u₁) := by
                simpa [hconjDiag] using (ccu_conj_local_target V† U hVdag)
    rcases (section7_theorem_7_4 u₀ u₁ hu₀ hu₁).1 hDiagDecomp with hEqual | hMul
    · left
      refine ⟨u₀, ?_⟩
      calc
        U = V * diag2 u₀ u₀ * V† := by simpa [hEqual] using hdiag
        _ = V * (u₀ • (1 : Square 2)) * V† := by rw [diag2_same_eq_smul_one_local]
        _ = u₀ • (V * (1 : Square 2) * V†) := by simp []
        _ = u₀ • (1 : Square 2) := by simp [hVright]
    · right
      calc
        det U = u₀ * u₁ := det_of_unitary_diag2_decomp_local hV hdiag
        _ = 1 := hMul
  · intro h
    have hDiagCond : u₀ = u₁ ∨ u₀ * u₁ = 1 := by
      rcases h with hScalar | hDet
      · rcases hScalar with ⟨c, hScalar⟩
        have hDiagScalar : diag2 u₀ u₁ = c • (1 : Square 2) := by
          calc
            diag2 u₀ u₁ = V† * U * V := by symm; exact hconjDiag
            _ = V† * (c • (1 : Square 2)) * V := by rw [hScalar]
            _ = c • (V† * (1 : Square 2) * V) := by simp []
            _ = c • (1 : Square 2) := by simp [hVleft,]
        have hu0c : u₀ = c := by
          have h00 := congrArg (fun M : Square 2 => M 0 0) hDiagScalar
          simpa [diag2] using h00
        have hu1c : u₁ = c := by
          have h11 := congrArg (fun M : Square 2 => M 1 1) hDiagScalar
          simpa [diag2] using h11
        exact Or.inl (by rw [hu0c, hu1c])
      · right
        calc
          u₀ * u₁ = det U := by symm; exact det_of_unitary_diag2_decomp_local hV hdiag
          _ = 1 := hDet
    rcases (section7_theorem_7_4 u₀ u₁ hu₀ hu₁).2 hDiagCond with
      ⟨X₁, X₂, X₃, X₄, hX₁, hX₂, hX₃, hX₄, hEqDiag⟩
    refine ⟨
      bcgate ((1 : Square 2) ⊗ₖ V) * X₁ * bcgate ((1 : Square 2) ⊗ₖ V†),
      bcgate ((1 : Square 2) ⊗ₖ V) * X₂ * bcgate ((1 : Square 2) ⊗ₖ V†),
      bcgate ((1 : Square 2) ⊗ₖ V) * X₃ * bcgate ((1 : Square 2) ⊗ₖ V†),
      bcgate ((1 : Square 2) ⊗ₖ V) * X₄ * bcgate ((1 : Square 2) ⊗ₖ V†),
      conj_local_target_twoQubitGate V hV X₁ hX₁,
      conj_local_target_twoQubitGate V hV X₂ hX₂,
      conj_local_target_twoQubitGate V hV X₃ hX₃,
      conj_local_target_twoQubitGate V hV X₄ hX₄,
      ?_⟩
    calc
      (bcgate ((1 : Square 2) ⊗ₖ V) * X₁ * bcgate ((1 : Square 2) ⊗ₖ V†)) *
          (bcgate ((1 : Square 2) ⊗ₖ V) * X₂ * bcgate ((1 : Square 2) ⊗ₖ V†)) *
          (bcgate ((1 : Square 2) ⊗ₖ V) * X₃ * bcgate ((1 : Square 2) ⊗ₖ V†)) *
          (bcgate ((1 : Square 2) ⊗ₖ V) * X₄ * bcgate ((1 : Square 2) ⊗ₖ V†))
          = bcgate ((1 : Square 2) ⊗ₖ V) * (X₁ * X₂ * X₃ * X₄) *
              bcgate ((1 : Square 2) ⊗ₖ V†) := by
                exact conj_local_target_product_four V hV X₁ X₂ X₃ X₄
      _ = bcgate ((1 : Square 2) ⊗ₖ V) * ccu (diag2 u₀ u₁) * bcgate ((1 : Square 2) ⊗ₖ V†) := by
            rw [hEqDiag]
      _ = ccu U := by
            simpa [hdiag] using (ccu_conj_local_target V (diag2 u₀ u₁) hV)

end TwoControl

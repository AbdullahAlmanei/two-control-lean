import TwoControl.BlockHelpers
import TwoControl.DiagonalizationHelpers
import TwoControl.KronHelpers
import TwoControl.SwapHelpers
import TwoControl.GateHelpers
import TwoControl.Section6

open scoped Matrix ComplexOrder
open Matrix

namespace TwoControl

open BlockHelpers
open KronHelpers
open SwapHelpers
open GateHelpers
open DiagonalizationHelpers

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

@[simp] private lemma acgate_one : acgate (1 : Square 4) = (1 : Square 8) := by
  unfold acgate abgate
  rw [TwoControl.one_kron_one 4 2]
  simp [swapbc_mul_swapbc]

@[simp] private lemma bcgate_swap2_eq : bcgate swap2 = swapbc := by
  rfl

@[simp] private lemma abgate_swap2_eq : abgate swap2 = swapab := by
  rfl

@[simp] private lemma acgate_swap2_eq : acgate swap2 = swapac := by
  rfl

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
  simp [swap2_mul_swap2, swap2_conj_diag4_one]

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
            _ = B := by simp [swap2_mul_swap2]
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
      · refine ⟨u₂, u₃, 1, 1, A * B * C, W₄, hPair, Submonoid.one_mem _,
          Submonoid.one_mem _, Submonoid.mul_mem _ (Submonoid.mul_mem _ hA hB) hC,
          hW₄, Or.inl ?_⟩
        simpa [hW₁ab, hW₂ab, hW₃ab, mul_assoc] using hEq
      · have hStart :
          ccu (diag2 u₂ u₃) = abgate (A * B) * (acgate C * bcgate W₄) := by
          calc
            ccu (diag2 u₂ u₃) = W₁ * W₂ * W₃ * bcgate W₄ := by simpa using hEq.symm
            _ = abgate A * abgate B * acgate C * bcgate W₄ := by
                  rw [hW₁ab, hW₂ab, hW₃ac]
            _ = abgate (A * B) * (acgate C * bcgate W₄) := by
                  simp [mul_assoc]
        rcases section7_lemma_7_1_left u₂ u₃ hu₂ (A * B) (Submonoid.mul_mem _ hA hB)
          (acgate C * bcgate W₄) hStart with ⟨V, hV, hVeq⟩
        have hWord :
            abgate V * acgate C * bcgate W₄ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by
          simpa [mul_assoc] using hVeq.symm
        refine ⟨1, starRingEnd ℂ u₂ * u₃, V, swap2, C, W₄ * swap2, hPairStep,
          hV, swap2_unitary, hC, Submonoid.mul_mem _ hW₄ swap2_unitary, Or.inr ?_⟩
        calc
          acgate V * bcgate swap2 * acgate C * bcgate (W₄ * swap2)
              = swapbc * (abgate V * acgate C * bcgate W₄) * swapbc := by
                  symm
                  exact swapbc_conj_word_abacbc V C W₄
          _ = swapbc * ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) * swapbc := by rw [hWord]
          _ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := by rw [swapbc_conj_ccu_diag2_one]
      · refine ⟨u₂, u₃, 1, 1, A * B, C * W₄, hPair, Submonoid.one_mem _,
          Submonoid.one_mem _, Submonoid.mul_mem _ hA hB, Submonoid.mul_mem _ hC hW₄,
          Or.inl ?_⟩
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
          swap2 * W₄ * swap2, hPairStep, Submonoid.mul_mem _ hV swap2_unitary,
          swap2_conj_unitary hB, Submonoid.mul_mem _ swap2_unitary hC,
          swap2_conj_unitary hW₄, Or.inr ?_⟩
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
          hV, swap2_unitary, Submonoid.mul_mem _ hB hC,
          Submonoid.mul_mem _ hW₄ swap2_unitary, Or.inr ?_⟩
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
          hV, swap2_unitary, hB,
          Submonoid.mul_mem _ (Submonoid.mul_mem _ hC hW₄) swap2_unitary, Or.inr ?_⟩
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
          hV, Submonoid.mul_mem _ swap2_unitary hB, hC,
          Submonoid.mul_mem _ hW₄ swap2_unitary, Or.inr ?_⟩
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
                simp [mul_assoc, swap2_mul_swap2]
              have hWnorm : swap2 * (swap2 * W₄ * swap2) = W₄ * swap2 := by
                calc
                  swap2 * (swap2 * W₄ * swap2) = (swap2 * swap2) * (W₄ * swap2) := by
                      simp [mul_assoc]
                  _ = W₄ * swap2 := by
                        rw [swap2_mul_swap2]
                        simp
              rw [hBnorm, hWnorm]
        calc
          acgate V * bcgate (swap2 * B) * acgate C * bcgate (W₄ * swap2)
              = acgate V * bcgate (swap2 * B * swap2) * abgate C * bcgate (swap2 * W₄ * swap2) :=
                  hNorm.symm
          _ = ccu (diag2 1 (starRingEnd ℂ u₂ * u₃)) := hConj
      · refine ⟨u₂, u₃, 1, 1, A, B * C * W₄, hPair, Submonoid.one_mem _,
          Submonoid.one_mem _, hA, Submonoid.mul_mem _ (Submonoid.mul_mem _ hB hC) hW₄,
          Or.inl ?_⟩
        simpa [hW₁ab, hW₂bc, hW₃bc, mul_assoc] using hEq
  · rcases hW₂ with ⟨B, hB, hW₂ab | hW₂ac | hW₂bc⟩
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · refine ⟨u₂, u₃, 1, A, B * C, W₄, hPair, Submonoid.one_mem _, hA,
          Submonoid.mul_mem _ hB hC, hW₄, Or.inl ?_⟩
        simpa [hW₁ac, hW₂ab, hW₃ab, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A * swap2, swap2 * B * swap2, swap2 * C, W₄, hPair,
          Submonoid.mul_mem _ hA swap2_unitary, swap2_conj_unitary hB,
          Submonoid.mul_mem _ swap2_unitary hC, hW₄, Or.inr ?_⟩
        calc
          acgate (A * swap2) * bcgate (swap2 * B * swap2) * acgate (swap2 * C) * bcgate W₄
              = acgate A * abgate B * acgate C * bcgate W₄ := by
                  symm
                  exact normalize_word_acabac A B C W₄
          _ = ccu (diag2 u₂ u₃) := by simpa [hW₁ac, hW₂ab, hW₃ac, mul_assoc] using hEq
      · refine ⟨u₂, u₃, 1, A, B, C * W₄, hPair, Submonoid.one_mem _, hA, hB,
          Submonoid.mul_mem _ hC hW₄, Or.inl ?_⟩
        simpa [hW₁ac, hW₂ab, hW₃bc, mul_assoc] using hEq
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · refine ⟨u₂, u₃, 1, A * B, C, W₄, hPair, Submonoid.one_mem _,
          Submonoid.mul_mem _ hA hB, hC, hW₄, Or.inl ?_⟩
        simpa [hW₁ac, hW₂ac, hW₃ab, mul_assoc] using hEq
      · refine ⟨u₂, u₃, 1, A * B * C, 1, W₄, hPair, Submonoid.one_mem _,
          Submonoid.mul_mem _ (Submonoid.mul_mem _ hA hB) hC, Submonoid.one_mem _,
          hW₄, Or.inl ?_⟩
        simpa [hW₁ac, hW₂ac, hW₃ac, mul_assoc] using hEq
      · refine ⟨u₂, u₃, 1, A * B, 1, C * W₄, hPair, Submonoid.one_mem _,
          Submonoid.mul_mem _ hA hB, Submonoid.one_mem _, Submonoid.mul_mem _ hC hW₄,
          Or.inl ?_⟩
        simpa [hW₁ac, hW₂ac, hW₃bc, mul_assoc] using hEq
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · refine ⟨u₂, u₃, A, B * swap2, C, swap2 * W₄, hPair, hA,
          Submonoid.mul_mem _ hB swap2_unitary, hC,
          Submonoid.mul_mem _ swap2_unitary hW₄, Or.inr ?_⟩
        calc
          acgate A * bcgate (B * swap2) * acgate C * bcgate (swap2 * W₄)
              = acgate A * bcgate B * abgate C * bcgate W₄ := by
                  symm
                  exact normalize_word_acbcab A B C W₄
          _ = ccu (diag2 u₂ u₃) := by simpa [hW₁ac, hW₂bc, hW₃ab, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A, B, C, W₄, hPair, hA, hB, hC, hW₄, Or.inr ?_⟩
        simpa [hW₁ac, hW₂bc, hW₃ac, mul_assoc] using hEq
      · refine ⟨u₂, u₃, 1, A, 1, B * C * W₄, hPair, Submonoid.one_mem _, hA,
          Submonoid.one_mem _, Submonoid.mul_mem _ (Submonoid.mul_mem _ hB hC) hW₄,
          Or.inl ?_⟩
        simpa [hW₁ac, hW₂bc, hW₃bc, mul_assoc] using hEq
  · rcases hW₂ with ⟨B, hB, hW₂ab | hW₂ac | hW₂bc⟩
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · refine ⟨u₂, u₃, A, 1, B * C, W₄, hPair, hA, Submonoid.one_mem _,
          Submonoid.mul_mem _ hB hC, hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂ab, hW₃ab, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A * swap2, B, C, swap2 * W₄, hPair,
          Submonoid.mul_mem _ hA swap2_unitary, hB, hC,
          Submonoid.mul_mem _ swap2_unitary hW₄, Or.inl ?_⟩
        calc
          bcgate (A * swap2) * acgate B * abgate C * bcgate (swap2 * W₄)
              = bcgate A * abgate B * acgate C * bcgate W₄ := by
                  symm
                  exact normalize_word_bcabac A B C W₄
          _ = ccu (diag2 u₂ u₃) := by simpa [hW₁bc, hW₂ab, hW₃ac, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A, 1, B, C * W₄, hPair, hA, Submonoid.one_mem _, hB,
          Submonoid.mul_mem _ hC hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂ab, hW₃bc, mul_assoc] using hEq
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · refine ⟨u₂, u₃, A, B, C, W₄, hPair, hA, hB, hC, hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂ac, hW₃ab, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A, B * C, 1, W₄, hPair, hA, Submonoid.mul_mem _ hB hC,
          Submonoid.one_mem _, hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂ac, hW₃ac, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A, B, 1, C * W₄, hPair, hA, hB, Submonoid.one_mem _,
          Submonoid.mul_mem _ hC hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂ac, hW₃bc, mul_assoc] using hEq
    · rcases hW₃ with ⟨C, hC, hW₃ab | hW₃ac | hW₃bc⟩
      · refine ⟨u₂, u₃, A * B, 1, C, W₄, hPair, Submonoid.mul_mem _ hA hB,
          Submonoid.one_mem _, hC, hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂bc, hW₃ab, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A * B, C, 1, W₄, hPair, Submonoid.mul_mem _ hA hB, hC,
          Submonoid.one_mem _, hW₄, Or.inl ?_⟩
        simpa [hW₁bc, hW₂bc, hW₃ac, mul_assoc] using hEq
      · refine ⟨u₂, u₃, A * B * C, 1, 1, W₄, hPair,
          Submonoid.mul_mem _ (Submonoid.mul_mem _ hA hB) hC,
          Submonoid.one_mem _, Submonoid.one_mem _, hW₄, Or.inl ?_⟩
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
        _ = V * (u₀ • (1 : Square 2)) * V† := by rw [diag2_same_eq_smul_one]
        _ = u₀ • (V * (1 : Square 2) * V†) := by simp []
        _ = u₀ • (1 : Square 2) := by simp [hVright]
    · right
      calc
        det U = u₀ * u₁ := det_of_unitary_diag2_decomp hV hdiag
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
          u₀ * u₁ = det U := by symm; exact det_of_unitary_diag2_decomp hV hdiag
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

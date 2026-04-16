import TwoControl.DiagonalizationHelpers
import TwoControl.SwapHelpers

open scoped Matrix ComplexOrder
open Matrix

namespace TwoControl

/-! ### Gate transport helper lemmas -/

namespace GateHelpers

def notc : Square 4 :=
  Matrix.of ![![1, 0, 0, 0],
              ![0, 0, 0, 1],
              ![0, 0, 1, 0],
              ![0, 1, 0, 0]]

lemma notc_conjTranspose : notc† = notc := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [notc]

lemma notc_mul_notc : notc * notc = (1 : Square 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [notc]

lemma notc_unitary : notc ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, show star notc = notc by
    simpa [star_eq_conjTranspose] using notc_conjTranspose, notc_mul_notc]

lemma notc_conj_diag4 (a b c d : ℂ) :
    notc * diag4 a b c d * notc† = diag4 a d c b := by
  rw [notc_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ, notc, diag4]

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

lemma unitary_column0_norm (Q : Square 2)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    star ((Q.mulVec ket0) 0) * (Q.mulVec ket0) 0 +
      star ((Q.mulVec ket0) 1) * (Q.mulVec ket0) 1 = 1 := by
  have hleft : Q† * Q = 1 := by
    simpa using (Matrix.mem_unitaryGroup_iff'.mp hQ)
  simpa [Matrix.mul_apply, Matrix.mulVec, ket0, Matrix.one_apply] using
    congrFun (congrFun hleft 0) 0

lemma unitary_column1_norm (Q : Square 2)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    star ((Q.mulVec ket1) 0) * (Q.mulVec ket1) 0 +
      star ((Q.mulVec ket1) 1) * (Q.mulVec ket1) 1 = 1 := by
  have hleft : Q† * Q = 1 := by
    simpa using (Matrix.mem_unitaryGroup_iff'.mp hQ)
  simpa [Matrix.mul_apply, Matrix.mulVec, ket1, Matrix.one_apply] using
    congrFun (congrFun hleft 1) 1

lemma unitary_columns_orthogonal_left (Q : Square 2)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    star ((Q.mulVec ket1) 0) * (Q.mulVec ket0) 0 +
      star ((Q.mulVec ket1) 1) * (Q.mulVec ket0) 1 = 0 := by
  have hleft : Q† * Q = 1 := by
    simpa using (Matrix.mem_unitaryGroup_iff'.mp hQ)
  simpa [Matrix.mul_apply, Matrix.mulVec, ket0, ket1, Matrix.one_apply] using
    congrFun (congrFun hleft 1) 0

lemma unitary_columns_orthogonal_right (Q : Square 2)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    star ((Q.mulVec ket0) 0) * (Q.mulVec ket1) 0 +
      star ((Q.mulVec ket0) 1) * (Q.mulVec ket1) 1 = 0 := by
  have hleft : Q† * Q = 1 := by
    simpa using (Matrix.mem_unitaryGroup_iff'.mp hQ)
  simpa [Matrix.mul_apply, Matrix.mulVec, ket0, ket1, Matrix.one_apply] using
    congrFun (congrFun hleft 0) 1

lemma unitary_column_projector_sum (Q : Square 2)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ketbra (Q.mulVec ket0) (Q.mulVec ket0) + ketbra (Q.mulVec ket1) (Q.mulVec ket1) = (1 : Square 2) := by
  have hright : Q * Q† = 1 := by
    simpa using (Matrix.mem_unitaryGroup_iff.mp hQ)
  calc
    ketbra (Q.mulVec ket0) (Q.mulVec ket0) + ketbra (Q.mulVec ket1) (Q.mulVec ket1) = Q * Q† := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ketbra, Matrix.vecMulVec, Matrix.mul_apply, mulVec_ket0_apply, mulVec_ket1_apply]
    _ = 1 := hright

lemma ketbra_mulVec (v w x : Vec 2) :
    (ketbra v w).mulVec x = (star w ⬝ᵥ x) • v := by
  ext i
  fin_cases i <;>
    simp [ketbra, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
      mul_add, mul_left_comm, mul_comm]

lemma ketbra_self_mulVec_of_dotProduct_eq_one {β : Vec 2}
    (hβ : star β ⬝ᵥ β = 1) :
    (ketbra β β).mulVec β = β := by
  rw [ketbra_mulVec]
  simp [hβ]

lemma ketbra_orthogonal_mulVec {β γ : Vec 2}
    (h : star γ ⬝ᵥ β = 0) :
    (ketbra γ γ).mulVec β = 0 := by
  rw [ketbra_mulVec]
  simp [h]

lemma ketbra_eq_proj1_of_first_zero {β : Vec 2}
    (ha : β 0 = 0) (hb : star (β 1) * β 1 = 1) :
    ketbra β β = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ketbra, proj1, Matrix.vecMulVec_apply, ket1, ha]
  simpa [mul_comm] using hb

lemma ketbra_eq_proj0_of_second_zero {β : Vec 2}
    (hb : β 1 = 0) (ha : star (β 0) * β 0 = 1) :
    ketbra β β = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ketbra, proj0, Matrix.vecMulVec_apply, ket0, hb]
  simpa [mul_comm] using ha

@[simp] lemma acgate_add (U W : Square 4) :
    acgate (U + W) = acgate U + acgate W := by
  unfold acgate abgate
  rw [kron_add_left, Matrix.mul_add, Matrix.add_mul]

@[simp] lemma bcgate_add (U W : Square 4) :
    bcgate (U + W) = bcgate U + bcgate W := by
  unfold bcgate
  exact KronHelpers.kron_add_right (1 : Square 2) U W

lemma bcgate_kron_two (X A : Square 2) :
    bcgate (X ⊗ₖ A) = ((1 : Square 2) ⊗ₖ X) ⊗ₖ A := by
  unfold bcgate
  exact (KronHelpers.kron_assoc_222 (1 : Square 2) X A).symm

lemma acgate_kron_two (X A : Square 2) :
    acgate (X ⊗ₖ A) = X ⊗ₖ ((1 : Square 2) ⊗ₖ A) := by
  unfold acgate swapbc abgate
  calc
    ((1 : Square 2) ⊗ₖ swap2) * ((X ⊗ₖ A) ⊗ₖ (1 : Square 2)) * ((1 : Square 2) ⊗ₖ swap2)
        = ((1 : Square 2) ⊗ₖ swap2) * (X ⊗ₖ (A ⊗ₖ (1 : Square 2))) * ((1 : Square 2) ⊗ₖ swap2) := by
          rw [KronHelpers.kron_assoc_222 X A (1 : Square 2)]
    _ = (((1 : Square 2) * X) ⊗ₖ (swap2 * (A ⊗ₖ (1 : Square 2)))) * ((1 : Square 2) ⊗ₖ swap2) := by
          rw [← KronHelpers.kron_mul_reindex (1 : Square 2) X swap2 (A ⊗ₖ (1 : Square 2))]
    _ = (X ⊗ₖ (swap2 * (A ⊗ₖ (1 : Square 2)))) * ((1 : Square 2) ⊗ₖ swap2) := by
          simp
    _ = (X * (1 : Square 2)) ⊗ₖ ((swap2 * (A ⊗ₖ (1 : Square 2))) * swap2) := by
          rw [← KronHelpers.kron_mul_reindex X (1 : Square 2) (swap2 * (A ⊗ₖ (1 : Square 2))) swap2]
    _ = X ⊗ₖ ((swap2 * (A ⊗ₖ (1 : Square 2))) * swap2) := by
          simp
    _ = X ⊗ₖ ((1 : Square 2) ⊗ₖ A) := by
          rw [SwapHelpers.swap2_conj_kron_right]

lemma swapab_conj_bcgate_kron_two (X A : Square 2) :
    swapab * bcgate (X ⊗ₖ A) * swapab = acgate (X ⊗ₖ A) := by
  unfold swapab
  rw [bcgate_kron_two, acgate_kron_two]
  calc
    (swap2 ⊗ₖ (1 : Square 2)) * (((1 : Square 2) ⊗ₖ X) ⊗ₖ A) * (swap2 ⊗ₖ (1 : Square 2))
        = ((swap2 * ((1 : Square 2) ⊗ₖ X)) ⊗ₖ A) * (swap2 ⊗ₖ (1 : Square 2)) := by
          rw [← KronHelpers.kron_mul_reindex swap2 ((1 : Square 2) ⊗ₖ X) (1 : Square 2) A]
          simp
    _ = ((swap2 * ((1 : Square 2) ⊗ₖ X)) * swap2) ⊗ₖ (A * (1 : Square 2)) := by
          rw [← KronHelpers.kron_mul_reindex (swap2 * ((1 : Square 2) ⊗ₖ X)) swap2 A (1 : Square 2)]
    _ = (X ⊗ₖ (1 : Square 2)) ⊗ₖ A := by
          rw [SwapHelpers.swap2_conj_kron_left]
          simp
    _ = X ⊗ₖ ((1 : Square 2) ⊗ₖ A) := by
          rw [KronHelpers.kron_assoc_222 X (1 : Square 2) A]

lemma swapab_conj_acgate_kron_two (X A : Square 2) :
    swapab * acgate (X ⊗ₖ A) * swapab = bcgate (X ⊗ₖ A) := by
  unfold swapab
  rw [acgate_kron_two, bcgate_kron_two]
  calc
    (swap2 ⊗ₖ (1 : Square 2)) * (X ⊗ₖ ((1 : Square 2) ⊗ₖ A)) * (swap2 ⊗ₖ (1 : Square 2))
        = (swap2 ⊗ₖ (1 : Square 2)) * ((X ⊗ₖ (1 : Square 2)) ⊗ₖ A) * (swap2 ⊗ₖ (1 : Square 2)) := by
          rw [← KronHelpers.kron_assoc_222 X (1 : Square 2) A]
    _ = ((swap2 * (X ⊗ₖ (1 : Square 2))) ⊗ₖ A) * (swap2 ⊗ₖ (1 : Square 2)) := by
          rw [← KronHelpers.kron_mul_reindex swap2 (X ⊗ₖ (1 : Square 2)) (1 : Square 2) A]
          simp
    _ = ((swap2 * (X ⊗ₖ (1 : Square 2))) * swap2) ⊗ₖ (A * (1 : Square 2)) := by
          rw [← KronHelpers.kron_mul_reindex (swap2 * (X ⊗ₖ (1 : Square 2))) swap2 A (1 : Square 2)]
    _ = ((1 : Square 2) ⊗ₖ X) ⊗ₖ A := by
          rw [SwapHelpers.swap2_conj_kron_right]
          simp

lemma blockify_bcgate (U : Square 4) :
    blockify (n := 4) (bcgate U) = Matrix.fromBlocks U 0 0 U := by
  unfold bcgate
  rw [← BlockHelpers.proj0_add_proj1, kron_add_left, blockify_add, blockify_proj0_kron, blockify_proj1_kron]
  simp [Matrix.fromBlocks_add]

lemma blockify_acgate (U : Square 4) :
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

lemma blockify_abgate (U : Square 4) :
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
    repeat rw [KronHelpers.kron_assoc_222]
    simpa using
      (blockify_blockExpansion (A ⊗ₖ (1 : Square 2)) (B ⊗ₖ (1 : Square 2))
        (C ⊗ₖ (1 : Square 2)) (D ⊗ₖ (1 : Square 2)))
  dsimp [A, B, C, D, Ub] at hBlocks ⊢
  exact hBlocks

lemma blockify_controlledGate (P : Square 2) :
    blockify (n := 2) (controlledGate P) = Matrix.fromBlocks (1 : Square 2) 0 0 P := by
  unfold controlledGate
  rw [blockify_add, blockify_proj0_kron, blockify_proj1_kron]
  simp [Matrix.fromBlocks_add]

lemma controlledGate_unitary (P : Square 2)
    (hP : P ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    controlledGate P ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  apply (blockify_mem_unitaryGroup_iff (n := 2) (U := controlledGate P)).1
  unfold controlledGate
  rw [blockify_add, blockify_proj0_kron, blockify_proj1_kron]
  simpa [Matrix.fromBlocks_add, BlockHelpers.block_one_eq] using
    (BlockHelpers.fromBlocks_diagonal_unitary (1 : Square 2) P (Submonoid.one_mem _) hP)

@[simp] private lemma proj0_conjTranspose : (proj0 : Square 2)† = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, ketbra, ket0]

@[simp] private lemma proj1_conjTranspose : (proj1 : Square 2)† = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, ketbra, ket1]

@[simp] private lemma abgate_conjTranspose (U : Square 4) : (abgate U)† = abgate U† := by
  unfold abgate
  rw [KronHelpers.conjTranspose_kron_reindex]
  simp

private lemma swapbc_conjTranspose : swapbc† = swapbc := by
  unfold swapbc
  rw [KronHelpers.conjTranspose_kron_reindex, SwapHelpers.swap2_conjTranspose]
  simp

@[simp] private lemma bcgate_conjTranspose (U : Square 4) : (bcgate U)† = bcgate U† := by
  unfold bcgate
  rw [KronHelpers.conjTranspose_kron_reindex]
  simp

@[simp] private lemma acgate_conjTranspose (U : Square 4) : (acgate U)† = acgate U† := by
  unfold acgate
  calc
    (swapbc * abgate U * swapbc)† = swapbc† * (abgate U)† * swapbc† := by
      simp [Matrix.conjTranspose_mul, mul_assoc]
    _ = swapbc * (abgate U)† * swapbc := by
      simp [swapbc_conjTranspose]
    _ = swapbc * abgate U† * swapbc := by
      rw [abgate_conjTranspose]
    _ = acgate U† := by rfl

lemma swapab_conj_abgate (U : Square 4) :
    swapab * abgate U * swapab = abgate (swap2 * U * swap2) := by
  unfold swapab abgate
  calc
    (swap2 ⊗ₖ (1 : Square 2)) * (U ⊗ₖ (1 : Square 2)) * (swap2 ⊗ₖ (1 : Square 2))
        = (((swap2 * U) ⊗ₖ ((1 : Square 2) * (1 : Square 2)))) * (swap2 ⊗ₖ (1 : Square 2)) := by
            rw [← KronHelpers.kron_mul_reindex swap2 U (1 : Square 2) (1 : Square 2)]
    _ = ((swap2 * U) ⊗ₖ (1 : Square 2)) * (swap2 ⊗ₖ (1 : Square 2)) := by
          simp
    _ = ((swap2 * U) * swap2) ⊗ₖ ((1 : Square 2) * (1 : Square 2)) := by
          rw [← KronHelpers.kron_mul_reindex (swap2 * U) swap2 (1 : Square 2) (1 : Square 2)]
    _ = abgate (swap2 * U * swap2) := by
          simp [mul_assoc, abgate]

@[simp] lemma swapbc_conj_ab (U : Square 4) :
    swapbc * abgate U * swapbc = acgate U := by
  rfl

set_option maxHeartbeats 400000 in
lemma swapab_conj_acgate (U : Square 4) :
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
  simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm,
    swapab_conj_acgate_kron_two]

set_option maxHeartbeats 400000 in
lemma swapab_conj_bcgate (U : Square 4) :
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
  simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm,
    swapab_conj_bcgate_kron_two]

lemma swapbc_conj_ac (U : Square 4) :
    swapbc * acgate U * swapbc = abgate U := by
  unfold acgate
  calc
    swapbc * (swapbc * abgate U * swapbc) * swapbc
        = (swapbc * swapbc) * abgate U * (swapbc * swapbc) := by simp [mul_assoc]
    _ = abgate U := by rw [SwapHelpers.swapbc_mul_swapbc]; simp

lemma swapbc_conj_bcgate (U : Square 4) :
    swapbc * bcgate U * swapbc = bcgate (swap2 * U * swap2) := by
  unfold swapbc bcgate
  calc
    ((1 : Square 2) ⊗ₖ swap2) * ((1 : Square 2) ⊗ₖ U) * ((1 : Square 2) ⊗ₖ swap2)
        = (((1 : Square 2) * (1 : Square 2)) ⊗ₖ (swap2 * U)) * ((1 : Square 2) ⊗ₖ swap2) := by
            rw [← KronHelpers.kron_mul_reindex (1 : Square 2) (1 : Square 2) swap2 U]
    _ = (((1 : Square 2) * (1 : Square 2)) * (1 : Square 2)) ⊗ₖ ((swap2 * U) * swap2) := by
          rw [← KronHelpers.kron_mul_reindex ((1 : Square 2) * (1 : Square 2)) (1 : Square 2)
            (swap2 * U) swap2]
    _ = bcgate (swap2 * U * swap2) := by simp [mul_assoc, bcgate]

lemma swapac_conj_ab (U : Square 4) :
    SwapHelpers.swapac * abgate U * SwapHelpers.swapac = bcgate (swap2 * U * swap2) := by
  unfold SwapHelpers.swapac
  calc
    swapbc * swapab * swapbc * abgate U * (swapbc * swapab * swapbc)
        = swapbc * (swapab * (swapbc * abgate U * swapbc) * swapab) * swapbc := by
            simp [mul_assoc]
    _ = swapbc * (swapab * acgate U * swapab) * swapbc := by rw [swapbc_conj_ab]
    _ = swapbc * bcgate U * swapbc := by rw [swapab_conj_acgate]
    _ = bcgate (swap2 * U * swap2) := by rw [swapbc_conj_bcgate]

lemma swapac_conj_ac (U : Square 4) :
    SwapHelpers.swapac * acgate U * SwapHelpers.swapac = acgate (swap2 * U * swap2) := by
  unfold SwapHelpers.swapac
  calc
    swapbc * swapab * swapbc * acgate U * (swapbc * swapab * swapbc)
        = swapbc * (swapab * (swapbc * acgate U * swapbc) * swapab) * swapbc := by
            simp [mul_assoc]
    _ = swapbc * (swapab * abgate U * swapab) * swapbc := by rw [swapbc_conj_ac]
    _ = swapbc * abgate (swap2 * U * swap2) * swapbc := by rw [swapab_conj_abgate]
    _ = acgate (swap2 * U * swap2) := by rw [swapbc_conj_ab]

lemma swapac_conj_bc (U : Square 4) :
    SwapHelpers.swapac * bcgate U * SwapHelpers.swapac = abgate (swap2 * U * swap2) := by
  unfold SwapHelpers.swapac
  calc
    swapbc * swapab * swapbc * bcgate U * (swapbc * swapab * swapbc)
        = swapbc * (swapab * (swapbc * bcgate U * swapbc) * swapab) * swapbc := by
            simp [mul_assoc]
    _ = swapbc * (swapab * bcgate (swap2 * U * swap2) * swapab) * swapbc := by
          rw [swapbc_conj_bcgate]
    _ = swapbc * acgate (swap2 * U * swap2) * swapbc := by rw [swapab_conj_bcgate]
    _ = abgate (swap2 * U * swap2) := by rw [swapbc_conj_ac]

@[simp] lemma abgate_mul (U W : Square 4) :
    abgate (U * W) = abgate U * abgate W := by
  unfold abgate
  simpa using
    (KronHelpers.kron_mul_reindex (A := U) (B := W) (C := (1 : Square 2)) (D := (1 : Square 2)))

@[simp] lemma bcgate_mul (U W : Square 4) :
    bcgate (U * W) = bcgate U * bcgate W := by
  unfold bcgate
  simpa using
    (KronHelpers.kron_mul_reindex (A := (1 : Square 2)) (B := (1 : Square 2)) (C := U) (D := W))

@[simp] lemma acgate_mul (U W : Square 4) :
    acgate (U * W) = acgate U * acgate W := by
  unfold acgate
  rw [abgate_mul]
  calc
    swapbc * (abgate U * abgate W) * swapbc
        = swapbc * abgate U * abgate W * swapbc := by simp [mul_assoc]
    _ = swapbc * abgate U * (swapbc * swapbc) * abgate W * swapbc := by
          rw [SwapHelpers.swapbc_mul_swapbc]
          simp [mul_assoc]
    _ = (swapbc * abgate U * swapbc) * (swapbc * abgate W * swapbc) := by
          simp [mul_assoc]
    _ = acgate U * acgate W := by rfl

lemma acgate_localA_eq (Q : Square 2) :
    acgate (Q ⊗ₖ (1 : Square 2)) = Q ⊗ₖ (1 : Square 4) := by
  rw [acgate_kron_two]
  simpa using congrArg (fun M => Q ⊗ₖ M) (TwoControl.one_kron_one 2 2)

lemma swapab_twoQubitGate (U : Square 8) (hU : TwoQubitGate U) :
    TwoQubitGate (swapab * U * swapab) := by
  rcases hU with ⟨V, hV, hEq | hEq | hEq⟩
  · refine ⟨swap2 * V * swap2, SwapHelpers.swap2_conj_unitary hV, ?_⟩
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

lemma swapac_twoQubitGate (U : Square 8) (hU : TwoQubitGate U) :
    TwoQubitGate (SwapHelpers.swapac * U * SwapHelpers.swapac) := by
  rcases hU with ⟨V, hV, hEq | hEq | hEq⟩
  · refine ⟨swap2 * V * swap2, SwapHelpers.swap2_conj_unitary hV, ?_⟩
    right
    right
    rw [hEq]
    exact swapac_conj_ab V
  · refine ⟨swap2 * V * swap2, SwapHelpers.swap2_conj_unitary hV, ?_⟩
    right
    left
    rw [hEq]
    exact swapac_conj_ac V
  · refine ⟨swap2 * V * swap2, SwapHelpers.swap2_conj_unitary hV, ?_⟩
    left
    rw [hEq]
    exact swapac_conj_bc V

lemma bcgate_localC_eq (R : Square 2) :
    bcgate ((1 : Square 2) ⊗ₖ R) = (1 : Square 4) ⊗ₖ R := by
  rw [bcgate_kron_two]
  simpa using congrArg (fun M => M ⊗ₖ R) (TwoControl.one_kron_one 2 2)

lemma acgate_localC_eq (R : Square 2) :
    acgate ((1 : Square 2) ⊗ₖ R) = bcgate ((1 : Square 2) ⊗ₖ R) := by
  rw [acgate_kron_two, bcgate_kron_two, ← KronHelpers.kron_assoc_222 (1 : Square 2) (1 : Square 2) R]

lemma abgate_commute_localC (A : Square 4) (R : Square 2) :
    abgate A * bcgate ((1 : Square 2) ⊗ₖ R) =
      bcgate ((1 : Square 2) ⊗ₖ R) * abgate A := by
  calc
    abgate A * bcgate ((1 : Square 2) ⊗ₖ R)
        = (A ⊗ₖ (1 : Square 2)) * ((1 : Square 4) ⊗ₖ R) := by
            rw [abgate, bcgate_localC_eq]
    _ = (A * (1 : Square 4)) ⊗ₖ ((1 : Square 2) * R) := by
          rw [← KronHelpers.kron_mul_reindex A (1 : Square 4) (1 : Square 2) R]
    _ = A ⊗ₖ R := by simp
    _ = ((1 : Square 4) * A) ⊗ₖ (R * (1 : Square 2)) := by simp
    _ = ((1 : Square 4) ⊗ₖ R) * (A ⊗ₖ (1 : Square 2)) := by
          rw [KronHelpers.kron_mul_reindex (1 : Square 4) A R (1 : Square 2)]
    _ = bcgate ((1 : Square 2) ⊗ₖ R) * abgate A := by
          conv_rhs => rw [bcgate_localC_eq, abgate]

lemma localC_cancel_right (V : Square 2) (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ((1 : Square 2) ⊗ₖ V) * ((1 : Square 2) ⊗ₖ V†) = (1 : Square 4) := by
  have hVright : V * V† = (1 : Square 2) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hV)
  calc
    ((1 : Square 2) ⊗ₖ V) * ((1 : Square 2) ⊗ₖ V†)
        = ((1 : Square 2) * (1 : Square 2)) ⊗ₖ (V * V†) := by
            rw [← kron_mul_two]
    _ = (1 : Square 2) ⊗ₖ (1 : Square 2) := by simp [hVright]
    _ = (1 : Square 4) := by simpa using TwoControl.one_kron_one 2 2

lemma localC_cancel_left (V : Square 2) (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ((1 : Square 2) ⊗ₖ V†) * ((1 : Square 2) ⊗ₖ V) = (1 : Square 4) := by
  have hVleft : V† * V = (1 : Square 2) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hV)
  calc
    ((1 : Square 2) ⊗ₖ V†) * ((1 : Square 2) ⊗ₖ V)
        = ((1 : Square 2) * (1 : Square 2)) ⊗ₖ (V† * V) := by
            rw [← kron_mul_two]
    _ = (1 : Square 2) ⊗ₖ (1 : Square 2) := by simp [hVleft]
    _ = (1 : Square 4) := by simpa using TwoControl.one_kron_one 2 2

lemma bcgate_localC_cancel_right (V : Square 2) (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    bcgate ((1 : Square 2) ⊗ₖ V) * bcgate ((1 : Square 2) ⊗ₖ V†) = (1 : Square 8) := by
  rw [← bcgate_mul, localC_cancel_right V hV]
  unfold bcgate
  simpa using (TwoControl.one_kron_one 2 4)

lemma bcgate_localC_cancel_left (V : Square 2) (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    bcgate ((1 : Square 2) ⊗ₖ V†) * bcgate ((1 : Square 2) ⊗ₖ V) = (1 : Square 8) := by
  rw [← bcgate_mul, localC_cancel_left V hV]
  unfold bcgate
  simpa using (TwoControl.one_kron_one 2 4)

lemma bcgate_localC_conj_kron (P : Square 2) (B : Square 4) (V : Square 2) :
    bcgate ((1 : Square 2) ⊗ₖ V) * (P ⊗ₖ B) * bcgate ((1 : Square 2) ⊗ₖ V†) =
      P ⊗ₖ (((1 : Square 2) ⊗ₖ V) * B * ((1 : Square 2) ⊗ₖ V†)) := by
  unfold bcgate
  calc
    ((1 : Square 2) ⊗ₖ ((1 : Square 2) ⊗ₖ V)) * (P ⊗ₖ B) *
        ((1 : Square 2) ⊗ₖ ((1 : Square 2) ⊗ₖ V†))
        = (((1 : Square 2) * P) ⊗ₖ (((1 : Square 2) ⊗ₖ V) * B)) *
            ((1 : Square 2) ⊗ₖ ((1 : Square 2) ⊗ₖ V†)) := by
              rw [← KronHelpers.kron_mul_reindex (1 : Square 2) P ((1 : Square 2) ⊗ₖ V) B]
    _ = ((((1 : Square 2) * P) * (1 : Square 2)) ⊗ₖ
          ((((1 : Square 2) ⊗ₖ V) * B) * ((1 : Square 2) ⊗ₖ V†))) := by
            rw [← KronHelpers.kron_mul_reindex ((1 : Square 2) * P) (1 : Square 2)
              (((1 : Square 2) ⊗ₖ V) * B) ((1 : Square 2) ⊗ₖ V†)]
    _ = P ⊗ₖ (((1 : Square 2) ⊗ₖ V) * B * ((1 : Square 2) ⊗ₖ V†)) := by
          simp [mul_assoc]

lemma controlledGate_conj_local_target (V U : Square 2)
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
                      rw [← KronHelpers.kron_mul_reindex (1 : Square 2) proj0 V (1 : Square 2)]
              _ = ((((1 : Square 2) * proj0) * (1 : Square 2)) ⊗ₖ ((V * (1 : Square 2)) * V†)) := by
                    rw [← KronHelpers.kron_mul_reindex ((1 : Square 2) * proj0) (1 : Square 2)
                      (V * (1 : Square 2)) V†]
              _ = proj0 ⊗ₖ (V * (1 : Square 2) * V†) := by simp
          · calc
              ((1 : Square 2) ⊗ₖ V) * (proj1 ⊗ₖ U) * ((1 : Square 2) ⊗ₖ V†)
                  = (((1 : Square 2) * proj1) ⊗ₖ (V * U)) * ((1 : Square 2) ⊗ₖ V†) := by
                      rw [← KronHelpers.kron_mul_reindex (1 : Square 2) proj1 V U]
              _ = ((((1 : Square 2) * proj1) * (1 : Square 2)) ⊗ₖ ((V * U) * V†)) := by
                    rw [← KronHelpers.kron_mul_reindex ((1 : Square 2) * proj1) (1 : Square 2)
                      (V * U) V†]
              _ = proj1 ⊗ₖ (V * U * V†) := by simp [mul_assoc]
    _ = proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ (V * U * V†) := by
          simp [hVright, mul_assoc]
    _ = controlledGate (V * U * V†) := by rw [controlledGate]

lemma ccu_conj_local_target (V U : Square 2)
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

lemma conj_local_target_twoQubitGate (V : Square 2)
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
      Submonoid.mul_mem _ (Submonoid.mul_mem _ hLocal hA) hLocalDag, Or.inr <| Or.inl ?_⟩
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
      Submonoid.mul_mem _ (Submonoid.mul_mem _ hLocal hA) hLocalDag, Or.inr <| Or.inr ?_⟩
    rw [hEq]
    calc
      bcgate ((1 : Square 2) ⊗ₖ V) * bcgate A * bcgate ((1 : Square 2) ⊗ₖ V†)
          = bcgate (((1 : Square 2) ⊗ₖ V) * A) * bcgate ((1 : Square 2) ⊗ₖ V†) := by
              rw [← bcgate_mul]
      _ = bcgate (((1 : Square 2) ⊗ₖ V) * A * ((1 : Square 2) ⊗ₖ V†)) := by
            rw [← bcgate_mul]

lemma conj_local_target_product_four (V : Square 2)
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

lemma acgate_localA_commute_bcgate (Q : Square 2) (U : Square 4) :
    acgate (Q ⊗ₖ (1 : Square 2)) * bcgate U =
      bcgate U * acgate (Q ⊗ₖ (1 : Square 2)) := by
  calc
    acgate (Q ⊗ₖ (1 : Square 2)) * bcgate U
      = (Q ⊗ₖ (1 : Square 4)) * ((1 : Square 2) ⊗ₖ U) := by
          rw [acgate_localA_eq, bcgate]
    _ = (Q * (1 : Square 2)) ⊗ₖ ((1 : Square 4) * U) := by
          rw [← KronHelpers.kron_mul_reindex Q (1 : Square 2) (1 : Square 4) U]
    _ = Q ⊗ₖ U := by simp
    _ = ((1 : Square 2) * Q) ⊗ₖ (U * (1 : Square 4)) := by simp
    _ = ((1 : Square 2) ⊗ₖ U) * (Q ⊗ₖ (1 : Square 4)) := by
          rw [← KronHelpers.kron_mul_reindex (1 : Square 2) Q U (1 : Square 4)]
    _ = bcgate U * acgate (Q ⊗ₖ (1 : Square 2)) := by
          rw [acgate_localA_eq, bcgate]

lemma bcgate_localB_commute_acgate (Q : Square 2) (U : Square 4) :
    bcgate (Q ⊗ₖ (1 : Square 2)) * acgate U =
      acgate U * bcgate (Q ⊗ₖ (1 : Square 2)) := by
  have hswap_acU : swapab * acgate U = bcgate U * swapab := by
    calc
      swapab * acgate U = (swapab * acgate U * swapab) * swapab := by
        simp [mul_assoc, SwapHelpers.swapab_mul_swapab]
      _ = bcgate U * swapab := by rw [swapab_conj_acgate]
  calc
    bcgate (Q ⊗ₖ (1 : Square 2)) * acgate U
        = (swapab * acgate (Q ⊗ₖ (1 : Square 2)) * swapab) * acgate U := by
            simpa using
              congrArg (fun M => M * acgate U)
                ((swapab_conj_acgate (Q ⊗ₖ (1 : Square 2))).symm)
    _ = swapab * acgate (Q ⊗ₖ (1 : Square 2)) * (swapab * acgate U) := by
          simp [mul_assoc]
    _ = swapab * acgate (Q ⊗ₖ (1 : Square 2)) * (bcgate U * swapab) := by
          rw [hswap_acU]
    _ = swapab * (acgate (Q ⊗ₖ (1 : Square 2)) * bcgate U) * swapab := by
          simp [mul_assoc]
    _ = swapab * (bcgate U * acgate (Q ⊗ₖ (1 : Square 2))) * swapab := by
          rw [acgate_localA_commute_bcgate]
    _ = (swapab * bcgate U * swapab) * (swapab * acgate (Q ⊗ₖ (1 : Square 2)) * swapab) := by
          calc
            swapab * (bcgate U * acgate (Q ⊗ₖ (1 : Square 2))) * swapab
                = swapab * bcgate U * acgate (Q ⊗ₖ (1 : Square 2)) * swapab := by
                    simp [mul_assoc]
            _ = swapab * bcgate U * (swapab * swapab) * acgate (Q ⊗ₖ (1 : Square 2)) * swapab := by
                    rw [SwapHelpers.swapab_mul_swapab]
                    simp [mul_assoc]
            _ = (swapab * bcgate U * swapab) * (swapab * acgate (Q ⊗ₖ (1 : Square 2)) * swapab) := by
                    simp [mul_assoc]
    _ = acgate U * bcgate (Q ⊗ₖ (1 : Square 2)) := by
          rw [swapab_conj_bcgate, swapab_conj_acgate]

lemma swapbc_mulVec_kronVec (a b c : Vec 2) :
    swapbc.mulVec (kronVec (kronVec a b) c : Vec 8) = kronVec (kronVec a c) b := by
  unfold swapbc
  calc
    ((1 : Square 2) ⊗ₖ swap2).mulVec (kronVec (kronVec a b) c : Vec 8)
        = ((1 : Square 2) ⊗ₖ swap2).mulVec (kronVec a (kronVec b c)) := by
            rw [StateHelpers.kronVec_assoc_222]
    _ = kronVec a (swap2.mulVec (kronVec b c)) := by
          simpa using
            (StateHelpers.kron_mulVec_reindexed (A := (1 : Square 2)) (B := swap2)
              (x := a) (y := kronVec b c))
    _ = kronVec a (kronVec c b) := by rw [SwapHelpers.swap2_mulVec_kronVec]
    _ = kronVec (kronVec a c) b := by rw [StateHelpers.kronVec_assoc_222]

lemma bcgate_mulVec_kronVec (U : Square 4) (a : Vec 2) (φ : Vec 4) :
    (bcgate U).mulVec (kronVec a φ) = kronVec a (U.mulVec φ) := by
  unfold bcgate
  simpa using
    (StateHelpers.kron_mulVec_reindexed (A := (1 : Square 2)) (B := U) (x := a) (y := φ))

lemma acgate_mulVec_kronVec (U : Square 4) (a b c : Vec 2) :
    (acgate U).mulVec (kronVec (kronVec a b) c : Vec 8) =
      swapbc.mulVec (kronVec (U.mulVec (kronVec a c)) b) := by
  unfold acgate
  calc
    (swapbc * abgate U * swapbc).mulVec (kronVec (kronVec a b) c : Vec 8)
        = swapbc.mulVec ((abgate U * swapbc).mulVec (kronVec (kronVec a b) c : Vec 8)) := by
            simp [mul_assoc, Matrix.mulVec_mulVec]
    _ = swapbc.mulVec ((abgate U).mulVec (swapbc.mulVec (kronVec (kronVec a b) c))) := by
          simp [Matrix.mulVec_mulVec]
    _ = swapbc.mulVec ((abgate U).mulVec (kronVec (kronVec a c) b)) := by
          rw [swapbc_mulVec_kronVec]
    _ = swapbc.mulVec (kronVec (U.mulVec (kronVec a c)) b) := by
          have htmp :
              (abgate U).mulVec (kronVec (kronVec a c) b) =
                kronVec (U.mulVec (kronVec a c)) b := by
            unfold abgate
            simpa using
              (StateHelpers.kron_mulVec_reindexed (A := U) (B := (1 : Square 2))
                (x := kronVec a c) (y := b))
          exact congrArg swapbc.mulVec htmp

lemma acgate_mulVec_of_product (U : Square 4)
    (a b c a' c' : Vec 2)
    (h : U.mulVec (kronVec a c) = kronVec a' c') :
    (acgate U).mulVec (kronVec (kronVec a b) c) = kronVec (kronVec a' b) c' := by
  rw [acgate_mulVec_kronVec, h, swapbc_mulVec_kronVec]

end GateHelpers

end TwoControl

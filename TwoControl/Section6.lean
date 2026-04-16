import Mathlib.LinearAlgebra.Matrix.Vec
import TwoControl.BlockHelpers
import TwoControl.KronHelpers
import TwoControl.SwapHelpers
import TwoControl.GateHelpers
import TwoControl.StateHelpers
import TwoControl.Section5

open scoped Matrix ComplexOrder
open Matrix

namespace TwoControl

open BlockHelpers
open KronHelpers
open SwapHelpers
open GateHelpers
open StateHelpers

/-! # Section 6: The second main lemma -/

@[simp] private lemma swapbc_mulVec_involutive (v : Vec 8) :
    swapbc.mulVec (swapbc.mulVec v) = v := by
  calc
    swapbc.mulVec (swapbc.mulVec v) = (swapbc * swapbc).mulVec v := by
      rw [← Matrix.mulVec_mulVec]
    _ = v := by rw [swapbc_mul_swapbc]; simp

private lemma controlled_on_second_mulVec_ket0 (P : Square 2) (x : Vec 2) :
    (((1 : Square 2) ⊗ₖ proj0) + P ⊗ₖ proj1).mulVec (kronVec x ket0) = kronVec x ket0 := by
  rw [Matrix.add_mulVec, kron_mulVec_two_two, kron_mulVec_two_two]
  simp

private lemma acgate_fix_of_output_fix (U : Square 4) (a : Vec 2)
    (h : (acgate U).mulVec (kronVec (kronVec a ket0) ket0) = kronVec (kronVec a ket0) ket0) :
    U.mulVec (kronVec a ket0) = kronVec a ket0 := by
  rw [acgate_mulVec_kronVec] at h
  have h' : kronVec (U.mulVec (kronVec a ket0)) ket0 = kronVec (kronVec a ket0) ket0 := by
    calc
      kronVec (U.mulVec (kronVec a ket0)) ket0
          = swapbc.mulVec (swapbc.mulVec (kronVec (U.mulVec (kronVec a ket0)) ket0)) := by
              symm
              exact swapbc_mulVec_involutive _
      _ = swapbc.mulVec (kronVec (kronVec a ket0) ket0) := by rw [h]
      _ = kronVec (kronVec a ket0) ket0 := by rw [swapbc_mulVec_kronVec]
  exact kronVec_right_cancel_ket0_vec4 h'

private lemma swapbc_mulVec_vec4_ket0 (φ : Vec 4) :
    swapbc.mulVec (kronVec φ ket0 : Vec 8) = ![φ 0, φ 1, 0, 0, φ 2, φ 3, 0, 0] := by
  let u : Vec 2 := ![φ 0, φ 1]
  let v : Vec 2 := ![φ 2, φ 3]
  have hdecomp : φ = kronVec ket0 u + kronVec ket1 v := by
    dsimp [u, v]
    exact vec4_basis_decomp φ
  calc
    swapbc.mulVec (kronVec φ ket0 : Vec 8)
        = swapbc.mulVec (kronVec (kronVec ket0 u + kronVec ket1 v) ket0 : Vec 8) := by
            rw [hdecomp]
    _ = swapbc.mulVec (kronVec (kronVec ket0 u) ket0 : Vec 8) +
          swapbc.mulVec (kronVec (kronVec ket1 v) ket0 : Vec 8) := by
            rw [kronVec_add_left, Matrix.mulVec_add]
    _ = kronVec (kronVec ket0 ket0) u + kronVec (kronVec ket1 ket0) v := by
          rw [swapbc_mulVec_kronVec, swapbc_mulVec_kronVec]
    _ = ![φ 0, φ 1, 0, 0, φ 2, φ 3, 0, 0] := by
          ext i
          fin_cases i <;>
            simp [u, v, ket0, ket1, kronVec_vec4_2_apply_0, kronVec_vec4_2_apply_1,
              kronVec_vec4_2_apply_2, kronVec_vec4_2_apply_3, kronVec_vec4_2_apply_4,
              kronVec_vec4_2_apply_5, kronVec_vec4_2_apply_6, kronVec_vec4_2_apply_7,
              kronVec_vec2_apply_0, kronVec_vec2_apply_1, kronVec_vec2_apply_2,
              kronVec_vec2_apply_3]

private lemma acgate_suffix_ket0 (U : Square 4)
  (a ψ : Vec 2) (φ : Vec 4)
  (_ha : IsQubit a) (hψ : IsQubit ψ) (hφ : IsQubit φ)
    (h : (acgate U).mulVec (kronVec (kronVec a ket0) ket0) = kronVec ψ φ) :
    ∃ w : Vec 2, IsQubit w ∧ φ = kronVec ket0 w := by
  have hψne : ψ ≠ 0 := isQubit_ne_zero hψ
  have hψnz : ψ 0 ≠ 0 ∨ ψ 1 ≠ 0 := by
    by_contra hzero
    apply hψne
    ext i
    fin_cases i
    · exact by simpa using (not_or.mp hzero).1
    · exact by simpa using (not_or.mp hzero).2
  rw [acgate_mulVec_kronVec] at h
  have h2 : ψ 0 * φ 2 = 0 := by
    have hEq := congrFun h 2
    simpa [swapbc_mulVec_vec4_ket0, kronVec_vec2_4_apply_2] using hEq
  have h3 : ψ 0 * φ 3 = 0 := by
    have hEq := congrFun h 3
    simpa [swapbc_mulVec_vec4_ket0, kronVec_vec2_4_apply_3] using hEq
  have h6 : ψ 1 * φ 2 = 0 := by
    have hEq := congrFun h 6
    simpa [swapbc_mulVec_vec4_ket0, kronVec_vec2_4_apply_6] using hEq
  have h7 : ψ 1 * φ 3 = 0 := by
    have hEq := congrFun h 7
    simpa [swapbc_mulVec_vec4_ket0, kronVec_vec2_4_apply_7] using hEq
  have hφ2 : φ 2 = 0 := by
    rcases hψnz with hψ0 | hψ1
    · exact (mul_eq_zero.mp h2).resolve_left hψ0
    · exact (mul_eq_zero.mp h6).resolve_left hψ1
  have hφ3 : φ 3 = 0 := by
    rcases hψnz with hψ0 | hψ1
    · exact (mul_eq_zero.mp h3).resolve_left hψ0
    · exact (mul_eq_zero.mp h7).resolve_left hψ1
  let w : Vec 2 := ![φ 0, φ 1]
  have hwEq : φ = kronVec ket0 w := by
    ext i
    fin_cases i <;> simp [w, ket0, hφ2, hφ3, kronVec_vec2_apply_0, kronVec_vec2_apply_1,
      kronVec_vec2_apply_2, kronVec_vec2_apply_3]
  have hwQ : IsQubit w := by
    have hφ' : IsQubit (kronVec ket0 w) := by simpa [hwEq] using hφ
    exact isQubit_of_kron_left hφ' isQubit_ket0
  exact ⟨w, hwQ, hwEq⟩

set_option maxHeartbeats 400000 in
private lemma acgate_prefix_ket0 (U : Square 4)
    (ψ β : Vec 2) (φ : Vec 4)
    (hψ : IsQubit ψ) (_hβ : IsQubit β) (hφ : IsQubit φ)
    (h : (acgate U).mulVec (kronVec ket0 (kronVec ψ β)) = kronVec ket0 φ) :
    ∃ w : Vec 2, IsQubit w ∧ φ = kronVec ψ w := by
  let γ : Vec 4 := U.mulVec (kronVec ket0 β)
  let u : Vec 2 := ![γ 0, γ 1]
  let v : Vec 2 := ![γ 2, γ 3]
  have hγdecomp : γ = kronVec ket0 u + kronVec ket1 v := by
    dsimp [γ, u, v]
    exact vec4_basis_decomp _
  have hExpand :
      (acgate U).mulVec (kronVec ket0 (kronVec ψ β)) =
        kronVec ket0 (kronVec ψ u) + kronVec ket1 (kronVec ψ v) := by
    calc
      (acgate U).mulVec (kronVec ket0 (kronVec ψ β))
          = (acgate U).mulVec (kronVec (kronVec ket0 ψ) β : Vec 8) := by
              rw [kronVec_assoc_222]
      _ = swapbc.mulVec (kronVec γ ψ) := by
              dsimp [γ]
              rw [acgate_mulVec_kronVec]
      _ = swapbc.mulVec (kronVec (kronVec ket0 u + kronVec ket1 v) ψ) := by rw [hγdecomp]
      _ = swapbc.mulVec (kronVec (kronVec ket0 u) ψ) +
            swapbc.mulVec (kronVec (kronVec ket1 v) ψ) := by
              rw [kronVec_add_left, Matrix.mulVec_add]
      _ = kronVec (kronVec ket0 ψ) u + kronVec (kronVec ket1 ψ) v := by
            rw [swapbc_mulVec_kronVec, swapbc_mulVec_kronVec]
      _ = kronVec ket0 (kronVec ψ u) + kronVec ket1 (kronVec ψ v) := by
            rw [kronVec_assoc_222, kronVec_assoc_222]
  have hEq : kronVec ket0 (kronVec ψ u) + kronVec ket1 (kronVec ψ v) = kronVec ket0 φ := by
    exact hExpand.symm.trans h
  have hψnz : ψ 0 ≠ 0 ∨ ψ 1 ≠ 0 := by
    by_contra hzero
    apply isQubit_ne_zero hψ
    ext i
    fin_cases i
    · exact by simpa using (not_or.mp hzero).1
    · exact by simpa using (not_or.mp hzero).2
  have h4 : ψ 0 * v 0 = 0 := by
    have hcomp := congrFun hEq 4
    simpa [ket0, ket1, kronVec_vec2_4_apply_4, kronVec_vec2_4_apply_0] using hcomp
  have h5 : ψ 0 * v 1 = 0 := by
    have hcomp := congrFun hEq 5
    simpa [ket0, ket1, kronVec_vec2_4_apply_5, kronVec_vec2_4_apply_1] using hcomp
  have h6 : ψ 1 * v 0 = 0 := by
    have hcomp := congrFun hEq 6
    simpa [ket0, ket1, kronVec_vec2_4_apply_6, kronVec_vec2_4_apply_2] using hcomp
  have h7 : ψ 1 * v 1 = 0 := by
    have hcomp := congrFun hEq 7
    simpa [ket0, ket1, kronVec_vec2_4_apply_7, kronVec_vec2_4_apply_3] using hcomp
  have hv0 : v 0 = 0 := by
    rcases hψnz with hψ0 | hψ1
    · exact (mul_eq_zero.mp h4).resolve_left hψ0
    · exact (mul_eq_zero.mp h6).resolve_left hψ1
  have hv1 : v 1 = 0 := by
    rcases hψnz with hψ0 | hψ1
    · exact (mul_eq_zero.mp h5).resolve_left hψ0
    · exact (mul_eq_zero.mp h7).resolve_left hψ1
  have hv : v = 0 := by
    ext i
    fin_cases i <;> simp [hv0, hv1]
  have hφEq8 : kronVec ket0 φ = kronVec ket0 (kronVec ψ u) := by
    calc
      kronVec ket0 φ = kronVec ket0 (kronVec ψ u) + kronVec ket1 (kronVec ψ v) := hEq.symm
      _ = kronVec ket0 (kronVec ψ u) := by simp [hv]
  have hwEq : φ = kronVec ψ u := by
    exact kronVec_left_cancel_ket0_vec4 hφEq8
  have huQ : IsQubit u := by
    have hkQ : IsQubit (kronVec ψ u) := by simpa [hwEq] using hφ
    rw [isQubit_iff_star_dot_eq_one] at hkQ hψ ⊢
    rw [dot_kronVec_two_two] at hkQ
    simpa [hψ] using hkQ
  exact ⟨u, huQ, hwEq⟩

private lemma acgate_fixed_middle_eq (U : Square 4)
    (ψ β w : Vec 2)
    (hψ : IsQubit ψ)
    (h : (acgate U).mulVec (kronVec ket0 (kronVec ψ β)) = kronVec ket0 (kronVec ψ w)) :
    U.mulVec (kronVec ket0 β) = kronVec ket0 w := by
  have hAc : (acgate U).mulVec (kronVec ket0 (kronVec ψ β)) =
      swapbc.mulVec (kronVec (U.mulVec (kronVec ket0 β)) ψ) := by
    calc
      (acgate U).mulVec (kronVec ket0 (kronVec ψ β))
          = (acgate U).mulVec (kronVec (kronVec ket0 ψ) β : Vec 8) := by rw [kronVec_assoc_222]
      _ = swapbc.mulVec (kronVec (U.mulVec (kronVec ket0 β)) ψ) := by rw [acgate_mulVec_kronVec]
  rw [hAc] at h
  have h' : kronVec (U.mulVec (kronVec ket0 β)) ψ = kronVec (kronVec ket0 w) ψ := by
    calc
      kronVec (U.mulVec (kronVec ket0 β)) ψ
          = swapbc.mulVec (swapbc.mulVec (kronVec (U.mulVec (kronVec ket0 β)) ψ)) := by
              symm
              exact swapbc_mulVec_involutive _
      _ = swapbc.mulVec (kronVec ket0 (kronVec ψ w)) := by rw [h]
      _ = swapbc.mulVec (kronVec (kronVec ket0 ψ) w) := by rw [kronVec_assoc_222]
      _ = kronVec (kronVec ket0 w) ψ := by rw [swapbc_mulVec_kronVec]
  exact kronVec_right_cancel_of_ne_zero_vec4 (isQubit_ne_zero hψ) h'

private lemma controlled_on_first_of_fixing_basis (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (h0 : U.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0)
    (h1 : U.mulVec (kronVec ket0 ket1) = kronVec ket0 ket1) :
    ∃ P : Square 2, P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      U = proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ P := by
  let Ub : BlockMatrix 2 := blockify (n := 2) U
  let A : Square 2 := Ub.toBlocks₁₁
  let B : Square 2 := Ub.toBlocks₁₂
  let C : Square 2 := Ub.toBlocks₂₁
  let D : Square 2 := Ub.toBlocks₂₂
  have hUdecomp : U = proj0 ⊗ₖ A + proj01 ⊗ₖ B + proj10 ⊗ₖ C + proj1 ⊗ₖ D := by
    dsimp [A, B, C, D, Ub]
    simpa using (blockDecomposition (n := 2) U)
  have h0' : kronVec ket0 (A.mulVec ket0) + kronVec ket1 (C.mulVec ket0) = kronVec ket0 ket0 := by
    have h0'' := h0
    rw [hUdecomp] at h0''
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
      kron_mulVec_two_two, kron_mulVec_two_two, kron_mulVec_two_two, kron_mulVec_two_two,
      proj0_mulVec_ket0, proj01_mulVec_ket0, proj10_mulVec_ket0, proj1_mulVec_ket0] at h0''
    simpa [kronVec_zero_left, kronVec_zero_right, add_assoc] using h0''
  have h1' : kronVec ket0 (A.mulVec ket1) + kronVec ket1 (C.mulVec ket1) = kronVec ket0 ket1 := by
    have h1'' := h1
    rw [hUdecomp] at h1''
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
      kron_mulVec_two_two, kron_mulVec_two_two, kron_mulVec_two_two, kron_mulVec_two_two,
      proj0_mulVec_ket0, proj01_mulVec_ket0, proj10_mulVec_ket0, proj1_mulVec_ket0] at h1''
    simpa [kronVec_zero_left, kronVec_zero_right, add_assoc] using h1''
  have hA0 : A.mulVec ket0 = ket0 := by
    ext i
    fin_cases i
    · simpa [kronVec_vec2_apply_0, kronVec_vec2_apply_2, ket0, ket1] using congrFun h0' 0
    · simpa [kronVec_vec2_apply_1, kronVec_vec2_apply_3, ket0, ket1] using congrFun h0' 1
  have hA1 : A.mulVec ket1 = ket1 := by
    ext i
    fin_cases i
    · simpa [kronVec_vec2_apply_0, kronVec_vec2_apply_2, ket0, ket1] using congrFun h1' 0
    · simpa [kronVec_vec2_apply_1, kronVec_vec2_apply_3, ket0, ket1] using congrFun h1' 1
  have hC0 : C.mulVec ket0 = 0 := by
    ext i
    fin_cases i
    · simpa [kronVec_vec2_apply_0, kronVec_vec2_apply_2, ket0, ket1] using congrFun h0' 2
    · simpa [kronVec_vec2_apply_1, kronVec_vec2_apply_3, ket0, ket1] using congrFun h0' 3
  have hC1 : C.mulVec ket1 = 0 := by
    ext i
    fin_cases i
    · simpa [kronVec_vec2_apply_0, kronVec_vec2_apply_2, ket0, ket1] using congrFun h1' 2
    · simpa [kronVec_vec2_apply_1, kronVec_vec2_apply_3, ket0, ket1] using congrFun h1' 3
  have hA : A = (1 : Square 2) := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mulVec, dotProduct, ket0, Matrix.one_apply] using congrFun hA0 0
    · simpa [Matrix.mulVec, dotProduct, ket1, Matrix.one_apply] using congrFun hA1 0
    · simpa [Matrix.mulVec, dotProduct, ket0, Matrix.one_apply] using congrFun hA0 1
    · simpa [Matrix.mulVec, dotProduct, ket1, Matrix.one_apply] using congrFun hA1 1
  have hC : C = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mulVec, dotProduct, ket0] using congrFun hC0 0
    · simpa [Matrix.mulVec, dotProduct, ket1] using congrFun hC1 0
    · simpa [Matrix.mulVec, dotProduct, ket0] using congrFun hC0 1
    · simpa [Matrix.mulVec, dotProduct, ket1] using congrFun hC1 1
  have hUbUnitary : Ub ∈ Matrix.unitaryGroup (Fin 2 ⊕ Fin 2) ℂ := by
    dsimp [Ub]
    exact (blockify_mem_unitaryGroup_iff (n := 2) (U := U)).2 hU
  have hUbBlocks : Ub = Matrix.fromBlocks A B C D := by
    dsimp [A, B, C, D, Ub]
    symm
    exact Matrix.fromBlocks_toBlocks (blockify (n := 2) U)
  have hUpperUnitary : Matrix.fromBlocks A B 0 D ∈ Matrix.unitaryGroup (Fin 2 ⊕ Fin 2) ℂ := by
    rw [hUbBlocks] at hUbUnitary
    simpa [hC] using hUbUnitary
  have hB : B = 0 := upper_block_zero_of_unitary A B D hUpperUnitary
  have hDiagUnitary : Matrix.fromBlocks (1 : Square 2) 0 0 D ∈ Matrix.unitaryGroup (Fin 2 ⊕ Fin 2) ℂ := by
    simpa [hA, hB] using hUpperUnitary
  have hD : D ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    exact (block_diagonal_unitary (1 : Square 2) D hDiagUnitary).2
  refine ⟨D, hD, ?_⟩
  rw [hUdecomp, hA, hB, hC]
  simp [TwoControl.zero_kron_right]

private lemma controlled_on_second_of_fixing_basis (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (h0 : U.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0)
    (h1 : U.mulVec (kronVec ket1 ket0) = kronVec ket1 ket0) :
    ∃ P : Square 2, P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      U = (1 : Square 2) ⊗ₖ proj0 + P ⊗ₖ proj1 := by
  let U' : Square 4 := swap2 * U * swap2
  have hU' : U' ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    dsimp [U']
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ swap2_unitary hU) swap2_unitary
  have h0' : U'.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0 := by
    dsimp [U']
    calc
      (swap2 * U * swap2).mulVec (kronVec ket0 ket0)
          = swap2.mulVec (U.mulVec (swap2.mulVec (kronVec ket0 ket0))) := by
              simp [Matrix.mulVec_mulVec, mul_assoc]
      _ = swap2.mulVec (U.mulVec (kronVec ket0 ket0)) := by rw [swap2_mulVec_kronVec]
      _ = swap2.mulVec (kronVec ket0 ket0) := by rw [h0]
      _ = kronVec ket0 ket0 := by rw [swap2_mulVec_kronVec]
  have h1' : U'.mulVec (kronVec ket0 ket1) = kronVec ket0 ket1 := by
    dsimp [U']
    calc
      (swap2 * U * swap2).mulVec (kronVec ket0 ket1)
          = swap2.mulVec (U.mulVec (swap2.mulVec (kronVec ket0 ket1))) := by
              simp [Matrix.mulVec_mulVec, mul_assoc]
      _ = swap2.mulVec (U.mulVec (kronVec ket1 ket0)) := by rw [swap2_mulVec_kronVec]
      _ = swap2.mulVec (kronVec ket1 ket0) := by rw [h1]
      _ = kronVec ket0 ket1 := by rw [swap2_mulVec_kronVec]
  rcases controlled_on_first_of_fixing_basis U' hU' h0' h1' with ⟨P, hP, hEq⟩
  refine ⟨P, hP, ?_⟩
  dsimp [U'] at hEq
  calc
      U = swap2 * (swap2 * U * swap2) * swap2 := by
        calc
      U = (swap2 * swap2) * U * (swap2 * swap2) := by
        rw [swap2_mul_swap2]
        simp []
      _ = swap2 * (swap2 * U * swap2) * swap2 := by
        simp [mul_assoc]
    _ = swap2 * (proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ P) * swap2 := by rw [hEq]
    _ = swap2 * (proj0 ⊗ₖ (1 : Square 2)) * swap2 + swap2 * (proj1 ⊗ₖ P) * swap2 := by
          rw [mul_add, add_mul]
    _ = (1 : Square 2) ⊗ₖ proj0 + P ⊗ₖ proj1 := by
          rw [swap2_conj_kron, swap2_conj_kron]

private lemma controlled_on_first_of_two_images (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    {β β' u v : Vec 2}
    (hβ : IsQubit β) (hβ' : IsQubit β')
    (horth : star β ⬝ᵥ β' = 0)
    (hu : IsQubit u) (hv : IsQubit v)
    (h0 : U.mulVec (kronVec ket0 β) = kronVec ket0 u)
    (h1 : U.mulVec (kronVec ket0 β') = kronVec ket0 v) :
    ∃ (P₀ P₁ : Square 2),
      P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      U = proj0 ⊗ₖ P₀ + proj1 ⊗ₖ P₁ := by
  let Qin : Square 2 := colMatrix β β'
  have hQin : Qin ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    dsimp [Qin]
    exact colMatrix_unitary_of_orthonormal β β' hβ hβ' horth
  have hket0dot : star ket0 ⬝ᵥ ket0 = (1 : ℂ) :=
    (isQubit_iff_star_dot_eq_one ket0).mp isQubit_ket0
  have horthOut : star u ⬝ᵥ v = 0 := by
    have hin0 : star (kronVec ket0 β) ⬝ᵥ kronVec ket0 β' = 0 := by
      rw [dot_kronVec_two_two_cross]
      rw [hket0dot, one_mul]
      exact horth
    have hpres := dot_mulVec_of_unitary U hU (kronVec ket0 β) (kronVec ket0 β')
    have hpres0 : star (U.mulVec (kronVec ket0 β)) ⬝ᵥ U.mulVec (kronVec ket0 β') = 0 :=
      hpres.trans hin0
    rw [h0, h1, dot_kronVec_two_two_cross] at hpres0
    rw [hket0dot, one_mul] at hpres0
    exact hpres0
  let Qout : Square 2 := colMatrix u v
  have hQout : Qout ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    dsimp [Qout]
    exact colMatrix_unitary_of_orthonormal u v hu hv horthOut
  let U' : Square 4 := ((1 : Square 2) ⊗ₖ Qout†) * U * ((1 : Square 2) ⊗ₖ Qin)
  have hU' : U' ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    dsimp [U']
    refine Submonoid.mul_mem _ ?_ (kron_unitary_two _ _ (Submonoid.one_mem _) hQin)
    exact Submonoid.mul_mem _ (kron_unitary_two _ _ (Submonoid.one_mem _) (conjTranspose_mem_unitaryGroup hQout)) hU
  have h0' : U'.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0 := by
    dsimp [U']
    calc
      (((1 : Square 2) ⊗ₖ Qout†) * U * ((1 : Square 2) ⊗ₖ Qin)).mulVec (kronVec ket0 ket0)
          = (((1 : Square 2) ⊗ₖ Qout†) * U).mulVec (((1 : Square 2) ⊗ₖ Qin).mulVec (kronVec ket0 ket0)) := by
              rw [Matrix.mulVec_mulVec, mul_assoc]
      _ = (((1 : Square 2) ⊗ₖ Qout†) * U).mulVec (kronVec ket0 (Qin.mulVec ket0)) := by
            rw [kron_mulVec_two_two]
            simp
      _ = (((1 : Square 2) ⊗ₖ Qout†) * U).mulVec (kronVec ket0 β) := by simp [Qin]
      _ = ((1 : Square 2) ⊗ₖ Qout†).mulVec (U.mulVec (kronVec ket0 β)) := by
        rw [Matrix.mulVec_mulVec]
      _ = ((1 : Square 2) ⊗ₖ Qout†).mulVec (kronVec ket0 u) := by rw [h0]
      _ = kronVec (((1 : Square 2).mulVec ket0)) (Qout†.mulVec u) := by rw [kron_mulVec_two_two]
      _ = kronVec ket0 (Qout†.mulVec u) := by simp
      _ = kronVec ket0 ket0 := by rw [colMatrix_conjTranspose_mulVec_left _ _ hQout]
  have h1' : U'.mulVec (kronVec ket0 ket1) = kronVec ket0 ket1 := by
    dsimp [U']
    calc
      (((1 : Square 2) ⊗ₖ Qout†) * U * ((1 : Square 2) ⊗ₖ Qin)).mulVec (kronVec ket0 ket1)
          = (((1 : Square 2) ⊗ₖ Qout†) * U).mulVec (((1 : Square 2) ⊗ₖ Qin).mulVec (kronVec ket0 ket1)) := by
              rw [Matrix.mulVec_mulVec, mul_assoc]
      _ = (((1 : Square 2) ⊗ₖ Qout†) * U).mulVec (kronVec ket0 (Qin.mulVec ket1)) := by
            rw [kron_mulVec_two_two]
            simp
      _ = (((1 : Square 2) ⊗ₖ Qout†) * U).mulVec (kronVec ket0 β') := by simp [Qin]
      _ = ((1 : Square 2) ⊗ₖ Qout†).mulVec (U.mulVec (kronVec ket0 β')) := by
        rw [Matrix.mulVec_mulVec]
      _ = ((1 : Square 2) ⊗ₖ Qout†).mulVec (kronVec ket0 v) := by rw [h1]
      _ = kronVec (((1 : Square 2).mulVec ket0)) (Qout†.mulVec v) := by rw [kron_mulVec_two_two]
      _ = kronVec ket0 (Qout†.mulVec v) := by simp
      _ = kronVec ket0 ket1 := by rw [colMatrix_conjTranspose_mulVec_right _ _ hQout]
  rcases controlled_on_first_of_fixing_basis U' hU' h0' h1' with ⟨P, hP, hEq⟩
  let P₀ : Square 2 := Qout * Qin†
  let P₁ : Square 2 := Qout * P * Qin†
  have hP₀ : P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    dsimp [P₀]
    exact Submonoid.mul_mem _ hQout (conjTranspose_mem_unitaryGroup hQin)
  have hP₁ : P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    dsimp [P₁]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hQout hP) (conjTranspose_mem_unitaryGroup hQin)
  have hQoutR : ((1 : Square 2) ⊗ₖ Qout) * ((1 : Square 2) ⊗ₖ Qout†) = (1 : Square 4) := by
    have hright : Qout * Qout† = (1 : Square 2) := Matrix.mem_unitaryGroup_iff.mp hQout
    rw [← kron_mul_two, hright]
    simpa using (TwoControl.one_kron_one 2 2)
  have hQinR : ((1 : Square 2) ⊗ₖ Qin) * ((1 : Square 2) ⊗ₖ Qin†) = (1 : Square 4) := by
    have hright : Qin * Qin† = (1 : Square 2) := Matrix.mem_unitaryGroup_iff.mp hQin
    rw [← kron_mul_two, hright]
    simpa using (TwoControl.one_kron_one 2 2)
  have hRebuild : (((1 : Square 2) ⊗ₖ Qout) * U') * ((1 : Square 2) ⊗ₖ Qin†) = U := by
    dsimp [U']
    calc
      (((1 : Square 2) ⊗ₖ Qout) * (((1 : Square 2) ⊗ₖ Qout†) * U * ((1 : Square 2) ⊗ₖ Qin))) *
          ((1 : Square 2) ⊗ₖ Qin†)
          = (((1 : Square 2) ⊗ₖ Qout) * ((1 : Square 2) ⊗ₖ Qout†)) * U *
              (((1 : Square 2) ⊗ₖ Qin) * ((1 : Square 2) ⊗ₖ Qin†)) := by
                simp [mul_assoc]
      _ = (1 : Square 4) * U * (1 : Square 4) := by rw [hQoutR, hQinR]
      _ = U := by simp
  refine ⟨P₀, P₁, hP₀, hP₁, ?_⟩
  calc
    U = (((1 : Square 2) ⊗ₖ Qout) * U') * ((1 : Square 2) ⊗ₖ Qin†) := hRebuild.symm
    _ = (((1 : Square 2) ⊗ₖ Qout) * (proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ P)) * ((1 : Square 2) ⊗ₖ Qin†) := by
          rw [hEq]
    _ = (((1 : Square 2) ⊗ₖ Qout) * (proj0 ⊗ₖ (1 : Square 2))) * ((1 : Square 2) ⊗ₖ Qin†) +
          (((1 : Square 2) ⊗ₖ Qout) * (proj1 ⊗ₖ P)) * ((1 : Square 2) ⊗ₖ Qin†) := by
            simp [mul_add, add_mul, mul_assoc]
    _ = proj0 ⊗ₖ P₀ + proj1 ⊗ₖ P₁ := by
          dsimp [P₀, P₁]
          rw [← kron_mul_two, ← kron_mul_two, ← kron_mul_two, ← kron_mul_two]
          simp [mul_assoc]

private lemma zero_matrix_of_mulVec_pair_det_ne_zero (M : Square 2) (u v : Vec 2)
    (hdet : detVec2 u v ≠ 0)
    (hu : M.mulVec u = 0) (hv : M.mulVec v = 0) :
    M = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  · have hu0 := congrFun hu 0
    have hv0 := congrFun hv 0
    have hu0' : M 0 0 * u 0 + M 0 1 * u 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hu0
    have hv0' : M 0 0 * v 0 + M 0 1 * v 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hv0
    have hmul : M 0 0 * detVec2 u v = 0 := by
      calc
        M 0 0 * detVec2 u v
            = (M 0 0 * u 0 + M 0 1 * u 1) * v 1 - (M 0 0 * v 0 + M 0 1 * v 1) * u 1 := by
                simp [detVec2]
                ring
        _ = 0 := by rw [hu0', hv0']; ring
    exact (mul_eq_zero.mp hmul).resolve_right hdet
  · have hu0 := congrFun hu 0
    have hv0 := congrFun hv 0
    have hu0' : M 0 0 * u 0 + M 0 1 * u 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hu0
    have hv0' : M 0 0 * v 0 + M 0 1 * v 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hv0
    have hmul : M 0 1 * detVec2 u v = 0 := by
      calc
        M 0 1 * detVec2 u v
            = (M 0 0 * v 0 + M 0 1 * v 1) * u 0 - (M 0 0 * u 0 + M 0 1 * u 1) * v 0 := by
                simp [detVec2]
                ring
        _ = 0 := by rw [hu0', hv0']; ring
    exact (mul_eq_zero.mp hmul).resolve_right hdet
  · have hu1 := congrFun hu 1
    have hv1 := congrFun hv 1
    have hu1' : M 1 0 * u 0 + M 1 1 * u 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hu1
    have hv1' : M 1 0 * v 0 + M 1 1 * v 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hv1
    have hmul : M 1 0 * detVec2 u v = 0 := by
      calc
        M 1 0 * detVec2 u v
            = (M 1 0 * u 0 + M 1 1 * u 1) * v 1 - (M 1 0 * v 0 + M 1 1 * v 1) * u 1 := by
                simp [detVec2]
                ring
        _ = 0 := by rw [hu1', hv1']; ring
    exact (mul_eq_zero.mp hmul).resolve_right hdet
  · have hu1 := congrFun hu 1
    have hv1 := congrFun hv 1
    have hu1' : M 1 0 * u 0 + M 1 1 * u 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hu1
    have hv1' : M 1 0 * v 0 + M 1 1 * v 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hv1
    have hmul : M 1 1 * detVec2 u v = 0 := by
      calc
        M 1 1 * detVec2 u v
            = (M 1 0 * v 0 + M 1 1 * v 1) * u 0 - (M 1 0 * u 0 + M 1 1 * u 1) * v 0 := by
                simp [detVec2]
                ring
        _ = 0 := by rw [hu1', hv1']; ring
    exact (mul_eq_zero.mp hmul).resolve_right hdet

private lemma controlled_on_first_of_entangled_input (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    {φ w : Vec 4}
  (_hφQ : IsQubit φ) (hEnt : IsEntangled φ)
    (h : (acgate U).mulVec (kronVec ket0 φ : Vec 8) = kronVec ket0 w) :
    ∃ (P₀ P₁ : Square 2),
      P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      U = proj0 ⊗ₖ P₀ + proj1 ⊗ₖ P₁ := by
  let Ub : BlockMatrix 2 := blockify (n := 2) U
  let A : Square 2 := Ub.toBlocks₁₁
  let B : Square 2 := Ub.toBlocks₁₂
  let C : Square 2 := Ub.toBlocks₂₁
  let D : Square 2 := Ub.toBlocks₂₂
  have hUdecomp : U = proj0 ⊗ₖ A + proj01 ⊗ₖ B + proj10 ⊗ₖ C + proj1 ⊗ₖ D := by
    dsimp [A, B, C, D, Ub]
    simpa using (blockDecomposition (n := 2) U)
  have hAcdecomp :
      acgate U =
        proj0 ⊗ₖ ((1 : Square 2) ⊗ₖ A) +
        proj01 ⊗ₖ ((1 : Square 2) ⊗ₖ B) +
        proj10 ⊗ₖ ((1 : Square 2) ⊗ₖ C) +
        proj1 ⊗ₖ ((1 : Square 2) ⊗ₖ D) := by
    rw [hUdecomp]
    repeat rw [acgate_add]
    repeat rw [acgate_kron_two]
  have hLower :
      kronVec ket0 (((1 : Square 2) ⊗ₖ A).mulVec φ) +
        kronVec ket1 (((1 : Square 2) ⊗ₖ C).mulVec φ) = kronVec ket0 w := by
    have h' := h
    rw [hAcdecomp] at h'
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec] at h'
    have h0term : (proj0 ⊗ₖ ((1 : Square 2) ⊗ₖ A)).mulVec (kronVec ket0 φ)
        = kronVec ket0 (((1 : Square 2) ⊗ₖ A).mulVec φ) := by
      simpa [proj0_mulVec_ket0] using
        (kron_mulVec_reindexed (A := proj0) (B := ((1 : Square 2) ⊗ₖ A)) (x := ket0) (y := φ))
    have h01term : (proj01 ⊗ₖ ((1 : Square 2) ⊗ₖ B)).mulVec (kronVec ket0 φ) = 0 := by
      simpa [proj01_mulVec_ket0, kronVec_zero_left] using
        (kron_mulVec_reindexed (A := proj01) (B := ((1 : Square 2) ⊗ₖ B)) (x := ket0) (y := φ))
    have h10term : (proj10 ⊗ₖ ((1 : Square 2) ⊗ₖ C)).mulVec (kronVec ket0 φ)
        = kronVec ket1 (((1 : Square 2) ⊗ₖ C).mulVec φ) := by
      simpa [proj10_mulVec_ket0] using
        (kron_mulVec_reindexed (A := proj10) (B := ((1 : Square 2) ⊗ₖ C)) (x := ket0) (y := φ))
    have h1term : (proj1 ⊗ₖ ((1 : Square 2) ⊗ₖ D)).mulVec (kronVec ket0 φ) = 0 := by
      simpa [proj1_mulVec_ket0, kronVec_zero_left] using
        (kron_mulVec_reindexed (A := proj1) (B := ((1 : Square 2) ⊗ₖ D)) (x := ket0) (y := φ))
    rw [h0term, h01term, h10term, h1term] at h'
    simpa [kronVec_zero_left, kronVec_zero_right, add_assoc] using h'
  have hCphi : ((1 : Square 2) ⊗ₖ C).mulVec φ = 0 := by
    ext i
    fin_cases i
    · simpa [kronVec_vec4_2_apply_4, kronVec_vec4_2_apply_0, ket0, ket1] using congrFun hLower 4
    · simpa [kronVec_vec4_2_apply_5, kronVec_vec4_2_apply_1, ket0, ket1] using congrFun hLower 5
    · simpa [kronVec_vec4_2_apply_6, kronVec_vec4_2_apply_2, ket0, ket1] using congrFun hLower 6
    · simpa [kronVec_vec4_2_apply_7, kronVec_vec4_2_apply_3, ket0, ket1] using congrFun hLower 7
  let u : Vec 2 := ![φ 0, φ 1]
  let v : Vec 2 := ![φ 2, φ 3]
  have hdet : detVec2 u v ≠ 0 := by
    have hdet4 : detVec4 φ ≠ 0 := (isEntangled_iff_detVec4_ne_zero φ).mp hEnt
    simpa [u, v, detVec2, detVec4] using hdet4
  have hCuv : kronVec ket0 (C.mulVec u) + kronVec ket1 (C.mulVec v) = 0 := by
    calc
      kronVec ket0 (C.mulVec u) + kronVec ket1 (C.mulVec v)
          = ((1 : Square 2) ⊗ₖ C).mulVec φ := by
              rw [show φ = kronVec ket0 u + kronVec ket1 v by
                    simpa [u, v] using (vec4_basis_decomp φ),
                Matrix.mulVec_add]
              rw [kron_mulVec_two_two, kron_mulVec_two_two]
              simp [u, v]
      _ = 0 := hCphi
  have hCu : C.mulVec u = 0 := by
    ext i
    fin_cases i
    · simpa [kronVec_vec2_apply_0, kronVec_vec2_apply_2, ket0, ket1] using congrFun hCuv 0
    · simpa [kronVec_vec2_apply_1, kronVec_vec2_apply_3, ket0, ket1] using congrFun hCuv 1
  have hCv : C.mulVec v = 0 := by
    ext i
    fin_cases i
    · simpa [kronVec_vec2_apply_0, kronVec_vec2_apply_2, ket0, ket1] using congrFun hCuv 2
    · simpa [kronVec_vec2_apply_1, kronVec_vec2_apply_3, ket0, ket1] using congrFun hCuv 3
  have hC : C = 0 := zero_matrix_of_mulVec_pair_det_ne_zero C u v hdet hCu hCv
  have hUbUnitary : Ub ∈ Matrix.unitaryGroup (Fin 2 ⊕ Fin 2) ℂ := by
    dsimp [Ub]
    exact (blockify_mem_unitaryGroup_iff (n := 2) (U := U)).2 hU
  have hUbBlocks : Ub = Matrix.fromBlocks A B C D := by
    dsimp [A, B, C, D, Ub]
    symm
    exact Matrix.fromBlocks_toBlocks (blockify (n := 2) U)
  have hUpperUnitary : Matrix.fromBlocks A B 0 D ∈ Matrix.unitaryGroup (Fin 2 ⊕ Fin 2) ℂ := by
    rw [hUbBlocks] at hUbUnitary
    simpa [hC] using hUbUnitary
  have hB : B = 0 := upper_block_zero_of_unitary A B D hUpperUnitary
  have hDiagUnitary : Matrix.fromBlocks A 0 0 D ∈ Matrix.unitaryGroup (Fin 2 ⊕ Fin 2) ℂ := by
    simpa [hB] using hUpperUnitary
  have hAUnitary : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := (block_diagonal_unitary A D hDiagUnitary).1
  have hDUnitary : D ∈ Matrix.unitaryGroup (Fin 2) ℂ := (block_diagonal_unitary A D hDiagUnitary).2
  refine ⟨A, D, hAUnitary, hDUnitary, ?_⟩
  rw [hUdecomp, hB, hC]
  simp [TwoControl.zero_kron_right]

/-- **Lemma 6.1** (Case analysis of a unitary).
For a 2-qubit unitary `V`, either
  (1) there exists a qubit `x` such that `V(x ⊗ |0⟩)` is entangled, or
  (2) there exists a qubit `ψ` such that for all qubits `x`,
      `V(x ⊗ |0⟩) = z ⊗ ψ` for some qubit `z`, or
  (3) there exists a qubit `ψ` such that for all qubits `x`,
      `V(x ⊗ |0⟩) = ψ ⊗ z` for some qubit `z`. -/
lemma section6_lemma_6_1
    (V : Square 4) (hV : V ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    (∃ x : Vec 2, IsQubit x ∧ IsEntangled (V.mulVec (kronVec x ket0))) ∨
    (∃ ψ : Vec 2, IsQubit ψ ∧
      ∀ x : Vec 2, IsQubit x →
        ∃ z : Vec 2, IsQubit z ∧ V.mulVec (kronVec x ket0) = kronVec z ψ) ∨
    (∃ ψ : Vec 2, IsQubit ψ ∧
      ∀ x : Vec 2, IsQubit x →
        ∃ z : Vec 2, IsQubit z ∧ V.mulVec (kronVec x ket0) = kronVec ψ z) := by
  classical
  by_cases hEnt : ∃ x : Vec 2, IsQubit x ∧ IsEntangled (V.mulVec (kronVec x ket0))
  · exact Or.inl hEnt
  · have hProd : ∀ x : Vec 2, IsQubit x → IsProductState (V.mulVec (kronVec x ket0)) := by
      intro x hx
      by_contra hNot
      exact hEnt ⟨x, hx, hNot⟩
    let s : ℂ := (1 / Real.sqrt 2 : ℂ)
    have hsqrt_ne : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
    have hs_ne : s ≠ 0 := by
      dsimp [s]
      exact one_div_ne_zero (by exact_mod_cast hsqrt_ne)
    have hketPlus : ketPlus = s • ket0 + s • ket1 := by
      ext i
      fin_cases i <;> simp [ketPlus, s, ket0, ket1]
    rcases hProd ket0 isQubit_ket0 with ⟨a0, b0, h00⟩
    rcases hProd ket1 isQubit_ket1 with ⟨a1, b1, h10⟩
    rcases hProd ketPlus isQubit_ketPlus with ⟨ap, bp, hPlus⟩
    have hplus_lin :
        V.mulVec (kronVec ketPlus ket0) = s • (V.mulVec (kronVec ket0 ket0) + V.mulVec (kronVec ket1 ket0)) := by
      calc
        V.mulVec (kronVec ketPlus ket0)
            = V.mulVec (kronVec (s • ket0 + s • ket1) ket0) := by rw [hketPlus]
        _ = V.mulVec (s • kronVec ket0 ket0 + s • kronVec ket1 ket0) := by
              rw [kronVec_add_left, kronVec_smul_left, kronVec_smul_left]
        _ = s • V.mulVec (kronVec ket0 ket0) + s • V.mulVec (kronVec ket1 ket0) := by
              rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
        _ = s • (V.mulVec (kronVec ket0 ket0) + V.mulVec (kronVec ket1 ket0)) := by
              simp [smul_add]
    have hsum_det0 :
        detVec4 (V.mulVec (kronVec ket0 ket0) + V.mulVec (kronVec ket1 ket0)) = 0 := by
      have hscaled :
          detVec4 (s • (V.mulVec (kronVec ket0 ket0) + V.mulVec (kronVec ket1 ket0))) = 0 := by
        calc
          detVec4 (s • (V.mulVec (kronVec ket0 ket0) + V.mulVec (kronVec ket1 ket0)))
              = detVec4 (V.mulVec (kronVec ketPlus ket0)) := by rw [hplus_lin]
          _ = detVec4 (kronVec ap bp) := by rw [hPlus]
          _ = 0 := detVec4_kronVec ap bp
      have hmul : s ^ 2 * detVec4 (V.mulVec (kronVec ket0 ket0) + V.mulVec (kronVec ket1 ket0)) = 0 := by
        rw [detVec4_smul] at hscaled
        exact hscaled
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 hs_ne)
    have hdet_prod : detVec2 a0 a1 * detVec2 b0 b1 = 0 := by
      rw [h00, h10, detVec4_add_kronVec] at hsum_det0
      exact hsum_det0
    rcases mul_eq_zero.mp hdet_prod with hA | hB
    · have hu0_ne : V.mulVec (kronVec ket0 ket0) ≠ 0 :=
          mulVec_ne_zero_of_unitary V hV kronVec_ket0_ket0_ne_zero
      have ha0_ne : a0 ≠ 0 := by
        apply left_ne_zero_of_kronVec_ne_zero (a := a0) (b := b0)
        rw [← h00]
        exact hu0_ne
      rcases exists_smul_of_detVec2_eq_zero ha0_ne hA with ⟨c, ha1⟩
      rcases normalize_vec2 a0 ha0_ne with ⟨ψ, hψ, μ, hμ_ne, ha0n⟩
      refine Or.inr <| Or.inr ⟨ψ, hψ, ?_⟩
      intro x hx
      let z0 : Vec 2 := x 0 • b0 + (x 1 * c) • b1
      let z : Vec 2 := μ • z0
      have hx_decomp : x = x 0 • ket0 + x 1 • ket1 := vec2_basis_decomp x
      have hz_eq : V.mulVec (kronVec x ket0) = kronVec ψ z := by
        calc
          V.mulVec (kronVec x ket0)
              = V.mulVec (kronVec (x 0 • ket0 + x 1 • ket1) ket0) := by
                  conv_lhs => rw [hx_decomp]
          _ = V.mulVec (x 0 • kronVec ket0 ket0 + x 1 • kronVec ket1 ket0) := by
                rw [kronVec_add_left, kronVec_smul_left, kronVec_smul_left]
          _ = x 0 • V.mulVec (kronVec ket0 ket0) + x 1 • V.mulVec (kronVec ket1 ket0) := by
                rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
          _ = x 0 • kronVec a0 b0 + x 1 • kronVec a1 b1 := by rw [h00, h10]
          _ = x 0 • kronVec a0 b0 + x 1 • kronVec (c • a0) b1 := by rw [ha1]
          _ = x 0 • kronVec a0 b0 + (x 1 * c) • kronVec a0 b1 := by
                rw [kronVec_smul_left, smul_smul]
          _ = kronVec a0 (x 0 • b0) + kronVec a0 ((x 1 * c) • b1) := by
                rw [← kronVec_smul_right, ← kronVec_smul_right]
          _ = kronVec a0 (x 0 • b0 + (x 1 * c) • b1) := by
                rw [← kronVec_add_right]
          _ = kronVec (μ • ψ) z0 := by rw [ha0n]
          _ = kronVec ψ (μ • z0) := by rw [kronVec_smul_left, ← kronVec_smul_right]
          _ = kronVec ψ z := by rfl
      have hImageQ : IsQubit (V.mulVec (kronVec x ket0)) := by
        exact isQubit_mulVec_of_unitary V hV (isQubit_kron hx isQubit_ket0)
      have hKronQ : IsQubit (kronVec ψ z) := by simpa [hz_eq] using hImageQ
      have hzQ : IsQubit z := isQubit_of_kron_left hKronQ hψ
      exact ⟨z, hzQ, hz_eq⟩
    · have hu0_ne : V.mulVec (kronVec ket0 ket0) ≠ 0 :=
          mulVec_ne_zero_of_unitary V hV kronVec_ket0_ket0_ne_zero
      have hb0_ne : b0 ≠ 0 := by
        apply right_ne_zero_of_kronVec_ne_zero (a := a0) (b := b0)
        rw [← h00]
        exact hu0_ne
      rcases exists_smul_of_detVec2_eq_zero hb0_ne hB with ⟨c, hb1⟩
      rcases normalize_vec2 b0 hb0_ne with ⟨ψ, hψ, μ, hμ_ne, hb0n⟩
      refine Or.inr <| Or.inl ⟨ψ, hψ, ?_⟩
      intro x hx
      let z0 : Vec 2 := x 0 • a0 + (x 1 * c) • a1
      let z : Vec 2 := μ • z0
      have hx_decomp : x = x 0 • ket0 + x 1 • ket1 := vec2_basis_decomp x
      have hz_eq : V.mulVec (kronVec x ket0) = kronVec z ψ := by
        calc
          V.mulVec (kronVec x ket0)
              = V.mulVec (kronVec (x 0 • ket0 + x 1 • ket1) ket0) := by
                  conv_lhs => rw [hx_decomp]
          _ = V.mulVec (x 0 • kronVec ket0 ket0 + x 1 • kronVec ket1 ket0) := by
                rw [kronVec_add_left, kronVec_smul_left, kronVec_smul_left]
          _ = x 0 • V.mulVec (kronVec ket0 ket0) + x 1 • V.mulVec (kronVec ket1 ket0) := by
                rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
          _ = x 0 • kronVec a0 b0 + x 1 • kronVec a1 b1 := by rw [h00, h10]
          _ = x 0 • kronVec a0 b0 + x 1 • kronVec a1 (c • b0) := by rw [hb1]
          _ = x 0 • kronVec a0 b0 + (x 1 * c) • kronVec a1 b0 := by
                rw [kronVec_smul_right, smul_smul]
          _ = kronVec (x 0 • a0) b0 + kronVec ((x 1 * c) • a1) b0 := by
                rw [← kronVec_smul_left, ← kronVec_smul_left]
          _ = kronVec (x 0 • a0 + (x 1 * c) • a1) b0 := by
                rw [← kronVec_add_left]
          _ = kronVec z0 (μ • ψ) := by rw [hb0n]
          _ = kronVec (μ • z0) ψ := by rw [kronVec_smul_right, ← kronVec_smul_left]
          _ = kronVec z ψ := by rfl
      have hImageQ : IsQubit (V.mulVec (kronVec x ket0)) := by
        exact isQubit_mulVec_of_unitary V hV (isQubit_kron hx isQubit_ket0)
      have hKronQ : IsQubit (kronVec z ψ) := by simpa [hz_eq] using hImageQ
      have hzQ : IsQubit z := isQubit_of_kron_right hKronQ hψ
      exact ⟨z, hzQ, hz_eq⟩

private lemma section6_lemma_6_2_branchB
    (U₁ W₂ V₃ U₄ : Square 4)
    (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
  (_hW₂ : W₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₃ : V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hU₄ : U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hbranch : ∃ ψ : Vec 2, IsQubit ψ ∧ ∀ x : Vec 2, IsQubit x →
        ∃ z : Vec 2, IsQubit z ∧ V₃†.mulVec (kronVec x ket0) = kronVec z ψ) :
    ∃ (W₁ W₃ W₄ : Square 4),
      W₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      W₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      W₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      ∃ (P₃ : Square 2), P₃ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄ =
          acgate W₁ * bcgate W₂ * acgate W₃ * bcgate W₄ ∧
        W₃ = (1 : Square 2) ⊗ₖ proj0 + P₃ ⊗ₖ proj1 := by
  rcases hbranch with ⟨ψ, hψ, hbranchψ⟩
  rcases exists_unitary_of_fixed_right_factor V₃† (conjTranspose_mem_unitaryGroup hV₃) hψ hbranchψ with
    ⟨Q, hQ, hQprop⟩
  let R : Square 2 := colMatrix ψ (qubitPerp ψ)
  have hR : R ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    dsimp [R]
    exact qubit_basis_unitary ψ hψ
  let Wd : Square 4 := ((1 : Square 2) ⊗ₖ R†) * V₃† * (Q† ⊗ₖ (1 : Square 2))
  have hWd : Wd ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    dsimp [Wd]
    refine Submonoid.mul_mem _ ?_ (kron_unitary_two _ _ (conjTranspose_mem_unitaryGroup hQ) (Submonoid.one_mem _))
    exact Submonoid.mul_mem _
      (kron_unitary_two _ _ (Submonoid.one_mem _) (conjTranspose_mem_unitaryGroup hR))
      (conjTranspose_mem_unitaryGroup hV₃)
  have hWd_fix : ∀ x : Vec 2, IsQubit x → Wd.mulVec (kronVec x ket0) = kronVec x ket0 := by
    intro x hx
    have hQx : IsQubit (Q†.mulVec x) := by
      exact isQubit_mulVec_of_unitary Q† (conjTranspose_mem_unitaryGroup hQ) hx
    have hQQx : Q.mulVec (Q†.mulVec x) = x := by
      have hright : Q * Q† = (1 : Square 2) := Matrix.mem_unitaryGroup_iff.mp hQ
      calc
        Q.mulVec (Q†.mulVec x) = (Q * Q†).mulVec x := by rw [← Matrix.mulVec_mulVec]
        _ = (1 : Square 2).mulVec x := by rw [hright]
        _ = x := by simp
    calc
      Wd.mulVec (kronVec x ket0)
          = (((1 : Square 2) ⊗ₖ R†) * V₃† * (Q† ⊗ₖ (1 : Square 2))).mulVec (kronVec x ket0) := by rfl
      _ = (((1 : Square 2) ⊗ₖ R†) * V₃†).mulVec ((Q† ⊗ₖ (1 : Square 2)).mulVec (kronVec x ket0)) := by
            rw [Matrix.mulVec_mulVec, mul_assoc]
      _ = (((1 : Square 2) ⊗ₖ R†) * V₃†).mulVec (kronVec (Q†.mulVec x) ket0) := by
            rw [kron_mulVec_two_two]
            simp
      _ = ((1 : Square 2) ⊗ₖ R†).mulVec (V₃†.mulVec (kronVec (Q†.mulVec x) ket0)) := by
            rw [Matrix.mulVec_mulVec]
      _ = ((1 : Square 2) ⊗ₖ R†).mulVec (kronVec (Q.mulVec (Q†.mulVec x)) ψ) := by
            rw [hQprop _ hQx]
      _ = ((1 : Square 2) ⊗ₖ R†).mulVec (kronVec x ψ) := by rw [hQQx]
      _ = kronVec x (R†.mulVec ψ) := by
        rw [kron_mulVec_two_two]
        simp
      _ = kronVec x ket0 := by
            rw [colMatrix_conjTranspose_mulVec_left _ _ hR]
  have hWd0 : Wd.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0 := hWd_fix ket0 isQubit_ket0
  have hWd1 : Wd.mulVec (kronVec ket1 ket0) = kronVec ket1 ket0 := hWd_fix ket1 isQubit_ket1
  rcases controlled_on_second_of_fixing_basis Wd hWd hWd0 hWd1 with ⟨P₃, hP₃, hWdEq⟩
  let W₁ : Square 4 := U₁ * (Q† ⊗ₖ (1 : Square 2))
  let W₃ : Square 4 := Wd†
  let W₄ : Square 4 := ((1 : Square 2) ⊗ₖ R†) * U₄
  have hW₁ : W₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    dsimp [W₁]
    exact Submonoid.mul_mem _ hU₁
      (kron_unitary_two _ _ (conjTranspose_mem_unitaryGroup hQ) (Submonoid.one_mem _))
  have hW₃ : W₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    dsimp [W₃]
    exact conjTranspose_mem_unitaryGroup hWd
  have hW₄ : W₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    dsimp [W₄]
    exact Submonoid.mul_mem _
      (kron_unitary_two _ _ (Submonoid.one_mem _) (conjTranspose_mem_unitaryGroup hR))
      hU₄
  have hW₃eq : W₃ = (1 : Square 2) ⊗ₖ proj0 + P₃† ⊗ₖ proj1 := by
    dsimp [W₃]
    have hAdj := congrArg Matrix.conjTranspose hWdEq
    rw [Matrix.conjTranspose_add, conjTranspose_kron_two, conjTranspose_kron_two] at hAdj
    simpa using hAdj
  have hQQ : (Q† ⊗ₖ (1 : Square 2)) * (Q ⊗ₖ (1 : Square 2)) = (1 : Square 4) := by
    have hQleft : Q† * Q = (1 : Square 2) := Matrix.mem_unitaryGroup_iff'.mp hQ
    rw [← kron_mul_two, hQleft]
    simpa using (TwoControl.one_kron_one 2 2)
  have hRR : ((1 : Square 2) ⊗ₖ R) * ((1 : Square 2) ⊗ₖ R†) = (1 : Square 4) := by
    have hRright : R * R† = (1 : Square 2) := Matrix.mem_unitaryGroup_iff.mp hR
    rw [← kron_mul_two, hRright]
    simpa using (TwoControl.one_kron_one 2 2)
  have hV₃_expand : (Q† ⊗ₖ (1 : Square 2)) * W₃ * ((1 : Square 2) ⊗ₖ R†) = V₃ := by
    dsimp [W₃, Wd]
    calc
      (Q† ⊗ₖ (1 : Square 2)) * (((((1 : Square 2) ⊗ₖ R†) * V₃† * (Q† ⊗ₖ (1 : Square 2)))†)) *
          ((1 : Square 2) ⊗ₖ R†)
          = (Q† ⊗ₖ (1 : Square 2)) * ((Q ⊗ₖ (1 : Square 2)) * V₃ * ((1 : Square 2) ⊗ₖ R)) *
              ((1 : Square 2) ⊗ₖ R†) := by
                rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, conjTranspose_kron_two,
                  conjTranspose_kron_two]
                simp [mul_assoc]
      _ = ((Q† ⊗ₖ (1 : Square 2)) * (Q ⊗ₖ (1 : Square 2))) * V₃ *
            (((1 : Square 2) ⊗ₖ R) * ((1 : Square 2) ⊗ₖ R†)) := by
              simp [mul_assoc]
      _ = (1 : Square 4) * V₃ * (1 : Square 4) := by rw [hQQ, hRR]
      _ = V₃ := by simp
  refine ⟨W₁, W₃, W₄, hW₁, hW₃, hW₄, P₃†, conjTranspose_mem_unitaryGroup hP₃, ?_, hW₃eq⟩
  calc
    acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄
        = acgate U₁ * bcgate W₂ * acgate ((Q† ⊗ₖ (1 : Square 2)) * W₃ * ((1 : Square 2) ⊗ₖ R†)) * bcgate U₄ := by
            rw [hV₃_expand]
    _ = acgate U₁ * bcgate W₂ * acgate (Q† ⊗ₖ (1 : Square 2)) * acgate W₃ *
          acgate ((1 : Square 2) ⊗ₖ R†) * bcgate U₄ := by
            simp [acgate_mul, mul_assoc]
    _ = acgate U₁ * acgate (Q† ⊗ₖ (1 : Square 2)) * bcgate W₂ * acgate W₃ *
          acgate ((1 : Square 2) ⊗ₖ R†) * bcgate U₄ := by
            calc
              acgate U₁ * bcgate W₂ * acgate (Q† ⊗ₖ (1 : Square 2)) * acgate W₃ *
                    acgate ((1 : Square 2) ⊗ₖ R†) * bcgate U₄
                  = acgate U₁ * (bcgate W₂ * acgate (Q† ⊗ₖ (1 : Square 2))) * acgate W₃ *
                      acgate ((1 : Square 2) ⊗ₖ R†) * bcgate U₄ := by simp [mul_assoc]
              _ = acgate U₁ * (acgate (Q† ⊗ₖ (1 : Square 2)) * bcgate W₂) * acgate W₃ *
                      acgate ((1 : Square 2) ⊗ₖ R†) * bcgate U₄ := by
                    rw [acgate_localA_commute_bcgate]
              _ = acgate U₁ * acgate (Q† ⊗ₖ (1 : Square 2)) * bcgate W₂ * acgate W₃ *
                      acgate ((1 : Square 2) ⊗ₖ R†) * bcgate U₄ := by simp [mul_assoc]
    _ = acgate U₁ * acgate (Q† ⊗ₖ (1 : Square 2)) * bcgate W₂ * acgate W₃ *
          bcgate ((1 : Square 2) ⊗ₖ R†) * bcgate U₄ := by
            rw [acgate_localC_eq]
    _ = acgate W₁ * bcgate W₂ * acgate W₃ * bcgate W₄ := by
          dsimp [W₁, W₄]
          calc
            acgate U₁ * acgate (Q† ⊗ₖ (1 : Square 2)) * bcgate W₂ * acgate W₃ *
                  bcgate ((1 : Square 2) ⊗ₖ R†) * bcgate U₄
                = acgate (U₁ * (Q† ⊗ₖ (1 : Square 2))) * bcgate W₂ * acgate W₃ *
                    bcgate ((1 : Square 2) ⊗ₖ R†) * bcgate U₄ := by
                      rw [← acgate_mul]
            _ = acgate (U₁ * (Q† ⊗ₖ (1 : Square 2))) * bcgate W₂ * acgate W₃ *
                    bcgate (((1 : Square 2) ⊗ₖ R†) * U₄) := by
                      calc
                        acgate (U₁ * (Q† ⊗ₖ (1 : Square 2))) * bcgate W₂ * acgate W₃ *
                              bcgate ((1 : Square 2) ⊗ₖ R†) * bcgate U₄
                            = acgate (U₁ * (Q† ⊗ₖ (1 : Square 2))) * bcgate W₂ * acgate W₃ *
                                (bcgate ((1 : Square 2) ⊗ₖ R†) * bcgate U₄) := by
                                  simp [mul_assoc]
                        _ = acgate (U₁ * (Q† ⊗ₖ (1 : Square 2))) * bcgate W₂ * acgate W₃ *
                                bcgate (((1 : Square 2) ⊗ₖ R†) * U₄) := by
                                  rw [← bcgate_mul]
            _ = acgate W₁ * bcgate W₂ * acgate W₃ * bcgate W₄ := by simp [W₁, W₄, mul_assoc]

private lemma section6_lemma_6_2_caseC
    (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (U₁ W₂ V₃ U₄ : Square 4)
    (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hW₂ : W₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₃ : V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hU₄ : U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (heq : acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄ = ccu (diag2 u₀ u₁))
    (hident : ∀ x : Vec 2, IsQubit x →
      (acgate U₁).mulVec (kronVec (kronVec x ket0) ket0) =
      (bcgate U₄† * acgate V₃†).mulVec (kronVec (kronVec x ket0) ket0))
    (hbranch : ∃ ψ : Vec 2, IsQubit ψ ∧ ∀ x : Vec 2, IsQubit x →
        ∃ z : Vec 2, IsQubit z ∧ V₃†.mulVec (kronVec x ket0) = kronVec ψ z) :
    u₀ = u₁ ∨ u₀ * u₁ = 1 := by
  rcases hbranch with ⟨ψ, hψ, hbranchψ⟩
  rcases exists_unitary_of_fixed_left_factor V₃† (conjTranspose_mem_unitaryGroup hV₃) hψ hbranchψ with
    ⟨Q, hQ, hQprop⟩
  have hβ0 : IsQubit (Q.mulVec ket0) := by
    exact isQubit_mulVec_of_unitary Q hQ isQubit_ket0
  have hβ1 : IsQubit (Q.mulVec ket1) := by
    exact isQubit_mulVec_of_unitary Q hQ isQubit_ket1
  have hβorth : star (Q.mulVec ket0) ⬝ᵥ Q.mulVec ket1 = 0 := by
    have hpres := dot_mulVec_of_unitary Q hQ ket0 ket1
    simpa [dotProduct, ket0, ket1, Fin.sum_univ_two] using hpres
  have hrhs : ∀ x : Vec 2, IsQubit x →
      (bcgate U₄† * acgate V₃†).mulVec (kronVec (kronVec x ket0) ket0) =
        kronVec ψ (U₄†.mulVec (kronVec ket0 (Q.mulVec x))) := by
    intro x hx
    have hV3x := acgate_mulVec_of_product V₃† x ket0 ket0 ψ (Q.mulVec x) (hQprop _ hx)
    calc
      (bcgate U₄† * acgate V₃†).mulVec (kronVec (kronVec x ket0) ket0)
          = (bcgate U₄†).mulVec ((acgate V₃†).mulVec (kronVec (kronVec x ket0) ket0)) := by
              rw [Matrix.mulVec_mulVec]
      _ = (bcgate U₄†).mulVec (kronVec (kronVec ψ ket0) (Q.mulVec x)) := by
            rw [hV3x]
      _ = kronVec ψ (U₄†.mulVec (kronVec ket0 (Q.mulVec x))) := by
            rw [kronVec_assoc_222]
            rw [bcgate_mulVec_kronVec]
  have hφ0Q : IsQubit (U₄†.mulVec (kronVec ket0 (Q.mulVec ket0))) := by
    exact isQubit_mulVec_of_unitary U₄† (conjTranspose_mem_unitaryGroup hU₄) (isQubit_kron isQubit_ket0 hβ0)
  have hφ1Q : IsQubit (U₄†.mulVec (kronVec ket0 (Q.mulVec ket1))) := by
    exact isQubit_mulVec_of_unitary U₄† (conjTranspose_mem_unitaryGroup hU₄) (isQubit_kron isQubit_ket0 hβ1)
  rcases acgate_suffix_ket0 U₁ ket0 ψ (U₄†.mulVec (kronVec ket0 (Q.mulVec ket0)))
      isQubit_ket0 hψ hφ0Q (by simpa [hrhs ket0 isQubit_ket0] using hident ket0 isQubit_ket0) with
    ⟨w0, hw0, hw0eq⟩
  rcases acgate_suffix_ket0 U₁ ket1 ψ (U₄†.mulVec (kronVec ket0 (Q.mulVec ket1)))
      isQubit_ket1 hψ hφ1Q (by simpa [hrhs ket1 isQubit_ket1] using hident ket1 isQubit_ket1) with
    ⟨w1, hw1, hw1eq⟩
  rcases controlled_on_first_of_two_images U₄† (conjTranspose_mem_unitaryGroup hU₄)
      hβ0 hβ1 hβorth hw0 hw1 hw0eq hw1eq with ⟨P₀, P₁, hP₀, hP₁, hU₄dagEq⟩
  have hU₄eq : U₄ = proj0 ⊗ₖ P₀† + proj1 ⊗ₖ P₁† := by
    have hAdj := congrArg Matrix.conjTranspose hU₄dagEq
    rw [Matrix.conjTranspose_add, conjTranspose_kron_two, conjTranspose_kron_two] at hAdj
    simpa using hAdj
  have hScalar : u₀ = u₁ ∨ u₀ * u₁ = 1 :=
    (section4_lemma_4_4 u₀ u₁ hu₀ hu₁).1 <| by
      refine ⟨U₁, W₂, V₃, U₄, hU₁, hW₂, hV₃, hU₄, P₀†, P₁†,
        conjTranspose_mem_unitaryGroup hP₀, conjTranspose_mem_unitaryGroup hP₁, hU₄eq, heq⟩
  exact hScalar

private lemma section6_lemma_6_2_caseA
    (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (U₁ W₂ V₃ U₄ : Square 4)
    (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hW₂ : W₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₃ : V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hU₄ : U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (heq : acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄ = ccu (diag2 u₀ u₁))
    (hident : ∀ x : Vec 2, IsQubit x →
      (acgate U₁).mulVec (kronVec (kronVec x ket0) ket0) =
      (bcgate U₄† * acgate V₃†).mulVec (kronVec (kronVec x ket0) ket0))
    (hbranch : ∃ x : Vec 2, IsQubit x ∧ IsEntangled (V₃†.mulVec (kronVec x ket0))) :
    u₀ = u₁ ∨ u₀ * u₁ = 1 := by
  rcases hbranch with ⟨x, hx, hEnt⟩
  let φ : Vec 4 := V₃†.mulVec (kronVec x ket0)
  let w : Vec 4 := U₁.mulVec (kronVec x ket0)
  have hφQ : IsQubit φ := by
    dsimp [φ]
    exact isQubit_mulVec_of_unitary V₃† (conjTranspose_mem_unitaryGroup hV₃) (isQubit_kron hx isQubit_ket0)
  have hswap_acU₁ : swapab * acgate U₁ = bcgate U₁ * swapab := by
    calc
      swapab * acgate U₁ = swapab * acgate U₁ * (swapab * swapab) := by rw [swapab_mul_swapab]; simp
      _ = (swapab * acgate U₁ * swapab) * swapab := by simp [mul_assoc]
      _ = bcgate U₁ * swapab := by rw [swapab_conj_acgate]
  have hswap_bcU₄ : swapab * bcgate U₄† = acgate U₄† * swapab := by
    calc
      swapab * bcgate U₄† = swapab * bcgate U₄† * (swapab * swapab) := by rw [swapab_mul_swapab]; simp
      _ = (swapab * bcgate U₄† * swapab) * swapab := by simp [mul_assoc]
      _ = acgate U₄† * swapab := by rw [swapab_conj_bcgate]
  have hswap_acV₃ : swapab * acgate V₃† = bcgate V₃† * swapab := by
    calc
      swapab * acgate V₃† = swapab * acgate V₃† * (swapab * swapab) := by rw [swapab_mul_swapab]; simp
      _ = (swapab * acgate V₃† * swapab) * swapab := by simp [mul_assoc]
      _ = bcgate V₃† * swapab := by rw [swapab_conj_acgate]
  have hswap_word : swapab * (bcgate U₄† * acgate V₃†) = acgate U₄† * bcgate V₃† * swapab := by
    calc
      swapab * (bcgate U₄† * acgate V₃†) = (swapab * bcgate U₄†) * acgate V₃† := by simp [mul_assoc]
      _ = (acgate U₄† * swapab) * acgate V₃† := by rw [hswap_bcU₄]
      _ = acgate U₄† * (swapab * acgate V₃†) := by simp [mul_assoc]
      _ = acgate U₄† * (bcgate V₃† * swapab) := by rw [hswap_acV₃]
      _ = acgate U₄† * bcgate V₃† * swapab := by simp [mul_assoc]
  have hswap :
      (bcgate U₁).mulVec (kronVec (kronVec ket0 x) ket0) =
        (acgate U₄† * bcgate V₃†).mulVec (kronVec (kronVec ket0 x) ket0) := by
    let t : Vec 8 := kronVec (kronVec x ket0) ket0
    calc
      (bcgate U₁).mulVec (kronVec (kronVec ket0 x) ket0)
          = (bcgate U₁).mulVec (swapab.mulVec t) := by
              dsimp [t]
              rw [swapab_mulVec_kronVec]
      _ = (bcgate U₁ * swapab).mulVec t := by rw [Matrix.mulVec_mulVec]
      _ = (swapab * acgate U₁).mulVec t := by rw [hswap_acU₁]
      _ = swapab.mulVec ((acgate U₁).mulVec t) := by rw [Matrix.mulVec_mulVec]
      _ = swapab.mulVec ((bcgate U₄† * acgate V₃†).mulVec t) := by
            dsimp [t]
            rw [hident x hx]
      _ = (swapab * (bcgate U₄† * acgate V₃†)).mulVec t := by rw [Matrix.mulVec_mulVec]
      _ = (acgate U₄† * bcgate V₃† * swapab).mulVec t := by rw [hswap_word]
      _ = (acgate U₄† * bcgate V₃†).mulVec (swapab.mulVec t) := by rw [Matrix.mulVec_mulVec]
      _ = (acgate U₄† * bcgate V₃†).mulVec (kronVec (kronVec ket0 x) ket0) := by
            dsimp [t]
            rw [swapab_mulVec_kronVec]
  have hLeft : (bcgate U₁).mulVec (kronVec (kronVec ket0 x) ket0) = kronVec ket0 w := by
    dsimp [w]
    rw [kronVec_assoc_222, bcgate_mulVec_kronVec]
  have hRight : (acgate U₄† * bcgate V₃†).mulVec (kronVec (kronVec ket0 x) ket0) =
      (acgate U₄†).mulVec (kronVec ket0 φ) := by
    calc
      (acgate U₄† * bcgate V₃†).mulVec (kronVec (kronVec ket0 x) ket0)
          = (acgate U₄†).mulVec ((bcgate V₃†).mulVec (kronVec (kronVec ket0 x) ket0)) := by
              rw [Matrix.mulVec_mulVec]
      _ = (acgate U₄†).mulVec (kronVec ket0 (V₃†.mulVec (kronVec x ket0))) := by
        rw [kronVec_assoc_222, bcgate_mulVec_kronVec]
      _ = (acgate U₄†).mulVec (kronVec ket0 φ) := by rfl
  have hEntEq : (acgate U₄†).mulVec (kronVec ket0 φ : Vec 8) = kronVec ket0 w := by
    calc
      (acgate U₄†).mulVec (kronVec ket0 φ : Vec 8)
          = (acgate U₄† * bcgate V₃†).mulVec (kronVec (kronVec ket0 x) ket0) := hRight.symm
      _ = (bcgate U₁).mulVec (kronVec (kronVec ket0 x) ket0) := hswap.symm
      _ = kronVec ket0 w := hLeft
  rcases controlled_on_first_of_entangled_input U₄† (conjTranspose_mem_unitaryGroup hU₄) hφQ hEnt hEntEq with
    ⟨P₀, P₁, hP₀, hP₁, hU₄dagEq⟩
  have hU₄eq : U₄ = proj0 ⊗ₖ P₀† + proj1 ⊗ₖ P₁† := by
    have hAdj := congrArg Matrix.conjTranspose hU₄dagEq
    rw [Matrix.conjTranspose_add, conjTranspose_kron_two, conjTranspose_kron_two] at hAdj
    simpa using hAdj
  have hScalar : u₀ = u₁ ∨ u₀ * u₁ = 1 :=
    (section4_lemma_4_4 u₀ u₁ hu₀ hu₁).1 <| by
      refine ⟨U₁, W₂, V₃, U₄, hU₁, hW₂, hV₃, hU₄, P₀†, P₁†,
        conjTranspose_mem_unitaryGroup hP₀, conjTranspose_mem_unitaryGroup hP₁, hU₄eq, heq⟩
  exact hScalar

/-- **Lemma 6.2**.
Suppose `|u₀| = |u₁| = 1`. For 2-qubit unitaries `U₁, W₂, V₃, U₄`, if
  `U₁^{AC} W₂^{BC} V₃^{AC} U₄^{BC} = CC(Diag(u₀, u₁))`,
  `V₃(|0⟩ ⊗ |0⟩) = |0⟩ ⊗ |0⟩`, and
  `∀ x, U₁^{AC}(x ⊗ |0⟩ ⊗ |0⟩) = U₄^{BC†} V₃^{AC†}(x ⊗ |0⟩ ⊗ |0⟩)`,
then either `u₀ = u₁` or `u₀ u₁ = 1` or there exist unitaries `W₁, W₃, W₄, P₃`
such that `U₁^{AC} W₂^{BC} V₃^{AC} U₄^{BC} = W₁^{AC} W₂^{BC} W₃^{AC} W₄^{BC}`
and `W₃ = I ⊗ |0⟩⟨0| + P₃ ⊗ |1⟩⟨1|`. -/
lemma section6_lemma_6_2
    (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (U₁ W₂ V₃ U₄ : Square 4)
    (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hW₂ : W₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₃ : V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hU₄ : U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (heq : acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄ = ccu (diag2 u₀ u₁))
    (hident : ∀ x : Vec 2, IsQubit x →
      (acgate U₁).mulVec (kronVec (kronVec x ket0) ket0) =
      (bcgate U₄† * acgate V₃†).mulVec (kronVec (kronVec x ket0) ket0)) :
    u₀ = u₁ ∨ u₀ * u₁ = 1 ∨
    ∃ (W₁ W₃ W₄ : Square 4),
      W₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      W₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      W₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      ∃ (P₃ : Square 2), P₃ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄ =
          acgate W₁ * bcgate W₂ * acgate W₃ * bcgate W₄ ∧
        W₃ = (1 : Square 2) ⊗ₖ proj0 + P₃ ⊗ₖ proj1 := by
  rcases section6_lemma_6_1 V₃† (conjTranspose_mem_unitaryGroup hV₃) with hA | hB | hC
  · rcases section6_lemma_6_2_caseA u₀ u₁ hu₀ hu₁ U₁ W₂ V₃ U₄ hU₁ hW₂ hV₃ hU₄ heq hident hA with hEq | hProd
    · exact Or.inl hEq
    · exact Or.inr (Or.inl hProd)
  · exact Or.inr (Or.inr (section6_lemma_6_2_branchB U₁ W₂ V₃ U₄ hU₁ hW₂ hV₃ hU₄ hB))
  · rcases section6_lemma_6_2_caseC u₀ u₁ hu₀ hu₁ U₁ W₂ V₃ U₄ hU₁ hW₂ hV₃ hU₄ heq hident hC with hEq | hProd
    · exact Or.inl hEq
    · exact Or.inr (Or.inl hProd)

private lemma section6_lemma_6_3_normalize_V₂
    (V₁ V₂ V₃ V₄ : Square 4)
    (hV₁ : V₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₂ : V₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₄ : V₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₂_struct : ∃ ψ : Vec 2, IsQubit ψ ∧
      ∀ x : Vec 2, IsQubit x →
        ∃ z : Vec 2, IsQubit z ∧ V₂.mulVec (kronVec x ket0) = kronVec z ψ) :
    ∃ (U₁ W₂ U₄ : Square 4),
      U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      W₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      ∃ (P₂ : Square 2), P₂ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ =
          acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄ ∧
        W₂ = (1 : Square 2) ⊗ₖ proj0 + P₂ ⊗ₖ proj1 := by
  rcases hV₂_struct with ⟨ψ, hψ, hV₂ψ⟩
  rcases exists_unitary_of_fixed_right_factor V₂ hV₂ hψ hV₂ψ with ⟨Q, hQ, hQprop⟩
  let R : Square 2 := colMatrix ψ (qubitPerp ψ)
  have hR : R ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    dsimp [R]
    exact qubit_basis_unitary ψ hψ
  let W₂ : Square 4 := ((1 : Square 2) ⊗ₖ R†) * V₂ * (Q† ⊗ₖ (1 : Square 2))
  have hW₂ : W₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    dsimp [W₂]
    refine Submonoid.mul_mem _ ?_ (kron_unitary_two _ _ (conjTranspose_mem_unitaryGroup hQ) (Submonoid.one_mem _))
    exact Submonoid.mul_mem _
      (kron_unitary_two _ _ (Submonoid.one_mem _) (conjTranspose_mem_unitaryGroup hR))
      hV₂
  have hW₂_fix : ∀ x : Vec 2, IsQubit x → W₂.mulVec (kronVec x ket0) = kronVec x ket0 := by
    intro x hx
    have hQx : IsQubit (Q†.mulVec x) := by
      exact isQubit_mulVec_of_unitary Q† (conjTranspose_mem_unitaryGroup hQ) hx
    have hQQx : Q.mulVec (Q†.mulVec x) = x := by
      have hleft : Q * Q† = (1 : Square 2) := Matrix.mem_unitaryGroup_iff.mp hQ
      calc
        Q.mulVec (Q†.mulVec x) = (Q * Q†).mulVec x := by rw [← Matrix.mulVec_mulVec]
        _ = (1 : Square 2).mulVec x := by rw [hleft]
        _ = x := by simp
    calc
      W₂.mulVec (kronVec x ket0)
          = (((1 : Square 2) ⊗ₖ R†) * V₂ * (Q† ⊗ₖ (1 : Square 2))).mulVec (kronVec x ket0) := by rfl
      _ = (((1 : Square 2) ⊗ₖ R†) * V₂).mulVec ((Q† ⊗ₖ (1 : Square 2)).mulVec (kronVec x ket0)) := by
            rw [Matrix.mulVec_mulVec, mul_assoc]
      _ = (((1 : Square 2) ⊗ₖ R†) * V₂).mulVec (kronVec (Q†.mulVec x) ket0) := by
            rw [kron_mulVec_two_two]
            simp
      _ = ((1 : Square 2) ⊗ₖ R†).mulVec (V₂.mulVec (kronVec (Q†.mulVec x) ket0)) := by
            rw [Matrix.mulVec_mulVec]
      _ = ((1 : Square 2) ⊗ₖ R†).mulVec (kronVec (Q.mulVec (Q†.mulVec x)) ψ) := by
            rw [hQprop _ hQx]
      _ = ((1 : Square 2) ⊗ₖ R†).mulVec (kronVec x ψ) := by rw [hQQx]
      _ = kronVec x (R†.mulVec ψ) := by
            rw [kron_mulVec_two_two]
            simp
      _ = kronVec x ket0 := by
            rw [colMatrix_conjTranspose_mulVec_left _ _ hR]
  have hW₂0 : W₂.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0 := hW₂_fix ket0 isQubit_ket0
  have hW₂1 : W₂.mulVec (kronVec ket1 ket0) = kronVec ket1 ket0 := hW₂_fix ket1 isQubit_ket1
  rcases controlled_on_second_of_fixing_basis W₂ hW₂ hW₂0 hW₂1 with ⟨P₂, hP₂, hW₂eq⟩
  let U₁ : Square 4 := V₁ * ((1 : Square 2) ⊗ₖ R)
  let U₄ : Square 4 := (Q ⊗ₖ (1 : Square 2)) * V₄
  have hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    dsimp [U₁]
    exact Submonoid.mul_mem _ hV₁
      (kron_unitary_two _ _ (Submonoid.one_mem _) hR)
  have hU₄ : U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    dsimp [U₄]
    exact Submonoid.mul_mem _
      (kron_unitary_two _ _ hQ (Submonoid.one_mem _))
      hV₄
  have hRR : ((1 : Square 2) ⊗ₖ R) * ((1 : Square 2) ⊗ₖ R†) = (1 : Square 4) := by
    have hright : R * R† = (1 : Square 2) := Matrix.mem_unitaryGroup_iff.mp hR
    rw [← kron_mul_two, hright]
    simpa using (TwoControl.one_kron_one 2 2)
  have hQQ : (Q† ⊗ₖ (1 : Square 2)) * (Q ⊗ₖ (1 : Square 2)) = (1 : Square 4) := by
    have hleft : Q† * Q = (1 : Square 2) := Matrix.mem_unitaryGroup_iff'.mp hQ
    rw [← kron_mul_two, hleft]
    simpa using (TwoControl.one_kron_one 2 2)
  have hV₂_expand : ((1 : Square 2) ⊗ₖ R) * W₂ * (Q ⊗ₖ (1 : Square 2)) = V₂ := by
    dsimp [W₂]
    calc
      ((1 : Square 2) ⊗ₖ R) * ((((1 : Square 2) ⊗ₖ R†) * V₂ * (Q† ⊗ₖ (1 : Square 2)))) *
          (Q ⊗ₖ (1 : Square 2))
          = (((1 : Square 2) ⊗ₖ R) * ((1 : Square 2) ⊗ₖ R†)) * V₂ *
              ((Q† ⊗ₖ (1 : Square 2)) * (Q ⊗ₖ (1 : Square 2))) := by
                simp [mul_assoc]
      _ = (1 : Square 4) * V₂ * (1 : Square 4) := by rw [hRR, hQQ]
      _ = V₂ := by simp
  refine ⟨U₁, W₂, U₄, hU₁, hW₂, hU₄, P₂, hP₂, ?_, hW₂eq⟩
  calc
    acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄
        = acgate V₁ * bcgate (((1 : Square 2) ⊗ₖ R) * W₂ * (Q ⊗ₖ (1 : Square 2))) * acgate V₃ * bcgate V₄ := by
            rw [hV₂_expand]
    _ = acgate V₁ * bcgate ((1 : Square 2) ⊗ₖ R) * bcgate W₂ * bcgate (Q ⊗ₖ (1 : Square 2)) *
          acgate V₃ * bcgate V₄ := by
            simp [bcgate_mul, mul_assoc]
    _ = acgate V₁ * acgate ((1 : Square 2) ⊗ₖ R) * bcgate W₂ * bcgate (Q ⊗ₖ (1 : Square 2)) *
          acgate V₃ * bcgate V₄ := by
            rw [← acgate_localC_eq]
    _ = acgate U₁ * bcgate W₂ * bcgate (Q ⊗ₖ (1 : Square 2)) * acgate V₃ * bcgate V₄ := by
          dsimp [U₁]
          rw [← acgate_mul]
    _ = acgate U₁ * bcgate W₂ * acgate V₃ * bcgate (Q ⊗ₖ (1 : Square 2)) * bcgate V₄ := by
          calc
            acgate U₁ * bcgate W₂ * bcgate (Q ⊗ₖ (1 : Square 2)) * acgate V₃ * bcgate V₄
                = acgate U₁ * bcgate W₂ * (bcgate (Q ⊗ₖ (1 : Square 2)) * acgate V₃) * bcgate V₄ := by
                    simp [mul_assoc]
            _ = acgate U₁ * bcgate W₂ * (acgate V₃ * bcgate (Q ⊗ₖ (1 : Square 2))) * bcgate V₄ := by
                    rw [bcgate_localB_commute_acgate]
            _ = acgate U₁ * bcgate W₂ * acgate V₃ * bcgate (Q ⊗ₖ (1 : Square 2)) * bcgate V₄ := by
                    simp [mul_assoc]
    _ = acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄ := by
          dsimp [U₄]
          calc
            acgate U₁ * bcgate W₂ * acgate V₃ * bcgate (Q ⊗ₖ (1 : Square 2)) * bcgate V₄
                = acgate U₁ * bcgate W₂ * acgate V₃ * (bcgate (Q ⊗ₖ (1 : Square 2)) * bcgate V₄) := by
                    simp [mul_assoc]
            _ = acgate U₁ * bcgate W₂ * acgate V₃ * bcgate ((Q ⊗ₖ (1 : Square 2)) * V₄) := by
                    rw [← bcgate_mul]
            _ = acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄ := by rfl

@[simp] private lemma controlledGate_diag2_conjTranspose_local (u₀ u₁ : ℂ) :
    (controlledGate (diag2 u₀ u₁))† = controlledGate (diag2 (star u₀) (star u₁)) := by
  rw [controlledGate_diag2_eq, controlledGate_diag2_eq]
  simp

private lemma ccu_diag2_conjTranspose_local (u₀ u₁ : ℂ) :
    (ccu (diag2 u₀ u₁))† = ccu (diag2 (star u₀) (star u₁)) := by
  rw [ccu, ccu, Matrix.conjTranspose_add, conjTranspose_kron_reindex,
    conjTranspose_kron_reindex, controlledGate_diag2_conjTranspose_local]
  simp

@[simp] private lemma abgate_one : abgate (1 : Square 4) = (1 : Square 8) := by
  unfold abgate
  simpa using (TwoControl.one_kron_one 4 2)

@[simp] private lemma bcgate_one : bcgate (1 : Square 4) = (1 : Square 8) := by
  unfold bcgate
  simpa using (TwoControl.one_kron_one 2 4)

@[simp] private lemma acgate_one : acgate (1 : Square 4) = (1 : Square 8) := by
  unfold acgate
  rw [abgate_one]
  simp [swapbc_mul_swapbc]

private lemma controlledGate_mulVec_left_zero (u₀ u₁ : ℂ) (x : Vec 2) :
    (controlledGate (diag2 u₀ u₁)).mulVec (kronVec ket0 x) = kronVec ket0 x := by
  unfold controlledGate
  calc
    (proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ diag2 u₀ u₁).mulVec (kronVec ket0 x)
        = (proj0 ⊗ₖ (1 : Square 2)).mulVec (kronVec ket0 x) +
            (proj1 ⊗ₖ diag2 u₀ u₁).mulVec (kronVec ket0 x) := by
              rw [Matrix.add_mulVec]
    _ = kronVec (proj0.mulVec ket0) ((1 : Square 2).mulVec x) +
          kronVec (proj1.mulVec ket0) ((diag2 u₀ u₁).mulVec x) := by
            rw [kron_mulVec_two_two, kron_mulVec_two_two]
    _ = kronVec ket0 x := by simp

private lemma ccu_mulVec_left_zero (u₀ u₁ : ℂ) (φ : Vec 4) :
    (ccu (diag2 u₀ u₁)).mulVec (kronVec ket0 φ : Vec 8) = kronVec ket0 φ := by
  unfold ccu
  calc
    (proj0 ⊗ₖ (1 : Square 4) + proj1 ⊗ₖ controlledGate (diag2 u₀ u₁)).mulVec (kronVec ket0 φ)
        = (proj0 ⊗ₖ (1 : Square 4)).mulVec (kronVec ket0 φ) +
            (proj1 ⊗ₖ controlledGate (diag2 u₀ u₁)).mulVec (kronVec ket0 φ) := by
              rw [Matrix.add_mulVec]
    _ = kronVec (proj0.mulVec ket0) ((1 : Square 4).mulVec φ) +
          kronVec (proj1.mulVec ket0) ((controlledGate (diag2 u₀ u₁)).mulVec φ) := by
            rw [kron_mulVec_reindexed, kron_mulVec_reindexed]
    _ = kronVec ket0 φ := by simp

private lemma ccu_mulVec_ket1_ket0 (u₀ u₁ : ℂ) (v : Vec 2) :
    (ccu (diag2 u₀ u₁)).mulVec (kronVec ket1 (kronVec ket0 v) : Vec 8) =
      kronVec ket1 (kronVec ket0 v) := by
  unfold ccu
  calc
    (proj0 ⊗ₖ (1 : Square 4) + proj1 ⊗ₖ controlledGate (diag2 u₀ u₁)).mulVec
        (kronVec ket1 (kronVec ket0 v))
        = (proj0 ⊗ₖ (1 : Square 4)).mulVec (kronVec ket1 (kronVec ket0 v)) +
            (proj1 ⊗ₖ controlledGate (diag2 u₀ u₁)).mulVec (kronVec ket1 (kronVec ket0 v)) := by
              rw [Matrix.add_mulVec]
    _ = kronVec (proj0.mulVec ket1) ((1 : Square 4).mulVec (kronVec ket0 v)) +
          kronVec (proj1.mulVec ket1) ((controlledGate (diag2 u₀ u₁)).mulVec (kronVec ket0 v)) := by
            rw [kron_mulVec_reindexed, kron_mulVec_reindexed]
    _ = kronVec ket1 ((controlledGate (diag2 u₀ u₁)).mulVec (kronVec ket0 v)) := by simp
    _ = kronVec ket1 (kronVec ket0 v) := by rw [controlledGate_mulVec_left_zero]

private lemma ccu_mulVec_middle_ket0 (u₀ u₁ : ℂ) (φ : Vec 4) :
    (ccu (diag2 u₀ u₁)).mulVec (swapbc.mulVec (kronVec φ ket0 : Vec 8)) =
      swapbc.mulVec (kronVec φ ket0 : Vec 8) := by
  let u : Vec 2 := ![φ 0, φ 1]
  let v : Vec 2 := ![φ 2, φ 3]
  have hdecomp : φ = kronVec ket0 u + kronVec ket1 v := by
    dsimp [u, v]
    exact vec4_basis_decomp φ
  calc
    (ccu (diag2 u₀ u₁)).mulVec (swapbc.mulVec (kronVec φ ket0 : Vec 8))
        = (ccu (diag2 u₀ u₁)).mulVec
            (swapbc.mulVec (kronVec (kronVec ket0 u + kronVec ket1 v) ket0 : Vec 8)) := by
              rw [hdecomp]
    _ = (ccu (diag2 u₀ u₁)).mulVec
          (swapbc.mulVec (kronVec (kronVec ket0 u) ket0 : Vec 8) +
            swapbc.mulVec (kronVec (kronVec ket1 v) ket0 : Vec 8)) := by
          rw [kronVec_add_left, Matrix.mulVec_add]
    _ = (ccu (diag2 u₀ u₁)).mulVec
          (kronVec (kronVec ket0 ket0) u + kronVec (kronVec ket1 ket0) v) := by
          rw [swapbc_mulVec_kronVec, swapbc_mulVec_kronVec]
    _ = (ccu (diag2 u₀ u₁)).mulVec
          (kronVec ket0 (kronVec ket0 u) + kronVec ket1 (kronVec ket0 v)) := by
          rw [← kronVec_assoc_222, ← kronVec_assoc_222]
    _ = (ccu (diag2 u₀ u₁)).mulVec (kronVec ket0 (kronVec ket0 u)) +
          (ccu (diag2 u₀ u₁)).mulVec (kronVec ket1 (kronVec ket0 v)) := by
          rw [Matrix.mulVec_add]
    _ = kronVec ket0 (kronVec ket0 u) + kronVec ket1 (kronVec ket0 v) := by
          rw [ccu_mulVec_left_zero, ccu_mulVec_ket1_ket0]
    _ = kronVec (kronVec ket0 ket0) u + kronVec (kronVec ket1 ket0) v := by
          rw [kronVec_assoc_222, kronVec_assoc_222]
    _ = swapbc.mulVec (kronVec (kronVec ket0 u) ket0 : Vec 8) +
          swapbc.mulVec (kronVec (kronVec ket1 v) ket0 : Vec 8) := by
          rw [swapbc_mulVec_kronVec, swapbc_mulVec_kronVec]
    _ = swapbc.mulVec
          (((kronVec (kronVec ket0 u) ket0 : Vec 8) + kronVec (kronVec ket1 v) ket0)) := by
          rw [← Matrix.mulVec_add]
    _ = swapbc.mulVec (kronVec (kronVec ket0 u + kronVec ket1 v) ket0 : Vec 8) := by
          rw [← kronVec_add_left]
    _ = swapbc.mulVec (kronVec φ ket0 : Vec 8) := by rw [hdecomp]

private lemma section6_lemma_6_3_identity_transfer
    (u₀ u₁ : ℂ)
    (U₁ W₂ V₃ U₄ : Square 4) (P₂ : Square 2)
    (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (heq : acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄ = ccu (diag2 u₀ u₁))
    (hW₂eq : W₂ = (1 : Square 2) ⊗ₖ proj0 + P₂ ⊗ₖ proj1) :
    ∀ x : Vec 2,
      (acgate U₁).mulVec (kronVec (kronVec x ket0) ket0) =
        (bcgate U₄† * acgate V₃†).mulVec (kronVec (kronVec x ket0) ket0) := by
  intro x
  let t : Vec 8 := kronVec (kronVec x ket0) ket0
  have hAdj : bcgate U₄† * acgate V₃† * bcgate W₂† * acgate U₁† =
      ccu (diag2 (star u₀) (star u₁)) := by
    calc
      bcgate U₄† * acgate V₃† * bcgate W₂† * acgate U₁†
          = (acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄)† := by
              simp [Matrix.conjTranspose_mul, mul_assoc]
      _ = (ccu (diag2 u₀ u₁))† := by rw [heq]
      _ = ccu (diag2 (star u₀) (star u₁)) := by rw [ccu_diag2_conjTranspose_local]
  have hW₂dagFix : W₂†.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0 := by
    rw [hW₂eq, Matrix.conjTranspose_add, conjTranspose_kron_two, conjTranspose_kron_two]
    rw [Matrix.add_mulVec, kron_mulVec_two_two, kron_mulVec_two_two]
    simp
  have hbcW₂dagFix : (bcgate W₂†).mulVec t = t := by
    dsimp [t]
    calc
      (bcgate W₂†).mulVec (kronVec (kronVec x ket0) ket0)
          = (bcgate W₂†).mulVec (kronVec x (kronVec ket0 ket0)) := by rw [kronVec_assoc_222]
      _ = kronVec x (W₂†.mulVec (kronVec ket0 ket0)) := by rw [bcgate_mulVec_kronVec]
      _ = kronVec x (kronVec ket0 ket0) := by rw [hW₂dagFix]
      _ = kronVec (kronVec x ket0) ket0 := by rw [← kronVec_assoc_222]
  have hccuFix :
      (ccu (diag2 (star u₀) (star u₁))).mulVec ((acgate U₁).mulVec t) =
        (acgate U₁).mulVec t := by
    dsimp [t]
    rw [acgate_mulVec_kronVec]
    exact ccu_mulVec_middle_ket0 (star u₀) (star u₁) (U₁.mulVec (kronVec x ket0))
  have hApply := congrArg (fun M => M.mulVec ((acgate U₁).mulVec t)) hAdj
  have hUcancel : acgate U₁† * acgate U₁ = (1 : Square 8) := by
    have hU₁right : U₁† * U₁ = (1 : Square 4) := Matrix.mem_unitaryGroup_iff'.mp hU₁
    rw [← acgate_mul, hU₁right, acgate_one]
  have hLeft :
      (bcgate U₄† * acgate V₃† * bcgate W₂† * acgate U₁†).mulVec ((acgate U₁).mulVec t) =
        (bcgate U₄† * acgate V₃†).mulVec t := by
    calc
      (bcgate U₄† * acgate V₃† * bcgate W₂† * acgate U₁†).mulVec ((acgate U₁).mulVec t)
          = (bcgate U₄† * acgate V₃† * bcgate W₂† * (acgate U₁† * acgate U₁)).mulVec t := by
              simp [Matrix.mulVec_mulVec, mul_assoc]
      _ = (bcgate U₄† * acgate V₃† * bcgate W₂†).mulVec t := by
            rw [hUcancel]
            simp
      _ = ((bcgate U₄† * acgate V₃†) * bcgate W₂†).mulVec t := by
        simp [mul_assoc]
      _ = (bcgate U₄† * acgate V₃†).mulVec ((bcgate W₂†).mulVec t) := by
        rw [Matrix.mulVec_mulVec]
      _ = (bcgate U₄† * acgate V₃†).mulVec t := by rw [hbcW₂dagFix]
  have hBridge : (bcgate U₄† * acgate V₃†).mulVec t = (acgate U₁).mulVec t := by
    calc
      (bcgate U₄† * acgate V₃†).mulVec t
          = (bcgate U₄† * acgate V₃† * bcgate W₂† * acgate U₁†).mulVec ((acgate U₁).mulVec t) := by
              symm
              exact hLeft
      _ = (ccu (diag2 (star u₀) (star u₁))).mulVec ((acgate U₁).mulVec t) := by
            simpa using hApply
      _ = (acgate U₁).mulVec t := by exact hccuFix
  simpa [t] using hBridge.symm

set_option maxHeartbeats 400000 in
/-- **Lemma 6.3**.
Suppose `|u₀| = |u₁| = 1`. For 2-qubit unitaries `V₁, V₂, V₃, V₄`, if
  `V₁^{AC} V₂^{BC} V₃^{AC} V₄^{BC} = CC(Diag(u₀, u₁))`,
  `∃ ψ, ∀ x, ∃ z, V₂(x ⊗ |0⟩) = z ⊗ ψ`,
then either `u₀ = u₁` or `u₀ u₁ = 1` or there exist unitaries
`W₁, W₂, W₃, W₄, P₁, P₂, P₃, P₄, Q` such that
  `W₁^{AC} W₂^{BC} W₃^{AC} W₄^{BC} = CC(Diag(u₀, u₁))`,
  `W₁ = I ⊗ (Q · |0⟩⟨0|) + P₁ ⊗ (Q · |1⟩⟨1|)`,
  `W₂ = I ⊗ |0⟩⟨0| + P₂ ⊗ |1⟩⟨1|`,
  `W₃ = I ⊗ |0⟩⟨0| + P₃ ⊗ |1⟩⟨1|`,
  `W₄ = I ⊗ (|0⟩⟨0| · Q†) + P₄ ⊗ (|1⟩⟨1| · Q†)`. -/
lemma section6_lemma_6_3
    (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (V₁ V₂ V₃ V₄ : Square 4)
    (hV₁ : V₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₂ : V₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₃ : V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hV₄ : V₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (heq : acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ = ccu (diag2 u₀ u₁))
    (hV₂_struct : ∃ ψ : Vec 2, IsQubit ψ ∧
      ∀ x : Vec 2, IsQubit x →
        ∃ z : Vec 2, IsQubit z ∧ V₂.mulVec (kronVec x ket0) = kronVec z ψ) :
    u₀ = u₁ ∨ u₀ * u₁ = 1 ∨
    ∃ (W₁ W₂ W₃ W₄ : Square 4),
      W₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      W₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      W₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      W₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      ∃ (P₁ P₂ P₃ P₄ Q : Square 2),
        P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        P₂ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        P₃ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        P₄ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        Q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        acgate W₁ * bcgate W₂ * acgate W₃ * bcgate W₄ = ccu (diag2 u₀ u₁) ∧
        W₁ = (1 : Square 2) ⊗ₖ (Q * proj0) + P₁ ⊗ₖ (Q * proj1) ∧
        W₂ = (1 : Square 2) ⊗ₖ proj0 + P₂ ⊗ₖ proj1 ∧
        W₃ = (1 : Square 2) ⊗ₖ proj0 + P₃ ⊗ₖ proj1 ∧
        W₄ = (1 : Square 2) ⊗ₖ (proj0 * Q†) + P₄ ⊗ₖ (proj1 * Q†) := by
  rcases section6_lemma_6_3_normalize_V₂ V₁ V₂ V₃ V₄ hV₁ hV₂ hV₄ hV₂_struct with
    ⟨U₁, W₂, U₄, hU₁, hW₂, hU₄, P₂, hP₂, hNormEq, hW₂eq⟩
  have heqU : acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄ = ccu (diag2 u₀ u₁) := by
    calc
      acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄
          = acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ := by
              symm
              exact hNormEq
      _ = ccu (diag2 u₀ u₁) := heq
  have hidentU :=
    section6_lemma_6_3_identity_transfer u₀ u₁ U₁ W₂ V₃ U₄ P₂ hU₁ heqU hW₂eq
  rcases section6_lemma_6_2 u₀ u₁ hu₀ hu₁ U₁ W₂ V₃ U₄ hU₁ hW₂ hV₃ hU₄ heqU
      (by
        intro x _hx
        exact hidentU x) with hEq | hProd | ⟨X₁, X₃, X₄, hX₁, hX₃, hX₄, P₃, hP₃, heqX, hX₃eq⟩
  · exact Or.inl hEq
  · exact Or.inr (Or.inl hProd)
  ·
    have heqXccu : acgate X₁ * bcgate W₂ * acgate X₃ * bcgate X₄ = ccu (diag2 u₀ u₁) := by
      calc
        acgate X₁ * bcgate W₂ * acgate X₃ * bcgate X₄
            = acgate U₁ * bcgate W₂ * acgate V₃ * bcgate U₄ := by
                symm
                exact heqX
        _ = ccu (diag2 u₀ u₁) := heqU
    have hidentX :=
      section6_lemma_6_3_identity_transfer u₀ u₁ X₁ W₂ X₃ X₄ P₂ hX₁ heqXccu hW₂eq
    have hX₃dagEq : X₃† = (1 : Square 2) ⊗ₖ proj0 + P₃† ⊗ₖ proj1 := by
      have hAdj := congrArg Matrix.conjTranspose hX₃eq
      rw [Matrix.conjTranspose_add, conjTranspose_kron_two, conjTranspose_kron_two] at hAdj
      simpa using hAdj
    have hX₃dagFix : ∀ z : Vec 2, X₃†.mulVec (kronVec z ket0) = kronVec z ket0 := by
      intro z
      rw [hX₃dagEq]
      exact controlled_on_second_mulVec_ket0 P₃† z
    have hX₃dag00 : X₃†.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0 := hX₃dagFix ket0
    have hX₃dag10 : X₃†.mulVec (kronVec ket1 ket0) = kronVec ket1 ket0 := hX₃dagFix ket1
    let t0 : Vec 8 := kronVec (kronVec ket0 ket0) ket0
    have hAcX₃dag0 : (acgate X₃†).mulVec t0 = t0 := by
      simpa [t0] using acgate_mulVec_of_product X₃† ket0 ket0 ket0 ket0 ket0 hX₃dag00
    have hEq0 :
        (acgate X₁).mulVec t0 = kronVec ket0 (X₄†.mulVec (kronVec ket0 ket0)) := by
      calc
        (acgate X₁).mulVec t0
            = (bcgate X₄† * acgate X₃†).mulVec t0 := by
                simpa [t0] using hidentX ket0
        _ = (bcgate X₄†).mulVec ((acgate X₃†).mulVec t0) := by
              rw [Matrix.mulVec_mulVec]
        _ = (bcgate X₄†).mulVec t0 := by rw [hAcX₃dag0]
        _ = kronVec ket0 (X₄†.mulVec (kronVec ket0 ket0)) := by
            dsimp [t0]
            rw [kronVec_assoc_222, bcgate_mulVec_kronVec]
    have hX₄dag00Q : IsQubit (X₄†.mulVec (kronVec ket0 ket0)) := by
      exact isQubit_mulVec_of_unitary X₄† (conjTranspose_mem_unitaryGroup hX₄)
        (isQubit_kron isQubit_ket0 isQubit_ket0)
    rcases acgate_suffix_ket0 X₁ ket0 ket0 (X₄†.mulVec (kronVec ket0 ket0))
        isQubit_ket0 isQubit_ket0 hX₄dag00Q hEq0 with ⟨β, hβ, hX₄dag0⟩
    have hX10kron : kronVec (X₁.mulVec (kronVec ket0 ket0)) ket0 = kronVec (kronVec ket0 β) ket0 := by
      rw [acgate_mulVec_kronVec] at hEq0
      have hEq0' : swapbc.mulVec (kronVec (X₁.mulVec (kronVec ket0 ket0)) ket0) =
          kronVec ket0 (kronVec ket0 β) := by
        simpa [hX₄dag0] using hEq0
      calc
        kronVec (X₁.mulVec (kronVec ket0 ket0)) ket0
            = swapbc.mulVec (swapbc.mulVec (kronVec (X₁.mulVec (kronVec ket0 ket0)) ket0)) := by
                symm
                exact swapbc_mulVec_involutive _
        _ = swapbc.mulVec (kronVec ket0 (kronVec ket0 β)) := by rw [hEq0']
        _ = swapbc.mulVec (kronVec (kronVec ket0 ket0) β) := by rw [kronVec_assoc_222]
        _ = kronVec (kronVec ket0 β) ket0 := by rw [swapbc_mulVec_kronVec]
    have hX10 : X₁.mulVec (kronVec ket0 ket0) = kronVec ket0 β := by
      exact kronVec_right_cancel_ket0_vec4 hX10kron
    have hAdjX :
        bcgate X₄† * acgate X₃† * bcgate W₂† * acgate X₁† = ccu (diag2 (star u₀) (star u₁)) := by
      calc
        bcgate X₄† * acgate X₃† * bcgate W₂† * acgate X₁†
            = (acgate X₁ * bcgate W₂ * acgate X₃ * bcgate X₄)† := by
                simp [Matrix.conjTranspose_mul, mul_assoc]
        _ = (ccu (diag2 u₀ u₁))† := by rw [heqXccu]
        _ = ccu (diag2 (star u₀) (star u₁)) := by rw [ccu_diag2_conjTranspose_local]
    have hW₂dagFix : ∀ z : Vec 2, W₂†.mulVec (kronVec z ket0) = kronVec z ket0 := by
      intro z
      rw [hW₂eq, Matrix.conjTranspose_add, conjTranspose_kron_two, conjTranspose_kron_two]
      rw [Matrix.add_mulVec, kron_mulVec_two_two, kron_mulVec_two_two]
      simp
    have hAcX₃dagLine : ∀ z : Vec 2,
        (acgate X₃†).mulVec (kronVec ket0 (kronVec z ket0)) = kronVec ket0 (kronVec z ket0) := by
      intro z
      simpa [kronVec_assoc_222] using
        acgate_mulVec_of_product X₃† ket0 z ket0 ket0 ket0 hX₃dag00
    have hAcX₁Line : ∀ z : Vec 2,
        (acgate X₁).mulVec (kronVec ket0 (kronVec z ket0)) = kronVec ket0 (kronVec z β) := by
      intro z
      simpa [kronVec_assoc_222] using
        acgate_mulVec_of_product X₁ ket0 z ket0 ket0 β hX10
    have hEq12 : ∀ z : Vec 2,
        (acgate X₁).mulVec (kronVec ket0 (kronVec z ket0)) =
          (bcgate X₄†).mulVec (kronVec ket0 (kronVec z ket0)) := by
      intro z
      let t : Vec 8 := kronVec ket0 (kronVec z ket0)
      have hccuFix :
          (ccu (diag2 (star u₀) (star u₁))).mulVec ((acgate X₁).mulVec t) =
            (acgate X₁).mulVec t := by
        rw [hAcX₁Line z]
        exact ccu_mulVec_left_zero (star u₀) (star u₁) (kronVec z β)
      have hX₁cancel : acgate X₁† * acgate X₁ = (1 : Square 8) := by
        have hleft : X₁† * X₁ = (1 : Square 4) := Matrix.mem_unitaryGroup_iff'.mp hX₁
        rw [← acgate_mul, hleft, acgate_one]
      have hbcW₂dagFix : (bcgate W₂†).mulVec t = t := by
        dsimp [t]
        calc
          (bcgate W₂†).mulVec (kronVec ket0 (kronVec z ket0))
              = kronVec ket0 (W₂†.mulVec (kronVec z ket0)) := by rw [bcgate_mulVec_kronVec]
          _ = kronVec ket0 (kronVec z ket0) := by rw [hW₂dagFix z]
      have hLeft :
          (bcgate X₄† * acgate X₃† * bcgate W₂† * acgate X₁†).mulVec ((acgate X₁).mulVec t) =
            (bcgate X₄†).mulVec t := by
        have hMid : (bcgate X₄† * acgate X₃†).mulVec ((bcgate W₂†).mulVec t) = (bcgate X₄†).mulVec t := by
          rw [hbcW₂dagFix]
          calc
            (bcgate X₄† * acgate X₃†).mulVec t = (bcgate X₄†).mulVec ((acgate X₃†).mulVec t) := by
                rw [Matrix.mulVec_mulVec]
            _ = (bcgate X₄†).mulVec t := by rw [hAcX₃dagLine z]
        calc
          (bcgate X₄† * acgate X₃† * bcgate W₂† * acgate X₁†).mulVec ((acgate X₁).mulVec t)
              = (bcgate X₄† * acgate X₃† * bcgate W₂† * (acgate X₁† * acgate X₁)).mulVec t := by
                  simp [Matrix.mulVec_mulVec, mul_assoc]
          _ = (bcgate X₄† * acgate X₃† * bcgate W₂†).mulVec t := by
                rw [hX₁cancel]
                simp
          _ = (bcgate X₄† * acgate X₃†).mulVec ((bcgate W₂†).mulVec t) := by
                rw [Matrix.mulVec_mulVec]
          _ = (bcgate X₄†).mulVec t := by exact hMid
      have hApply := congrArg (fun M => M.mulVec ((acgate X₁).mulVec t)) hAdjX
      calc
        (acgate X₁).mulVec t = (ccu (diag2 (star u₀) (star u₁))).mulVec ((acgate X₁).mulVec t) := by
          symm
          exact hccuFix
        _ = (bcgate X₄† * acgate X₃† * bcgate W₂† * acgate X₁†).mulVec ((acgate X₁).mulVec t) := by
              symm
              exact hApply
        _ = (bcgate X₄†).mulVec t := hLeft
    have hX₄β : ∀ z : Vec 2, X₄†.mulVec (kronVec z ket0) = kronVec z β := by
      intro z
      have hkron : kronVec ket0 (X₄†.mulVec (kronVec z ket0)) = kronVec ket0 (kronVec z β) := by
        calc
          kronVec ket0 (X₄†.mulVec (kronVec z ket0))
              = (bcgate X₄†).mulVec (kronVec ket0 (kronVec z ket0)) := by rw [bcgate_mulVec_kronVec]
          _ = (acgate X₁).mulVec (kronVec ket0 (kronVec z ket0)) := by
                symm
                exact hEq12 z
          _ = kronVec ket0 (kronVec z β) := hAcX₁Line z
      exact kronVec_left_cancel_ket0_vec4 hkron
    let Q : Square 2 := colMatrix β (qubitPerp β)
    have hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
      dsimp [Q]
      exact qubit_basis_unitary β hβ
    let Y₄ : Square 4 := X₄ * ((1 : Square 2) ⊗ₖ Q)
    have hY₄ : Y₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
      dsimp [Y₄]
      exact Submonoid.mul_mem _ hX₄ (kron_unitary_two _ _ (Submonoid.one_mem _) hQ)
    have hY₄fix : ∀ z : Vec 2, Y₄.mulVec (kronVec z ket0) = kronVec z ket0 := by
      intro z
      have hright : X₄ * X₄† = (1 : Square 4) := Matrix.mem_unitaryGroup_iff.mp hX₄
      calc
        Y₄.mulVec (kronVec z ket0)
            = X₄.mulVec (((1 : Square 2) ⊗ₖ Q).mulVec (kronVec z ket0)) := by
                dsimp [Y₄]
                rw [Matrix.mulVec_mulVec]
        _ = X₄.mulVec (kronVec z (Q.mulVec ket0)) := by
              rw [kron_mulVec_two_two]
              simp
        _ = X₄.mulVec (kronVec z β) := by simp [Q]
        _ = X₄.mulVec (X₄†.mulVec (kronVec z ket0)) := by rw [hX₄β z]
        _ = (X₄ * X₄†).mulVec (kronVec z ket0) := by rw [← Matrix.mulVec_mulVec]
        _ = kronVec z ket0 := by rw [hright]; simp
    have hY₄fix0 : Y₄.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0 := hY₄fix ket0
    have hY₄fix1 : Y₄.mulVec (kronVec ket1 ket0) = kronVec ket1 ket0 := hY₄fix ket1
    rcases controlled_on_second_of_fixing_basis Y₄ hY₄ hY₄fix0 hY₄fix1 with ⟨P₄, hP₄, hY₄eq⟩
    have hQright : Q * Q† = (1 : Square 2) := Matrix.mem_unitaryGroup_iff.mp hQ
    have hKronQQ : ((1 : Square 2) ⊗ₖ Q) * ((1 : Square 2) ⊗ₖ Q†) = (1 : Square 4) := by
      calc
        ((1 : Square 2) ⊗ₖ Q) * ((1 : Square 2) ⊗ₖ Q†)
            = ((1 : Square 2) * (1 : Square 2)) ⊗ₖ (Q * Q†) := by rw [← kron_mul_two]
        _ = (1 : Square 2) ⊗ₖ (1 : Square 2) := by rw [hQright]; simp
        _ = (1 : Square 4) := by simpa using (TwoControl.one_kron_one 2 2)
    have hX₄rebuild : Y₄ * ((1 : Square 2) ⊗ₖ Q†) = X₄ := by
      dsimp [Y₄]
      calc
        (X₄ * ((1 : Square 2) ⊗ₖ Q)) * ((1 : Square 2) ⊗ₖ Q†)
            = X₄ * (((1 : Square 2) ⊗ₖ Q) * ((1 : Square 2) ⊗ₖ Q†)) := by simp [mul_assoc]
        _ = X₄ * (1 : Square 4) := by rw [hKronQQ]
        _ = X₄ := by simp
    have hX₄eq : X₄ = (1 : Square 2) ⊗ₖ (proj0 * Q†) + P₄ ⊗ₖ (proj1 * Q†) := by
      calc
        X₄ = Y₄ * ((1 : Square 2) ⊗ₖ Q†) := by symm; exact hX₄rebuild
        _ = (((1 : Square 2) ⊗ₖ proj0) + P₄ ⊗ₖ proj1) * ((1 : Square 2) ⊗ₖ Q†) := by rw [hY₄eq]
        _ = (1 : Square 2) ⊗ₖ (proj0 * Q†) + P₄ ⊗ₖ (proj1 * Q†) := by
            rw [add_mul, ← kron_mul_two, ← kron_mul_two]
            simp
    let Y₁ : Square 4 := ((1 : Square 2) ⊗ₖ Q†) * X₁
    have hY₁ : Y₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
      dsimp [Y₁]
      exact Submonoid.mul_mem _ (kron_unitary_two _ _ (Submonoid.one_mem _) (conjTranspose_mem_unitaryGroup hQ)) hX₁
    let t1 : Vec 8 := kronVec (kronVec ket1 ket0) ket0
    have hAcX₃dag1 : (acgate X₃†).mulVec t1 = t1 := by
      simpa [t1] using acgate_mulVec_of_product X₃† ket1 ket0 ket0 ket1 ket0 hX₃dag10
    have hAcX₁0β : (acgate X₁).mulVec t0 = kronVec ket0 (kronVec ket0 β) := by
      calc
        (acgate X₁).mulVec t0
            = (bcgate X₄† * acgate X₃†).mulVec t0 := by
                simpa [t0] using hidentX ket0
        _ = (bcgate X₄†).mulVec ((acgate X₃†).mulVec t0) := by rw [Matrix.mulVec_mulVec]
        _ = (bcgate X₄†).mulVec t0 := by rw [hAcX₃dag0]
        _ = kronVec ket0 (X₄†.mulVec (kronVec ket0 ket0)) := by
            dsimp [t0]
            rw [kronVec_assoc_222, bcgate_mulVec_kronVec]
        _ = kronVec ket0 (kronVec ket0 β) := by rw [hX₄β ket0]
    have hAcX₁1β : (acgate X₁).mulVec t1 = kronVec ket1 (kronVec ket0 β) := by
      calc
        (acgate X₁).mulVec t1
            = (bcgate X₄† * acgate X₃†).mulVec t1 := by
                simpa [t1] using hidentX ket1
        _ = (bcgate X₄†).mulVec ((acgate X₃†).mulVec t1) := by rw [Matrix.mulVec_mulVec]
        _ = (bcgate X₄†).mulVec t1 := by rw [hAcX₃dag1]
        _ = kronVec ket1 (X₄†.mulVec (kronVec ket0 ket0)) := by
            dsimp [t1]
            rw [kronVec_assoc_222, bcgate_mulVec_kronVec]
        _ = kronVec ket1 (kronVec ket0 β) := by rw [hX₄β ket0]
    have hAcY₁0 : (acgate Y₁).mulVec t0 = t0 := by
      dsimp [Y₁]
      calc
        (acgate (((1 : Square 2) ⊗ₖ Q†) * X₁)).mulVec t0
            = (acgate ((1 : Square 2) ⊗ₖ Q†) * acgate X₁).mulVec t0 := by
                rw [acgate_mul]
        _ = (bcgate ((1 : Square 2) ⊗ₖ Q†) * acgate X₁).mulVec t0 := by
              rw [acgate_localC_eq]
        _ = (bcgate ((1 : Square 2) ⊗ₖ Q†)).mulVec ((acgate X₁).mulVec t0) := by
              rw [Matrix.mulVec_mulVec]
        _ = (bcgate ((1 : Square 2) ⊗ₖ Q†)).mulVec (kronVec ket0 (kronVec ket0 β)) := by
              rw [hAcX₁0β]
        _ = kronVec ket0 (((1 : Square 2) ⊗ₖ Q†).mulVec (kronVec ket0 β)) := by
              rw [bcgate_mulVec_kronVec]
        _ = kronVec ket0 (kronVec ket0 (Q†.mulVec β)) := by
              rw [kron_mulVec_two_two]
              simp
        _ = kronVec ket0 (kronVec ket0 ket0) := by
              rw [colMatrix_conjTranspose_mulVec_left _ _ hQ]
        _ = t0 := by rw [← kronVec_assoc_222]
    have hAcY₁1 : (acgate Y₁).mulVec t1 = t1 := by
      dsimp [Y₁]
      calc
        (acgate (((1 : Square 2) ⊗ₖ Q†) * X₁)).mulVec t1
            = (acgate ((1 : Square 2) ⊗ₖ Q†) * acgate X₁).mulVec t1 := by
                rw [acgate_mul]
        _ = (bcgate ((1 : Square 2) ⊗ₖ Q†) * acgate X₁).mulVec t1 := by
              rw [acgate_localC_eq]
        _ = (bcgate ((1 : Square 2) ⊗ₖ Q†)).mulVec ((acgate X₁).mulVec t1) := by
              rw [Matrix.mulVec_mulVec]
        _ = (bcgate ((1 : Square 2) ⊗ₖ Q†)).mulVec (kronVec ket1 (kronVec ket0 β)) := by
              rw [hAcX₁1β]
        _ = kronVec ket1 (((1 : Square 2) ⊗ₖ Q†).mulVec (kronVec ket0 β)) := by
              rw [bcgate_mulVec_kronVec]
        _ = kronVec ket1 (kronVec ket0 (Q†.mulVec β)) := by
              rw [kron_mulVec_two_two]
              simp
        _ = kronVec ket1 (kronVec ket0 ket0) := by
              rw [colMatrix_conjTranspose_mulVec_left _ _ hQ]
        _ = t1 := by rw [← kronVec_assoc_222]
    have hY₁fix0 : Y₁.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0 := by
      exact acgate_fix_of_output_fix Y₁ ket0 (by simpa [t0] using hAcY₁0)
    have hY₁fix1 : Y₁.mulVec (kronVec ket1 ket0) = kronVec ket1 ket0 := by
      exact acgate_fix_of_output_fix Y₁ ket1 (by simpa [t1] using hAcY₁1)
    rcases controlled_on_second_of_fixing_basis Y₁ hY₁ hY₁fix0 hY₁fix1 with ⟨P₁, hP₁, hY₁eq⟩
    have hX₁rebuild : ((1 : Square 2) ⊗ₖ Q) * Y₁ = X₁ := by
      dsimp [Y₁]
      calc
        ((1 : Square 2) ⊗ₖ Q) * (((1 : Square 2) ⊗ₖ Q†) * X₁)
            = (((1 : Square 2) ⊗ₖ Q) * ((1 : Square 2) ⊗ₖ Q†)) * X₁ := by simp [mul_assoc]
        _ = (1 : Square 4) * X₁ := by rw [hKronQQ]
        _ = X₁ := by simp
    have hX₁eq : X₁ = (1 : Square 2) ⊗ₖ (Q * proj0) + P₁ ⊗ₖ (Q * proj1) := by
      calc
        X₁ = ((1 : Square 2) ⊗ₖ Q) * Y₁ := by symm; exact hX₁rebuild
        _ = ((1 : Square 2) ⊗ₖ Q) * (((1 : Square 2) ⊗ₖ proj0) + P₁ ⊗ₖ proj1) := by rw [hY₁eq]
        _ = (1 : Square 2) ⊗ₖ (Q * proj0) + P₁ ⊗ₖ (Q * proj1) := by
          rw [mul_add, ← kron_mul_two, ← kron_mul_two]
          simp
    exact Or.inr (Or.inr ⟨X₁, W₂, X₃, X₄, hX₁, hW₂, hX₃, hX₄, P₁, P₂, P₃, P₄, Q,
      hP₁, hP₂, hP₃, hP₄, hQ, heqXccu, hX₁eq, hW₂eq, hX₃eq, hX₄eq⟩)

    private lemma exists_product_state_on_left_ket0 (U : Square 4)
      (_hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
      ∃ w : Vec 2, IsQubit w ∧ IsProductState (U.mulVec (kronVec ket0 w)) := by
    let u : Vec 4 := U.mulVec (kronVec ket0 ket0)
    let v : Vec 4 := U.mulVec (kronVec ket0 ket1)
    by_cases hvProd : IsProductState v
    · exact ⟨ket1, isQubit_ket1, by simpa [v] using hvProd⟩
    · have hvDet : detVec4 v ≠ 0 := by
        intro hdet
        exact hvProd ((isProductState_iff_detVec4_eq_zero v).2 hdet)
      let B : ℂ := u 0 * v 3 + v 0 * u 3 - u 1 * v 2 - v 1 * u 2
      rcases quadratic_root_eq_zero (detVec4 u) B (detVec4 v) hvDet with ⟨t, ht⟩
      let w0 : Vec 2 := ket0 + t • ket1
      have hw0_ne : w0 ≠ 0 := by
        intro hw0
        have h0 := congrFun hw0 0
        simp [w0, ket0, ket1] at h0
      rcases normalize_vec2 w0 hw0_ne with ⟨w, hw, μ, hμ_ne, hw0eq⟩
      have hImageEq : U.mulVec (kronVec ket0 w0) = u + t • v := by
        dsimp [u, v, w0]
        calc
          U.mulVec (kronVec ket0 (ket0 + t • ket1))
              = U.mulVec (kronVec ket0 ket0 + kronVec ket0 (t • ket1)) := by
                  rw [kronVec_add_right]
          _ = U.mulVec (kronVec ket0 ket0 + t • kronVec ket0 ket1) := by
                rw [kronVec_smul_right]
          _ = U.mulVec (kronVec ket0 ket0) + t • U.mulVec (kronVec ket0 ket1) := by
                rw [Matrix.mulVec_add, Matrix.mulVec_smul]
          _ = u + t • v := by rfl
      have hdet0 : detVec4 (U.mulVec (kronVec ket0 w0)) = 0 := by
        rw [hImageEq, detVec4_add_smul]
        have ht' : detVec4 u + t * B + t ^ 2 * detVec4 v = 0 := by
          calc
            detVec4 u + t * B + t ^ 2 * detVec4 v
                = detVec4 u + B * t + detVec4 v * t ^ 2 := by ring
            _ = 0 := ht
        simpa [B] using ht'
      have hScaled : U.mulVec (kronVec ket0 w0) = μ • U.mulVec (kronVec ket0 w) := by
        calc
          U.mulVec (kronVec ket0 w0) = U.mulVec (kronVec ket0 (μ • w)) := by rw [hw0eq]
          _ = U.mulVec (μ • kronVec ket0 w) := by rw [kronVec_smul_right]
          _ = μ • U.mulVec (kronVec ket0 w) := by rw [Matrix.mulVec_smul]
      have hdetw : detVec4 (U.mulVec (kronVec ket0 w)) = 0 := by
        have hscaled0 : detVec4 (μ • U.mulVec (kronVec ket0 w)) = 0 := by
          simpa [hScaled] using hdet0
        rw [detVec4_smul] at hscaled0
        exact (mul_eq_zero.mp hscaled0).resolve_left (pow_ne_zero 2 hμ_ne)
      exact ⟨w, hw, (isProductState_iff_detVec4_eq_zero _).2 hdetw⟩

  private lemma section6_lemma_6_4_normalize_V₃
      (U₁ U₂ U₃ U₄ : Square 4)
      (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
      (hU₂ : U₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
      (hU₃ : U₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
      (hU₄ : U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
      ∃ (V₁ V₂ V₃ V₄ : Square 4),
        V₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
        V₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
        V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
        V₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
        acgate U₁ * bcgate U₂ * acgate U₃ * bcgate U₄ =
          acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ ∧
        V₃.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0 := by
    rcases exists_product_state_on_left_ket0 U₃ hU₃ with ⟨w, hw, hProd⟩
    let ξ : Vec 4 := U₃.mulVec (kronVec ket0 w)
    have hξQ : IsQubit ξ := by
      dsimp [ξ]
      exact isQubit_mulVec_of_unitary U₃ hU₃ (isQubit_kron isQubit_ket0 hw)
    rcases qubit_product_state_factors hξQ hProd with ⟨ψ, φ, hψ, hφ, hξeq⟩
    let W0 : Square 2 := colMatrix ψ (qubitPerp ψ)
    let W1 : Square 2 := colMatrix φ (qubitPerp φ)
    let W2 : Square 2 := colMatrix w (qubitPerp w)
    have hW0 : W0 ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
      dsimp [W0]
      exact qubit_basis_unitary ψ hψ
    have hW1 : W1 ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
      dsimp [W1]
      exact qubit_basis_unitary φ hφ
    have hW2 : W2 ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
      dsimp [W2]
      exact qubit_basis_unitary w hw
    let V₁ : Square 4 := U₁ * (W0 ⊗ₖ (1 : Square 2))
    let V₂ : Square 4 := U₂ * ((1 : Square 2) ⊗ₖ W1)
    let V₃ : Square 4 := ((W0 ⊗ₖ W1)†) * U₃ * ((1 : Square 2) ⊗ₖ W2)
    let V₄ : Square 4 := (((1 : Square 2) ⊗ₖ W2)†) * U₄
    have hV₁ : V₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
      dsimp [V₁]
      exact Submonoid.mul_mem _ hU₁ (kron_unitary_two _ _ hW0 (Submonoid.one_mem _))
    have hV₂ : V₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
      dsimp [V₂]
      exact Submonoid.mul_mem _ hU₂ (kron_unitary_two _ _ (Submonoid.one_mem _) hW1)
    have hW01 : W0 ⊗ₖ W1 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
      exact kron_unitary_two _ _ hW0 hW1
    have hV₃ : V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
      dsimp [V₃]
      exact Submonoid.mul_mem _
        (Submonoid.mul_mem _ (conjTranspose_mem_unitaryGroup hW01) hU₃)
        (kron_unitary_two _ _ (Submonoid.one_mem _) hW2)
    have hV₄ : V₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
      dsimp [V₄]
      exact Submonoid.mul_mem _
        (conjTranspose_mem_unitaryGroup (kron_unitary_two _ _ (Submonoid.one_mem _) hW2))
        hU₄
    have hV₃_fix : V₃.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0 := by
      dsimp [V₃, ξ]
      calc
        (((W0 ⊗ₖ W1)† * U₃ * ((1 : Square 2) ⊗ₖ W2)).mulVec (kronVec ket0 ket0))
            = (((W0 ⊗ₖ W1)† * U₃)).mulVec (((1 : Square 2) ⊗ₖ W2).mulVec (kronVec ket0 ket0)) := by
                rw [Matrix.mulVec_mulVec, mul_assoc]
        _ = (((W0 ⊗ₖ W1)† * U₃)).mulVec (kronVec ket0 (W2.mulVec ket0)) := by
              rw [kron_mulVec_two_two]
              simp
        _ = (((W0 ⊗ₖ W1)† * U₃)).mulVec (kronVec ket0 w) := by
              simp [W2]
        _ = (W0 ⊗ₖ W1)†.mulVec (U₃.mulVec (kronVec ket0 w)) := by
              rw [Matrix.mulVec_mulVec]
        _ = (W0 ⊗ₖ W1)†.mulVec ξ := by rfl
        _ = (W0 ⊗ₖ W1)†.mulVec (kronVec ψ φ) := by rw [hξeq]
        _ = kronVec (W0†.mulVec ψ) (W1†.mulVec φ) := by
              rw [conjTranspose_kron_two, kron_mulVec_two_two]
        _ = kronVec ket0 (W1†.mulVec φ) := by
              rw [colMatrix_conjTranspose_mulVec_left _ _ hW0]
        _ = kronVec ket0 ket0 := by
              rw [colMatrix_conjTranspose_mulVec_left _ _ hW1]
    have hInsertLeft :
        acgate (W0 ⊗ₖ (1 : Square 2)) * acgate ((1 : Square 2) ⊗ₖ W1) *
          acgate ((W0 ⊗ₖ W1)†) = (1 : Square 8) := by
      calc
        acgate (W0 ⊗ₖ (1 : Square 2)) * acgate ((1 : Square 2) ⊗ₖ W1) *
            acgate ((W0 ⊗ₖ W1)†)
            = acgate ((W0 ⊗ₖ (1 : Square 2)) * ((1 : Square 2) ⊗ₖ W1)) *
                acgate ((W0 ⊗ₖ W1)†) := by
                  rw [← acgate_mul]
        _ = acgate (W0 ⊗ₖ W1) * acgate ((W0 ⊗ₖ W1)†) := by
              rw [← kron_mul_two]
              simp
        _ = acgate ((W0 ⊗ₖ W1) * (W0 ⊗ₖ W1)†) := by
              rw [← acgate_mul]
        _ = acgate (1 : Square 4) := by
              have hright : (W0 ⊗ₖ W1) * (W0 ⊗ₖ W1)† = (1 : Square 4) :=
                Matrix.mem_unitaryGroup_iff.mp hW01
              rw [hright]
        _ = (1 : Square 8) := by rw [acgate_one]
    have hInsertRight :
        bcgate ((1 : Square 2) ⊗ₖ W2) * bcgate (((1 : Square 2) ⊗ₖ W2)†) = (1 : Square 8) := by
      calc
        bcgate ((1 : Square 2) ⊗ₖ W2) * bcgate (((1 : Square 2) ⊗ₖ W2)†)
            = bcgate (((1 : Square 2) ⊗ₖ W2) * (((1 : Square 2) ⊗ₖ W2)†)) := by
                rw [← bcgate_mul]
        _ = bcgate (1 : Square 4) := by
              have hright : ((1 : Square 2) ⊗ₖ W2) * (((1 : Square 2) ⊗ₖ W2)†) = (1 : Square 4) := by
                exact Matrix.mem_unitaryGroup_iff.mp (kron_unitary_two _ _ (Submonoid.one_mem _) hW2)
              rw [hright]
        _ = (1 : Square 8) := by rw [bcgate_one]
    refine ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, ?_, hV₃_fix⟩
    calc
      acgate U₁ * bcgate U₂ * acgate U₃ * bcgate U₄
          = acgate U₁ * bcgate U₂ * (acgate (W0 ⊗ₖ (1 : Square 2)) *
              acgate ((1 : Square 2) ⊗ₖ W1) * acgate ((W0 ⊗ₖ W1)†)) *
              acgate U₃ * (bcgate ((1 : Square 2) ⊗ₖ W2) * bcgate (((1 : Square 2) ⊗ₖ W2)†)) *
              bcgate U₄ := by
                rw [hInsertLeft, hInsertRight]
                simp [mul_assoc]
      _ = acgate U₁ * acgate (W0 ⊗ₖ (1 : Square 2)) * bcgate U₂ * acgate ((1 : Square 2) ⊗ₖ W1) *
            acgate ((W0 ⊗ₖ W1)†) * acgate U₃ * bcgate ((1 : Square 2) ⊗ₖ W2) *
            bcgate (((1 : Square 2) ⊗ₖ W2)†) * bcgate U₄ := by
              calc
                acgate U₁ * bcgate U₂ * (acgate (W0 ⊗ₖ (1 : Square 2)) *
                    acgate ((1 : Square 2) ⊗ₖ W1) * acgate ((W0 ⊗ₖ W1)†)) *
                    acgate U₃ * (bcgate ((1 : Square 2) ⊗ₖ W2) * bcgate (((1 : Square 2) ⊗ₖ W2)†)) *
                    bcgate U₄
                    = acgate U₁ * (bcgate U₂ * acgate (W0 ⊗ₖ (1 : Square 2))) * acgate ((1 : Square 2) ⊗ₖ W1) *
                        acgate ((W0 ⊗ₖ W1)†) * acgate U₃ * (bcgate ((1 : Square 2) ⊗ₖ W2) *
                        bcgate (((1 : Square 2) ⊗ₖ W2)†)) * bcgate U₄ := by
                          simp [mul_assoc]
                _ = acgate U₁ * (acgate (W0 ⊗ₖ (1 : Square 2)) * bcgate U₂) * acgate ((1 : Square 2) ⊗ₖ W1) *
                        acgate ((W0 ⊗ₖ W1)†) * acgate U₃ * (bcgate ((1 : Square 2) ⊗ₖ W2) *
                        bcgate (((1 : Square 2) ⊗ₖ W2)†)) * bcgate U₄ := by
                          rw [acgate_localA_commute_bcgate]
                _ = acgate U₁ * acgate (W0 ⊗ₖ (1 : Square 2)) * bcgate U₂ * acgate ((1 : Square 2) ⊗ₖ W1) *
                        acgate ((W0 ⊗ₖ W1)†) * acgate U₃ * bcgate ((1 : Square 2) ⊗ₖ W2) *
                        bcgate (((1 : Square 2) ⊗ₖ W2)†) * bcgate U₄ := by
                          rw [acgate_localC_eq]
                          simp [mul_assoc]
      _ = acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ := by
        simp [V₁, V₂, V₃, V₄, acgate_mul, bcgate_mul, acgate_localC_eq W2,
              (acgate_localC_eq W1).symm, mul_assoc]

  private lemma section6_lemma_6_4_identity_transfer
      (u₀ u₁ : ℂ)
      (V₁ V₂ V₃ V₄ : Square 4)
      (hV₄ : V₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
      (heq : acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ = ccu (diag2 u₀ u₁))
      (hV₃_fix : V₃.mulVec (kronVec ket0 ket0) = kronVec ket0 ket0) :
      ∀ x : Vec 2, IsQubit x →
        (acgate V₁ * bcgate V₂).mulVec (kronVec ket0 (kronVec x ket0)) =
          (bcgate V₄†).mulVec (kronVec ket0 (kronVec x ket0)) := by
    intro x hx
    let t : Vec 8 := kronVec ket0 (kronVec x ket0)
    have hV₃fix8 : (acgate V₃).mulVec t = t := by
      dsimp [t]
      simpa [kronVec_assoc_222] using
        (acgate_mulVec_of_product V₃ ket0 x ket0 ket0 ket0 hV₃_fix)
    have hV₄cancel : bcgate V₄ * bcgate V₄† = (1 : Square 8) := by
      have hright : V₄ * V₄† = (1 : Square 4) := Matrix.mem_unitaryGroup_iff.mp hV₄
      rw [← bcgate_mul, hright, bcgate_one]
    calc
      (acgate V₁ * bcgate V₂).mulVec t
          = (acgate V₁ * bcgate V₂).mulVec ((acgate V₃).mulVec t) := by rw [hV₃fix8]
      _ = (acgate V₁ * bcgate V₂ * acgate V₃).mulVec t := by
            rw [← Matrix.mulVec_mulVec]
            simp [mul_assoc]
      _ = ((acgate V₁ * bcgate V₂ * acgate V₃) * (1 : Square 8)).mulVec t := by
            simp
      _ = ((acgate V₁ * bcgate V₂ * acgate V₃) * (bcgate V₄ * bcgate V₄†)).mulVec t := by
            rw [hV₄cancel]
      _ = (acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ * bcgate V₄†).mulVec t := by
            simp [mul_assoc]
      _ = (ccu (diag2 u₀ u₁) * bcgate V₄†).mulVec t := by rw [heq]
      _ = (ccu (diag2 u₀ u₁)).mulVec ((bcgate V₄†).mulVec t) := by
            rw [Matrix.mulVec_mulVec]
      _ = (ccu (diag2 u₀ u₁)).mulVec (kronVec ket0 (V₄†.mulVec (kronVec x ket0))) := by
            dsimp [t]
            rw [bcgate_mulVec_kronVec]
      _ = kronVec ket0 (V₄†.mulVec (kronVec x ket0)) := by
            exact ccu_mulVec_left_zero u₀ u₁ (V₄†.mulVec (kronVec x ket0))
      _ = (bcgate V₄†).mulVec (kronVec ket0 (kronVec x ket0)) := by
            dsimp [t]
            rw [bcgate_mulVec_kronVec]

  private lemma section6_lemma_6_4_caseA
      (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
      (V₁ V₂ V₃ V₄ : Square 4)
      (hV₁ : V₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
      (hV₂ : V₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
      (hV₃ : V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
      (hV₄ : V₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
      (heq : acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ = ccu (diag2 u₀ u₁))
      (hident : ∀ x : Vec 2, IsQubit x →
        (acgate V₁ * bcgate V₂).mulVec (kronVec ket0 (kronVec x ket0)) =
          (bcgate V₄†).mulVec (kronVec ket0 (kronVec x ket0)))
      (hbranch : ∃ x : Vec 2, IsQubit x ∧ IsEntangled (V₂.mulVec (kronVec x ket0))) :
      u₀ = u₁ ∨ u₀ * u₁ = 1 := by
    rcases hbranch with ⟨x, hx, hEnt⟩
    let φ : Vec 4 := V₂.mulVec (kronVec x ket0)
    let w : Vec 4 := V₄†.mulVec (kronVec x ket0)
    have hφQ : IsQubit φ := by
      dsimp [φ]
      exact isQubit_mulVec_of_unitary V₂ hV₂ (isQubit_kron hx isQubit_ket0)
    have hEq0 : (acgate V₁).mulVec (kronVec ket0 φ : Vec 8) = kronVec ket0 w := by
      calc
        (acgate V₁).mulVec (kronVec ket0 φ : Vec 8)
            = (acgate V₁).mulVec (kronVec ket0 (V₂.mulVec (kronVec x ket0))) := by rfl
        _ = (acgate V₁).mulVec ((bcgate V₂).mulVec (kronVec ket0 (kronVec x ket0))) := by
              dsimp [φ]
              rw [bcgate_mulVec_kronVec]
        _ = (acgate V₁ * bcgate V₂).mulVec (kronVec ket0 (kronVec x ket0)) := by
              rw [Matrix.mulVec_mulVec]
        _ = (bcgate V₄†).mulVec (kronVec ket0 (kronVec x ket0)) := hident x hx
        _ = kronVec ket0 w := by
              dsimp [w]
              rw [bcgate_mulVec_kronVec]
    rcases controlled_on_first_of_entangled_input V₁ hV₁ hφQ hEnt hEq0 with
      ⟨P₀, P₁, hP₀, hP₁, hV₁eq⟩
    exact (section4_lemma_4_3 u₀ u₁ hu₀ hu₁).1 <| by
      refine ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, P₀, P₁, hP₀, hP₁, hV₁eq, heq⟩

  private lemma section6_lemma_6_4_caseC
      (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1)
      (V₁ V₂ V₃ V₄ : Square 4)
      (hV₁ : V₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
      (hV₂ : V₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
      (hV₃ : V₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
      (hV₄ : V₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ)
      (heq : acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ = ccu (diag2 u₀ u₁))
      (hident : ∀ x : Vec 2, IsQubit x →
        (acgate V₁ * bcgate V₂).mulVec (kronVec ket0 (kronVec x ket0)) =
          (bcgate V₄†).mulVec (kronVec ket0 (kronVec x ket0)))
      (hbranch : ∃ ψ : Vec 2, IsQubit ψ ∧
        ∀ x : Vec 2, IsQubit x →
          ∃ z : Vec 2, IsQubit z ∧ V₂.mulVec (kronVec x ket0) = kronVec ψ z) :
      u₀ = u₁ ∨ u₀ * u₁ = 1 := by
    rcases hbranch with ⟨ψ, hψ, hbranchψ⟩
    rcases exists_unitary_of_fixed_left_factor V₂ hV₂ hψ hbranchψ with ⟨Q, hQ, hQprop⟩
    have hβ0 : IsQubit (Q.mulVec ket0) := by
      exact isQubit_mulVec_of_unitary Q hQ isQubit_ket0
    have hβ1 : IsQubit (Q.mulVec ket1) := by
      exact isQubit_mulVec_of_unitary Q hQ isQubit_ket1
    have hβorth : star (Q.mulVec ket0) ⬝ᵥ Q.mulVec ket1 = 0 := by
      have hpres := dot_mulVec_of_unitary Q hQ ket0 ket1
      simpa [dotProduct, ket0, ket1, Fin.sum_univ_two] using hpres
    have hφ0Q : IsQubit (V₄†.mulVec (kronVec ket0 ket0)) := by
      exact isQubit_mulVec_of_unitary V₄† (conjTranspose_mem_unitaryGroup hV₄)
        (isQubit_kron isQubit_ket0 isQubit_ket0)
    have hφ1Q : IsQubit (V₄†.mulVec (kronVec ket1 ket0)) := by
      exact isQubit_mulVec_of_unitary V₄† (conjTranspose_mem_unitaryGroup hV₄)
        (isQubit_kron isQubit_ket1 isQubit_ket0)
    have hEq0 :
        (acgate V₁).mulVec (kronVec ket0 (kronVec ψ (Q.mulVec ket0))) =
          kronVec ket0 (V₄†.mulVec (kronVec ket0 ket0)) := by
      calc
        (acgate V₁).mulVec (kronVec ket0 (kronVec ψ (Q.mulVec ket0)))
            = (acgate V₁).mulVec (kronVec ket0 (V₂.mulVec (kronVec ket0 ket0))) := by
                rw [← hQprop ket0 isQubit_ket0]
        _ = (acgate V₁).mulVec ((bcgate V₂).mulVec (kronVec ket0 (kronVec ket0 ket0))) := by
              rw [bcgate_mulVec_kronVec]
        _ = (acgate V₁ * bcgate V₂).mulVec (kronVec ket0 (kronVec ket0 ket0)) := by
              rw [Matrix.mulVec_mulVec]
        _ = (bcgate V₄†).mulVec (kronVec ket0 (kronVec ket0 ket0)) := hident ket0 isQubit_ket0
        _ = kronVec ket0 (V₄†.mulVec (kronVec ket0 ket0)) := by
              rw [bcgate_mulVec_kronVec]
    have hEq1 :
        (acgate V₁).mulVec (kronVec ket0 (kronVec ψ (Q.mulVec ket1))) =
          kronVec ket0 (V₄†.mulVec (kronVec ket1 ket0)) := by
      calc
        (acgate V₁).mulVec (kronVec ket0 (kronVec ψ (Q.mulVec ket1)))
            = (acgate V₁).mulVec (kronVec ket0 (V₂.mulVec (kronVec ket1 ket0))) := by
                rw [← hQprop ket1 isQubit_ket1]
        _ = (acgate V₁).mulVec ((bcgate V₂).mulVec (kronVec ket0 (kronVec ket1 ket0))) := by
              rw [bcgate_mulVec_kronVec]
        _ = (acgate V₁ * bcgate V₂).mulVec (kronVec ket0 (kronVec ket1 ket0)) := by
              rw [Matrix.mulVec_mulVec]
        _ = (bcgate V₄†).mulVec (kronVec ket0 (kronVec ket1 ket0)) := hident ket1 isQubit_ket1
        _ = kronVec ket0 (V₄†.mulVec (kronVec ket1 ket0)) := by
              rw [bcgate_mulVec_kronVec]
    rcases acgate_prefix_ket0 V₁ ψ (Q.mulVec ket0) (V₄†.mulVec (kronVec ket0 ket0))
        hψ hβ0 hφ0Q hEq0 with ⟨w0, hw0, hw0eq⟩
    rcases acgate_prefix_ket0 V₁ ψ (Q.mulVec ket1) (V₄†.mulVec (kronVec ket1 ket0))
        hψ hβ1 hφ1Q hEq1 with ⟨w1, hw1, hw1eq⟩
    have hFix0 : V₁.mulVec (kronVec ket0 (Q.mulVec ket0)) = kronVec ket0 w0 := by
      exact acgate_fixed_middle_eq V₁ ψ (Q.mulVec ket0) w0 hψ (by simpa [hw0eq] using hEq0)
    have hFix1 : V₁.mulVec (kronVec ket0 (Q.mulVec ket1)) = kronVec ket0 w1 := by
      exact acgate_fixed_middle_eq V₁ ψ (Q.mulVec ket1) w1 hψ (by simpa [hw1eq] using hEq1)
    rcases controlled_on_first_of_two_images V₁ hV₁ hβ0 hβ1 hβorth hw0 hw1 hFix0 hFix1 with
      ⟨P₀, P₁, hP₀, hP₁, hV₁eq⟩
    exact (section4_lemma_4_3 u₀ u₁ hu₀ hu₁).1 <| by
      refine ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, P₀, P₁, hP₀, hP₁, hV₁eq, heq⟩

  private lemma conj_proj0_eq_ketbra (Q : Square 2) :
      Q * proj0 * Q† = ketbra (Q.mulVec ket0) (Q.mulVec ket0) := by
    calc
      Q * proj0 * Q† = Q * Matrix.vecMulVec ket0 (star ket0) * Q† := by rfl
      _ = Matrix.vecMulVec (Q.mulVec ket0) (star ket0) * Q† := by rw [Matrix.mul_vecMulVec]
      _ = Matrix.vecMulVec (Q.mulVec ket0) ((star ket0) ᵥ* Q†) := by rw [Matrix.vecMulVec_mul]
      _ = Matrix.vecMulVec (Q.mulVec ket0) (star (Q.mulVec ket0)) := by rw [Matrix.star_mulVec]
      _ = ketbra (Q.mulVec ket0) (Q.mulVec ket0) := by rfl

  private lemma conj_proj1_eq_ketbra (Q : Square 2) :
      Q * proj1 * Q† = ketbra (Q.mulVec ket1) (Q.mulVec ket1) := by
    calc
      Q * proj1 * Q† = Q * Matrix.vecMulVec ket1 (star ket1) * Q† := by rfl
      _ = Matrix.vecMulVec (Q.mulVec ket1) (star ket1) * Q† := by rw [Matrix.mul_vecMulVec]
      _ = Matrix.vecMulVec (Q.mulVec ket1) ((star ket1) ᵥ* Q†) := by rw [Matrix.vecMulVec_mul]
      _ = Matrix.vecMulVec (Q.mulVec ket1) (star (Q.mulVec ket1)) := by rw [Matrix.star_mulVec]
      _ = ketbra (Q.mulVec ket1) (Q.mulVec ket1) := by rfl

  private lemma kron_mul_three (A₁ A₂ B₁ B₂ C₁ C₂ : Square 2) :
      ((A₁ ⊗ₖ B₁) ⊗ₖ C₁) * ((A₂ ⊗ₖ B₂) ⊗ₖ C₂) =
        ((A₁ * A₂) ⊗ₖ (B₁ * B₂)) ⊗ₖ (C₁ * C₂) := by
    calc
      ((A₁ ⊗ₖ B₁) ⊗ₖ C₁) * ((A₂ ⊗ₖ B₂) ⊗ₖ C₂)
          = (((A₁ ⊗ₖ B₁) * (A₂ ⊗ₖ B₂)) ⊗ₖ (C₁ * C₂)) := by
              rw [← kron_mul_reindex (A₁ ⊗ₖ B₁) (A₂ ⊗ₖ B₂) C₁ C₂]
      _ = ((A₁ * A₂) ⊗ₖ (B₁ * B₂)) ⊗ₖ (C₁ * C₂) := by
            rw [kron_mul_two]

  @[simp] private lemma proj0_mul_proj0_right (B : Square 2) :
      proj0 * (proj0 * B) = proj0 * B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [proj0, ketbra, ket0, Matrix.mul_apply, Fin.sum_univ_two]

  @[simp] private lemma proj1_mul_proj1_right (B : Square 2) :
      proj1 * (proj1 * B) = proj1 * B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [proj1, ketbra, ket1, Matrix.mul_apply, Fin.sum_univ_two]

  @[simp] private lemma proj0_mul_proj1_right (B : Square 2) :
      proj0 * (proj1 * B) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [proj0, proj1, ketbra, ket0, ket1, Matrix.mul_apply, Fin.sum_univ_two]

  @[simp] private lemma proj1_mul_proj0_right (B : Square 2) :
      proj1 * (proj0 * B) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [proj0, proj1, ketbra, ket0, ket1, Matrix.mul_apply, Fin.sum_univ_two]

  @[simp] private lemma mul_proj0_mul_proj0_right (A B : Square 2) :
      A * proj0 * (proj0 * B) = A * proj0 * B := by
    calc
      A * proj0 * (proj0 * B) = A * (proj0 * (proj0 * B)) := by rw [mul_assoc]
      _ = A * (proj0 * B) := by rw [proj0_mul_proj0_right]
      _ = A * proj0 * B := by rw [← mul_assoc]

  @[simp] private lemma mul_proj1_mul_proj1_right (A B : Square 2) :
      A * proj1 * (proj1 * B) = A * proj1 * B := by
    calc
      A * proj1 * (proj1 * B) = A * (proj1 * (proj1 * B)) := by rw [mul_assoc]
      _ = A * (proj1 * B) := by rw [proj1_mul_proj1_right]
      _ = A * proj1 * B := by rw [← mul_assoc]

  @[simp] private lemma mul_proj0_mul_proj1_right (A B : Square 2) :
      A * proj0 * (proj1 * B) = 0 := by
    calc
      A * proj0 * (proj1 * B) = A * (proj0 * (proj1 * B)) := by rw [mul_assoc]
      _ = A * 0 := by rw [proj0_mul_proj1_right]
      _ = 0 := by simp

  @[simp] private lemma mul_proj1_mul_proj0_right (A B : Square 2) :
      A * proj1 * (proj0 * B) = 0 := by
    calc
      A * proj1 * (proj0 * B) = A * (proj1 * (proj0 * B)) := by rw [mul_assoc]
      _ = A * 0 := by rw [proj1_mul_proj0_right]
      _ = 0 := by simp

  set_option maxHeartbeats 400000 in
  private lemma section6_lemma_6_4_special_word (P₁ P₂ P₃ P₄ Q : Square 2) :
      acgate ((1 : Square 2) ⊗ₖ (Q * proj0) + P₁ ⊗ₖ (Q * proj1)) *
        bcgate ((1 : Square 2) ⊗ₖ proj0 + P₂ ⊗ₖ proj1) *
        acgate ((1 : Square 2) ⊗ₖ proj0 + P₃ ⊗ₖ proj1) *
        bcgate ((1 : Square 2) ⊗ₖ (proj0 * Q†) + P₄ ⊗ₖ (proj1 * Q†))
        = ((1 : Square 2) ⊗ₖ (1 : Square 2)) ⊗ₖ (Q * proj0 * Q†) +
          ((P₁ * P₃) ⊗ₖ (P₂ * P₄)) ⊗ₖ (Q * proj1 * Q†) := by
    repeat rw [acgate_add]
    repeat rw [bcgate_add]
    repeat rw [acgate_kron_two]
    repeat rw [bcgate_kron_two]
    repeat rw [← kron_assoc_222]
    repeat rw [mul_add]
    repeat rw [add_mul]
    repeat rw [mul_assoc]
    repeat rw [kron_mul_three]
    simp [TwoControl.zero_kron_right, add_comm]

/-- **Lemma 6.4** (The second main lemma).
Suppose `|u₀| = |u₁| = 1`. There exist 2-qubit unitaries `U₁, U₂, U₃, U₄`
such that `U₁^{AC} U₂^{BC} U₃^{AC} U₄^{BC} = CC(Diag(u₀, u₁))`
if and only if either `u₀ = u₁` or `u₀ u₁ = 1`. -/
lemma section6_lemma_6_4
    (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (U₁ U₂ U₃ U₄ : Square 4),
      U₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₂ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₃ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      U₄ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      acgate U₁ * bcgate U₂ * acgate U₃ * bcgate U₄ = ccu (diag2 u₀ u₁))
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by
  constructor
  · rintro ⟨U₁, U₂, U₃, U₄, hU₁, hU₂, hU₃, hU₄, heq⟩
    rcases section6_lemma_6_4_normalize_V₃ U₁ U₂ U₃ U₄ hU₁ hU₂ hU₃ hU₄ with
      ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, hNormEq, hV₃fix⟩
    have heqV : acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄ = ccu (diag2 u₀ u₁) := by
      calc
        acgate V₁ * bcgate V₂ * acgate V₃ * bcgate V₄
            = acgate U₁ * bcgate U₂ * acgate U₃ * bcgate U₄ := by
                symm
                exact hNormEq
        _ = ccu (diag2 u₀ u₁) := heq
    have hident :=
      section6_lemma_6_4_identity_transfer u₀ u₁ V₁ V₂ V₃ V₄ hV₄ heqV hV₃fix
    rcases section6_lemma_6_1 V₂ hV₂ with hA | hB | hC
    · exact section6_lemma_6_4_caseA u₀ u₁ hu₀ hu₁ V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ heqV hident hA
    · rcases section6_lemma_6_3 u₀ u₁ hu₀ hu₁ V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ heqV hB with
        hEq | hRest
      · exact Or.inl hEq
      ·
        rcases hRest with hProd |
          ⟨W₁, W₂, W₃, W₄, hW₁, hW₂, hW₃, hW₄, P₁, P₂, P₃, P₄, Q,
            hP₁, hP₂, hP₃, hP₄, hQ, heqW, hW₁eq, hW₂eq, hW₃eq, hW₄eq⟩
        · exact Or.inr hProd
        ·
          have hSpecial :
            ((1 : Square 2) ⊗ₖ (1 : Square 2)) ⊗ₖ (Q * proj0 * Q†) +
              ((P₁ * P₃) ⊗ₖ (P₂ * P₄)) ⊗ₖ (Q * proj1 * Q†) = ccu (diag2 u₀ u₁) := by
            calc
              ((1 : Square 2) ⊗ₖ (1 : Square 2)) ⊗ₖ (Q * proj0 * Q†) +
                  ((P₁ * P₃) ⊗ₖ (P₂ * P₄)) ⊗ₖ (Q * proj1 * Q†)
                  = acgate W₁ * bcgate W₂ * acgate W₃ * bcgate W₄ := by
                      symm
                      simpa [hW₁eq, hW₂eq, hW₃eq, hW₄eq] using
                        (section6_lemma_6_4_special_word P₁ P₂ P₃ P₄ Q)
              _ = ccu (diag2 u₀ u₁) := heqW
          have hOne : u₀ = 1 ∧ u₁ = 1 :=
            (section4_lemma_4_2 u₀ u₁ hu₀ hu₁ Q hQ).1 <| by
              refine ⟨P₁ * P₃, P₂ * P₄, Submonoid.mul_mem _ hP₁ hP₃,
                Submonoid.mul_mem _ hP₂ hP₄, ?_⟩
              calc
                ((1 : Square 2) ⊗ₖ (1 : Square 2)) ⊗ₖ ketbra (Q.mulVec ket0) (Q.mulVec ket0) +
                    ((P₁ * P₃) ⊗ₖ (P₂ * P₄)) ⊗ₖ ketbra (Q.mulVec ket1) (Q.mulVec ket1)
                    = ((1 : Square 2) ⊗ₖ (1 : Square 2)) ⊗ₖ (Q * proj0 * Q†) +
                        ((P₁ * P₃) ⊗ₖ (P₂ * P₄)) ⊗ₖ (Q * proj1 * Q†) := by
                            rw [conj_proj0_eq_ketbra, conj_proj1_eq_ketbra]
                _ = ccu (diag2 u₀ u₁) := hSpecial
          rcases hOne with ⟨hu₀one, hu₁one⟩
          exact Or.inl (by rw [hu₀one, hu₁one])
    · exact section6_lemma_6_4_caseC u₀ u₁ hu₀ hu₁ V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ heqV hident hC
  · intro h
    rcases (section4_lemma_4_3 u₀ u₁ hu₀ hu₁).2 h with
      ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, P₀, P₁, hP₀, hP₁, hV₁eq, heq⟩
    exact ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, heq⟩

end TwoControl

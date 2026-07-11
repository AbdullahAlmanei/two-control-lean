import TwoControl.Clifford.Universal.GateSets
import TwoControl.CosineSine.Statements

namespace TwoControl
namespace Clifford
namespace Universal

open Matrix

/-- Concrete two-qubit Paige-Wei decomposition data. -/
def TwoQubitCosineSineWitness (_U P R Q : Square 4) : Prop :=
  ∃ (P₀ P₁ Q₀ Q₁ : Square 2) (θ₀ θ₁ : ℝ),
    P₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    P₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    Q₀ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    Q₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    P = CosineSine.blockDiag2 P₀ P₁ ∧
    R = CosineSine.conditionalRy θ₀ θ₁ ∧
    Q = CosineSine.blockDiag2 Q₀ Q₁

private theorem unblockify_mem_unitaryGroup {n : ℕ} {M : BlockMatrix n}
    (hM : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ) :
    unblockify M ∈ Matrix.unitaryGroup (Fin (2 * n)) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.2
  apply blockify_injective (n := n)
  calc
    blockify ((unblockify M)† * unblockify M) = M† * M := by
      simp [blockify, unblockify]
    _ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hM
    _ = blockify (1 : Square (2 * n)) := by
      symm
      simpa [blockify] using
        (Matrix.submatrix_one_equiv (finTwoBlockEquiv n))

private theorem blockDiag2_eq_unblockify_fromBlocks (A D : Square 2) :
    CosineSine.blockDiag2 A D = unblockify (Matrix.fromBlocks A 0 0 D) := by
  rw [CosineSine.blockDiag2, unblockify_fromBlocks]
  simp [zero_kron_right]

theorem blockDiag2_mem_unitaryGroup {A D : Square 2}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hD : D ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    CosineSine.blockDiag2 A D ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [blockDiag2_eq_unblockify_fromBlocks]
  exact unblockify_mem_unitaryGroup
    (BlockHelpers.fromBlocks_diagonal_unitary A D hA hD)

private theorem middle_factor_mem_unitaryGroup {U P R Q : Square 4}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hP : P ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (hEq : U = P * R * Q) :
    R ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have hPdag : P† ∈ Matrix.unitaryGroup (Fin 4) ℂ := conjTranspose_mem_unitaryGroup hP
  have hQdag : Q† ∈ Matrix.unitaryGroup (Fin 4) ℂ := conjTranspose_mem_unitaryGroup hQ
  have hLeft : P† * P = (1 : Square 4) := Matrix.mem_unitaryGroup_iff'.mp hP
  have hRight : Q * Q† = (1 : Square 4) := Matrix.mem_unitaryGroup_iff.mp hQ
  have hR : R = P† * U * Q† := by
    calc
      R = (1 : Square 4) * R * (1 : Square 4) := by simp
      _ = (P† * P) * R * (Q * Q†) := by rw [hLeft, hRight]
      _ = P† * U * Q† := by rw [hEq]; simp [mul_assoc]
  rw [hR]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hPdag hU) hQdag

/-- Concrete 2-qubit Paige-Wei cosine-sine step obtained from the existing
paper-facing theorem in `TwoControl.CosineSine.Statements`. -/
theorem two_qubit_cosine_sine_step (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ P R Q : Square 4,
      P ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      R ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      Q ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      TwoQubitCosineSineWitness U P R Q ∧
      U = P * R * Q := by
  rcases CosineSine.cosinesine_exists U hU with
    ⟨P₀, P₁, Q₀, Q₁, θ₀, θ₁, hP₀, hP₁, hQ₀, hQ₁, hEq⟩
  let P : Square 4 := CosineSine.blockDiag2 P₀ P₁
  let R : Square 4 := CosineSine.conditionalRy θ₀ θ₁
  let Q : Square 4 := CosineSine.blockDiag2 Q₀ Q₁
  have hP : P ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    dsimp [P]
    exact blockDiag2_mem_unitaryGroup hP₀ hP₁
  have hQ : Q ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    dsimp [Q]
    exact blockDiag2_mem_unitaryGroup hQ₀ hQ₁
  have hEq' : U = P * R * Q := by
    simpa [P, R, Q] using hEq
  have hR : R ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
    middle_factor_mem_unitaryGroup hU hP hQ hEq'
  refine ⟨P, R, Q, hP, hR, hQ, ?_, hEq'⟩
  exact ⟨P₀, P₁, Q₀, Q₁, θ₀, θ₁, hP₀, hP₁, hQ₀, hQ₁, rfl, rfl, rfl⟩

end Universal
end Clifford
end TwoControl

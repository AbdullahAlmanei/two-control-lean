import TwoControl.BlockHelpers
import TwoControl.DiagonalizationHelpers
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Eigenspace.Matrix

open scoped Matrix ComplexOrder ComplexStarModule
open Matrix
open Module.End

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

private lemma blockify_W (u₀ u₁ : ℂ) :
    blockify (n := 4) (diag2 u₀ u₁ ⊗ₖ (1 : Square 4)) =
      Matrix.fromBlocks (u₀ • (1 : Square 4)) 0 0 (u₁ • (1 : Square 4)) := by
  simpa using blockify_diag2_kron_one (n := 4) u₀ u₁

private lemma block_one_eq (n : ℕ) :
    (1 : BlockMatrix n) = Matrix.fromBlocks (1 : Square n) 0 0 (1 : Square n) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]

private lemma block_scalar_eq (u : ℂ) (n : ℕ) :
    Matrix.fromBlocks (u • (1 : Square n)) 0 0 (u • (1 : Square n)) = u • (1 : BlockMatrix n) := by
  rw [block_one_eq]
  symm
  simpa using (Matrix.fromBlocks_smul u (1 : Square n) (0 : Square n) (0 : Square n) (1 : Square n))

private lemma smul_eq_smul_implies_zero {n : ℕ} {a b : ℂ} {M : Square n}
    (hab : a ≠ b) (h : a • M = b • M) : M = 0 := by
  ext i j
  have hij : a * M i j = b * M i j := by
    simpa using congrFun (congrFun h i) j
  have hzero : (a - b) * M i j = 0 := by
    rw [sub_mul, hij, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hab)

private lemma block_diagonal_unitary {n : ℕ} (A D : Square n)
    (h : Matrix.fromBlocks A 0 0 D ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ) :
    A ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ D ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rcases h with ⟨hleft, hright⟩
  have hleft' := hleft
  rw [star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at hleft'
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero] at hleft'
  rw [block_one_eq] at hleft'
  have hright' := hright
  rw [star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at hright'
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero] at hright'
  rw [block_one_eq] at hright'
  rcases Matrix.fromBlocks_inj.mp hleft' with ⟨hAleft, _, _, hDleft⟩
  rcases Matrix.fromBlocks_inj.mp hright' with ⟨hAright, _, _, hDright⟩
  exact ⟨⟨by simpa [star_eq_conjTranspose] using hAleft,
            by simpa [star_eq_conjTranspose] using hAright⟩,
         ⟨by simpa [star_eq_conjTranspose] using hDleft,
            by simpa [star_eq_conjTranspose] using hDright⟩⟩

/-- **Lemma 3.1** (Commutativity characterization).
    Suppose `u₀, u₁` are unit complex numbers.
    An 8×8 unitary `U` commutes with `Diag(u₀, u₁) ⊗ I₂ ⊗ I₂`
    if and only if either `u₀ = u₁` or
    `U = |0⟩⟨0| ⊗ V₀₀ + |1⟩⟨1| ⊗ V₁₁`
    for some 4×4 unitaries `V₀₀, V₁₁`. -/
lemma section3_lemma_3_1 (u₀ u₁ : ℂ) (_hu₀ : ‖u₀‖ = 1) (_hu₁ : ‖u₁‖ = 1)
    (U : Square 8) (hU : U ∈ Matrix.unitaryGroup (Fin 8) ℂ) :
    (U * (diag2 u₀ u₁ ⊗ₖ (1 : Square 2) ⊗ₖ (1 : Square 2)) =
     (diag2 u₀ u₁ ⊗ₖ (1 : Square 2) ⊗ₖ (1 : Square 2)) * U)
    ↔ u₀ = u₁ ∨
      (∃ (V₀₀ V₁₁ : Square 4),
        V₀₀ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
        V₁₁ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
        U = proj0 ⊗ₖ V₀₀ + proj1 ⊗ₖ V₁₁) := by
  set W : Square 8 := (((diag2 u₀ u₁ ⊗ₖ (1 : Square 2)) : Square 4) ⊗ₖ (1 : Square 2))
  change U * W = W * U ↔ _
  have hWb : blockify W = Matrix.fromBlocks (u₀ • (1 : Square 4)) 0 0 (u₁ • (1 : Square 4)) := by
    simpa [W, kron_one_assoc] using blockify_W u₀ u₁
  constructor
  · intro hcomm
    by_cases heq : u₀ = u₁
    · exact Or.inl heq
    · right
      let Ub : BlockMatrix 4 := blockify U
      let U00 : Square 4 := Ub.toBlocks₁₁
      let U01 : Square 4 := Ub.toBlocks₁₂
      let U10 : Square 4 := Ub.toBlocks₂₁
      let U11 : Square 4 := Ub.toBlocks₂₂
      have hUb_blocks : Ub = Matrix.fromBlocks U00 U01 U10 U11 := by
        symm
        exact Matrix.fromBlocks_toBlocks Ub
      have hcommb : Ub * blockify W = blockify W * Ub := by
        dsimp [Ub]
        simpa [TwoControl.blockify_mul] using congrArg (blockify (n := 4)) hcomm
      have hblocks :
          Matrix.fromBlocks (u₀ • U00) (u₁ • U01) (u₀ • U10) (u₁ • U11) =
            Matrix.fromBlocks (u₀ • U00) (u₀ • U01) (u₁ • U10) (u₁ • U11) := by
        calc
          Matrix.fromBlocks (u₀ • U00) (u₁ • U01) (u₀ • U10) (u₁ • U11) = Ub * blockify W := by
            rw [hUb_blocks, hWb, Matrix.fromBlocks_multiply]
            simp
          _ = blockify W * Ub := hcommb
          _ = Matrix.fromBlocks (u₀ • U00) (u₀ • U01) (u₁ • U10) (u₁ • U11) := by
            rw [hUb_blocks, hWb, Matrix.fromBlocks_multiply]
            simp
      rcases Matrix.fromBlocks_inj.mp hblocks with ⟨_, h01, h10, _⟩
      have hU01_zero : U01 = 0 := by
        apply smul_eq_smul_implies_zero (a := u₁) (b := u₀)
        · intro h
          exact heq h.symm
        · exact h01
      have hU10_zero : U10 = 0 := by
        apply smul_eq_smul_implies_zero (a := u₀) (b := u₁)
        · exact heq
        · exact h10
      have hUb_diag : Ub = Matrix.fromBlocks U00 0 0 U11 := by
        rw [hUb_blocks, hU01_zero, hU10_zero]
      have hUb_unitary : Ub ∈ Matrix.unitaryGroup (Fin 4 ⊕ Fin 4) ℂ := by
        simpa [Ub] using (blockify_mem_unitaryGroup_iff (n := 4) (U := U)).2 hU
      have hUb_diag_unitary : Matrix.fromBlocks U00 0 0 U11 ∈ Matrix.unitaryGroup (Fin 4 ⊕ Fin 4) ℂ := by
        simpa [hUb_diag] using hUb_unitary
      have ⟨hU00_unitary, hU11_unitary⟩ := block_diagonal_unitary U00 U11 hUb_diag_unitary
      have hU_form : U = proj0 ⊗ₖ U00 + proj1 ⊗ₖ U11 := by
        calc
          U = unblockify Ub := by
            dsimp [Ub]
            simp
          _ = unblockify (Matrix.fromBlocks U00 0 0 U11) := by rw [hUb_diag]
          _ = proj0 ⊗ₖ U00 + proj01 ⊗ₖ (0 : Square 4) + proj10 ⊗ₖ (0 : Square 4) + proj1 ⊗ₖ U11 := by
            simpa using (unblockify_fromBlocks U00 (0 : Square 4) (0 : Square 4) U11)
          _ = proj0 ⊗ₖ U00 + proj1 ⊗ₖ U11 := by
            rw [TwoControl.zero_kron_right, TwoControl.zero_kron_right]
            simp
      exact ⟨U00, U11, hU00_unitary, hU11_unitary, hU_form⟩
  · intro h
    rcases h with heq | ⟨V₀₀, V₁₁, _, _, hUeq⟩
    · have hWscalar : blockify W = u₀ • (1 : BlockMatrix 4) := by
        calc
          blockify W = Matrix.fromBlocks (u₀ • (1 : Square 4)) 0 0 (u₁ • (1 : Square 4)) := hWb
          _ = Matrix.fromBlocks (u₀ • (1 : Square 4)) 0 0 (u₀ • (1 : Square 4)) := by rw [heq]
          _ = u₀ • (1 : BlockMatrix 4) := block_scalar_eq u₀ 4
      apply (blockify_injective (n := 4))
      calc
        blockify (U * W) = blockify U * blockify W := by rw [TwoControl.blockify_mul]
        _ = blockify U * (u₀ • (1 : BlockMatrix 4)) := by rw [hWscalar]
        _ = u₀ • blockify U := by rw [mul_smul_comm, mul_one]
        _ = (u₀ • (1 : BlockMatrix 4)) * blockify U := by
          symm
          rw [smul_mul_assoc, one_mul]
        _ = blockify W * blockify U := by rw [hWscalar]
        _ = blockify (W * U) := by rw [TwoControl.blockify_mul]
    · have hUb : blockify U = Matrix.fromBlocks V₀₀ 0 0 V₁₁ := by
        rw [hUeq, TwoControl.blockify_add, TwoControl.blockify_proj0_kron,
          TwoControl.blockify_proj1_kron, Matrix.fromBlocks_add]
        simp
      apply (blockify_injective (n := 4))
      calc
        blockify (U * W) = blockify U * blockify W := by rw [TwoControl.blockify_mul]
        _ = Matrix.fromBlocks V₀₀ 0 0 V₁₁ * Matrix.fromBlocks (u₀ • (1 : Square 4)) 0 0 (u₁ • (1 : Square 4)) := by
          rw [hUb, hWb]
        _ = Matrix.fromBlocks (u₀ • V₀₀) 0 0 (u₁ • V₁₁) := by
          rw [Matrix.fromBlocks_multiply]
          simp
        _ = Matrix.fromBlocks (u₀ • (1 : Square 4)) 0 0 (u₁ • (1 : Square 4)) * Matrix.fromBlocks V₀₀ 0 0 V₁₁ := by
          symm
          rw [Matrix.fromBlocks_multiply]
          simp
        _ = blockify W * blockify U := by rw [hUb, hWb]
        _ = blockify (W * U) := by rw [TwoControl.blockify_mul]

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
    simpa [star_eq_conjTranspose] using notc_conjTranspose, notc_mul_notc]

private lemma notc_conj_diag4 (a b c d : ℂ) :
    notc * diag4 a b c d * notc† = diag4 a d c b := by
  rw [notc_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ, notc, diag4]

private lemma tensor_witness_of_eq (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ (P Q : Square 2) (V : Square 4),
      P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      V ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      P ⊗ₖ Q = V * diag4 1 1 u u * V† := by
  refine ⟨diag2 1 u, 1, 1, ?_, ?_, ?_, ?_⟩
  · exact diag2_unitary 1 u (by simp) hu
  · exact Submonoid.one_mem _
  · exact Submonoid.one_mem _
  · simp [diag2_one_right_kron]

private lemma tensor_witness_of_mul_eq_one
    (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) (h : u₀ * u₁ = 1) :
    ∃ (P Q : Square 2) (V : Square 4),
      P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      V ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      P ⊗ₖ Q = V * diag4 1 1 u₀ u₁ * V† := by
  refine ⟨diag2 1 u₀, diag2 1 u₁, notc, ?_, ?_, notc_unitary, ?_⟩
  · exact diag2_unitary 1 u₀ (by simp) hu₀
  · exact diag2_unitary 1 u₁ (by simp) hu₁
  · calc
      diag2 1 u₀ ⊗ₖ diag2 1 u₁ = diag4 1 u₁ u₀ 1 := by
        simpa [h] using diag2_kron_diag2 1 u₀ 1 u₁
      _ = notc * diag4 1 1 u₀ u₁ * notc† := by
        symm
        simpa using notc_conj_diag4 1 1 u₀ u₁

private lemma eq_or_mul_eq_one_of_three_multiset
    {x y z u₀ u₁ : ℂ}
    (hxyz : ({x, y, z} : Multiset ℂ) = ({1, u₀, u₁} : Multiset ℂ))
    (hmul : x * y = z) :
    u₀ = u₁ ∨ u₀ * u₁ = 1 := by
  have hmem : (1 : ℂ) ∈ ({x, y, z} : Multiset ℂ) := by
    rw [hxyz]
    simp
  rcases (by simpa [Multiset.mem_cons, eq_comm, or_left_comm, or_assoc] using hmem :
      1 = x ∨ 1 = y ∨ 1 = z) with hx | hy | hz
  · have hyz : ({y, z} : Multiset ℂ) = ({u₀, u₁} : Multiset ℂ) := by
      apply (Multiset.cons_inj_right (1 : ℂ)).mp
      calc
        (1 : ℂ) ::ₘ ({y, z} : Multiset ℂ) = ({x, y, z} : Multiset ℂ) := by
          simp [hx.symm]
        _ = ({1, u₀, u₁} : Multiset ℂ) := hxyz
        _ = (1 : ℂ) ::ₘ ({u₀, u₁} : Multiset ℂ) := rfl
    have hyz' : y = z := by simpa [hx.symm] using hmul
    have hu₀ : u₀ = y := by
      have : u₀ ∈ ({y, z} : Multiset ℂ) := by
        rw [hyz]
        simp
      simpa [hyz', Multiset.mem_cons, or_left_comm, or_assoc] using this
    have hu₁ : u₁ = y := by
      have : u₁ ∈ ({y, z} : Multiset ℂ) := by
        rw [hyz]
        simp
      simpa [hyz', Multiset.mem_cons, or_left_comm, or_assoc] using this
    exact Or.inl (hu₀.trans hu₁.symm)
  · have hxz : ({x, z} : Multiset ℂ) = ({u₀, u₁} : Multiset ℂ) := by
      apply (Multiset.cons_inj_right (1 : ℂ)).mp
      calc
        (1 : ℂ) ::ₘ ({x, z} : Multiset ℂ) = ({x, y, z} : Multiset ℂ) := by
          simp [hy.symm, Multiset.cons_swap]
        _ = ({1, u₀, u₁} : Multiset ℂ) := hxyz
        _ = (1 : ℂ) ::ₘ ({u₀, u₁} : Multiset ℂ) := rfl
    have hxz' : x = z := by simpa [hy.symm] using hmul
    have hu₀ : u₀ = x := by
      have : u₀ ∈ ({x, z} : Multiset ℂ) := by
        rw [hxz]
        simp
      simpa [hxz', Multiset.mem_cons, or_left_comm, or_assoc] using this
    have hu₁ : u₁ = x := by
      have : u₁ ∈ ({x, z} : Multiset ℂ) := by
        rw [hxz]
        simp
      simpa [hxz', Multiset.mem_cons, or_left_comm, or_assoc] using this
    exact Or.inl (hu₀.trans hu₁.symm)
  · have hxy : ({x, y} : Multiset ℂ) = ({u₀, u₁} : Multiset ℂ) := by
      apply (Multiset.cons_inj_right (1 : ℂ)).mp
      calc
        (1 : ℂ) ::ₘ ({x, y} : Multiset ℂ) = ({x, y, z} : Multiset ℂ) := by
          rw [hz.symm]
          calc
            (1 : ℂ) ::ₘ ({x, y} : Multiset ℂ) = x ::ₘ (1 : ℂ) ::ₘ ({y} : Multiset ℂ) := by
              simpa using (Multiset.cons_swap (1 : ℂ) x ({y} : Multiset ℂ))
            _ = x ::ₘ y ::ₘ ({1} : Multiset ℂ) := by
              simpa using congrArg (fun s : Multiset ℂ => x ::ₘ s)
                (Multiset.cons_swap (1 : ℂ) y (0 : Multiset ℂ))
        _ = ({1, u₀, u₁} : Multiset ℂ) := hxyz
        _ = (1 : ℂ) ::ₘ ({u₀, u₁} : Multiset ℂ) := rfl
    have hprod : u₀ * u₁ = x * y := by
      calc
        u₀ * u₁ = ({u₀, u₁} : Multiset ℂ).prod := by simp
        _ = ({x, y} : Multiset ℂ).prod := by rw [← hxy]
        _ = x * y := by simp
    exact Or.inr <| by calc
      u₀ * u₁ = x * y := hprod
      _ = z := hmul
      _ = 1 := hz.symm

/-- **Lemma 3.2** (Eigenvalue condition for tensor product). -/
lemma section3_lemma_3_2 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (P Q : Square 2) (V : Square 4),
      P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      V ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      P ⊗ₖ Q = V * diag4 1 1 u₀ u₁ * V†)
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by
  constructor
  · intro h
    rcases h with ⟨P, Q, V, hP, hQ, hV, hEq⟩
    rcases unitary_diag2_exists P hP with ⟨a, b, UP, ha, hb, hUP, hPdiag⟩
    rcases unitary_diag2_exists Q hQ with ⟨c, d, UQ, hc, hd, hUQ, hQdiag⟩
    have hPQdiag :
        P ⊗ₖ Q = (UP ⊗ₖ UQ) * diag4 (a * c) (a * d) (b * c) (b * d) * (UP ⊗ₖ UQ)† := by
      calc
        P ⊗ₖ Q = (UP * diag2 a b * UP†) ⊗ₖ (UQ * diag2 c d * UQ†) := by rw [hPdiag, hQdiag]
        _ = ((UP * diag2 a b) ⊗ₖ (UQ * diag2 c d)) * (UP† ⊗ₖ UQ†) := by
          rw [kron_mul_two]
        _ = ((UP ⊗ₖ UQ) * (diag2 a b ⊗ₖ diag2 c d)) * (UP† ⊗ₖ UQ†) := by
          rw [kron_mul_two]
        _ = (UP ⊗ₖ UQ) * diag4 (a * c) (a * d) (b * c) (b * d) * (UP† ⊗ₖ UQ†) := by
          rw [diag2_kron_diag2]
        _ = (UP ⊗ₖ UQ) * diag4 (a * c) (a * d) (b * c) (b * d) * (UP ⊗ₖ UQ)† := by
          rw [conjTranspose_kron_two]
    have hW : UP ⊗ₖ UQ ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
      kron_unitary_two UP UQ hUP hUQ
    have hcharLeft : (P ⊗ₖ Q).charpoly = (diag4 (a * c) (a * d) (b * c) (b * d)).charpoly := by
      rw [hPQdiag]
      exact charpoly_unitary_conj (UP ⊗ₖ UQ) _ hW
    have hcharRight : (P ⊗ₖ Q).charpoly = (diag4 1 1 u₀ u₁).charpoly := by
      rw [hEq]
      exact charpoly_unitary_conj V _ hV
    have hroots : ({a * c, a * d, b * c, b * d} : Multiset ℂ) = ({1, 1, u₀, u₁} : Multiset ℂ) := by
      rw [← roots_charpoly_diag4 (a * c) (a * d) (b * c) (b * d),
        ← roots_charpoly_diag4 1 1 u₀ u₁, ← hcharLeft, hcharRight]
    have hmem : (1 : ℂ) ∈ ({a * c, a * d, b * c, b * d} : Multiset ℂ) := by
      rw [hroots]
      simp
    rcases (by simpa [Multiset.mem_cons, eq_comm, or_left_comm, or_assoc] using hmem :
        1 = a * c ∨ 1 = a * d ∨ 1 = b * c ∨ 1 = b * d) with hac | had | hbc | hbd
    · have hthree : ({a * d, b * c, b * d} : Multiset ℂ) = ({1, u₀, u₁} : Multiset ℂ) := by
        apply (Multiset.cons_inj_right (1 : ℂ)).mp
        calc
          (1 : ℂ) ::ₘ ({a * d, b * c, b * d} : Multiset ℂ) =
              ({a * c, a * d, b * c, b * d} : Multiset ℂ) := by
            simp [hac.symm]
          _ = ({1, 1, u₀, u₁} : Multiset ℂ) := hroots
          _ = (1 : ℂ) ::ₘ ({1, u₀, u₁} : Multiset ℂ) := rfl
      have hmul : (a * d) * (b * c) = b * d := by
        calc
          (a * d) * (b * c) = (a * c) * (b * d) := by ring
          _ = b * d := by simp [hac.symm]
      exact eq_or_mul_eq_one_of_three_multiset hthree hmul
    · have hthree0 : ({a * c, b * c, b * d} : Multiset ℂ) = ({1, u₀, u₁} : Multiset ℂ) := by
        apply (Multiset.cons_inj_right (1 : ℂ)).mp
        calc
          (1 : ℂ) ::ₘ ({a * c, b * c, b * d} : Multiset ℂ) =
              ({a * c, a * d, b * c, b * d} : Multiset ℂ) := by
            simp [had.symm, Multiset.cons_swap]
          _ = ({1, 1, u₀, u₁} : Multiset ℂ) := hroots
          _ = (1 : ℂ) ::ₘ ({1, u₀, u₁} : Multiset ℂ) := rfl
      have hthree : ({a * c, b * d, b * c} : Multiset ℂ) = ({1, u₀, u₁} : Multiset ℂ) := by
        calc
          ({a * c, b * d, b * c} : Multiset ℂ) = ({a * c, b * c, b * d} : Multiset ℂ) := by
            simpa using congrArg (fun s : Multiset ℂ => a * c ::ₘ s)
              (Multiset.cons_swap (b * d) (b * c) (0 : Multiset ℂ))
          _ = ({1, u₀, u₁} : Multiset ℂ) := hthree0
      have hmul : (a * c) * (b * d) = b * c := by
        calc
          (a * c) * (b * d) = (a * d) * (b * c) := by ring
          _ = b * c := by simp [had.symm]
      exact eq_or_mul_eq_one_of_three_multiset hthree hmul
    · have hthree0 : ({a * c, a * d, b * d} : Multiset ℂ) = ({1, u₀, u₁} : Multiset ℂ) := by
        apply (Multiset.cons_inj_right (1 : ℂ)).mp
        calc
          (1 : ℂ) ::ₘ ({a * c, a * d, b * d} : Multiset ℂ) =
              ({a * c, a * d, b * c, b * d} : Multiset ℂ) := by
            simp [hbc.symm, Multiset.cons_swap]
          _ = ({1, 1, u₀, u₁} : Multiset ℂ) := hroots
          _ = (1 : ℂ) ::ₘ ({1, u₀, u₁} : Multiset ℂ) := rfl
      have hthree : ({a * c, b * d, a * d} : Multiset ℂ) = ({1, u₀, u₁} : Multiset ℂ) := by
        calc
          ({a * c, b * d, a * d} : Multiset ℂ) = ({a * c, a * d, b * d} : Multiset ℂ) := by
            simpa using congrArg (fun s : Multiset ℂ => a * c ::ₘ s)
              (Multiset.cons_swap (b * d) (a * d) (0 : Multiset ℂ))
          _ = ({1, u₀, u₁} : Multiset ℂ) := hthree0
      have hmul : (a * c) * (b * d) = a * d := by
        calc
          (a * c) * (b * d) = (a * d) * (b * c) := by ring
          _ = a * d := by simp [hbc.symm]
      exact eq_or_mul_eq_one_of_three_multiset hthree hmul
    · have hthree0 : ({a * c, a * d, b * c} : Multiset ℂ) = ({1, u₀, u₁} : Multiset ℂ) := by
        apply (Multiset.cons_inj_right (1 : ℂ)).mp
        calc
          (1 : ℂ) ::ₘ ({a * c, a * d, b * c} : Multiset ℂ) =
              ({a * c, a * d, b * c, b * d} : Multiset ℂ) := by
            calc
              (1 : ℂ) ::ₘ ({a * c, a * d, b * c} : Multiset ℂ) =
                  a * c ::ₘ (1 : ℂ) ::ₘ ({a * d, b * c} : Multiset ℂ) := by
                simpa using (Multiset.cons_swap (1 : ℂ) (a * c) ({a * d, b * c} : Multiset ℂ))
              _ = a * c ::ₘ a * d ::ₘ (1 : ℂ) ::ₘ ({b * c} : Multiset ℂ) := by
                simpa using congrArg (fun s : Multiset ℂ => a * c ::ₘ s)
                  (Multiset.cons_swap (1 : ℂ) (a * d) ({b * c} : Multiset ℂ))
              _ = a * c ::ₘ a * d ::ₘ b * c ::ₘ ({1} : Multiset ℂ) := by
                simpa using congrArg (fun s : Multiset ℂ => a * c ::ₘ a * d ::ₘ s)
                  (Multiset.cons_swap (1 : ℂ) (b * c) (0 : Multiset ℂ))
              _ = ({a * c, a * d, b * c, b * d} : Multiset ℂ) := by
                rw [hbd]
                rfl
          _ = ({1, 1, u₀, u₁} : Multiset ℂ) := hroots
          _ = (1 : ℂ) ::ₘ ({1, u₀, u₁} : Multiset ℂ) := rfl
      have hthree : ({a * d, b * c, a * c} : Multiset ℂ) = ({1, u₀, u₁} : Multiset ℂ) := by
        calc
          ({a * d, b * c, a * c} : Multiset ℂ) = ({a * d, a * c, b * c} : Multiset ℂ) := by
            simpa using congrArg (fun s : Multiset ℂ => a * d ::ₘ s)
              (Multiset.cons_swap (b * c) (a * c) (0 : Multiset ℂ))
          _ = ({a * c, a * d, b * c} : Multiset ℂ) := by
            simpa using (Multiset.cons_swap (a * d) (a * c) ({b * c} : Multiset ℂ))
          _ = ({1, u₀, u₁} : Multiset ℂ) := hthree0
      have hmul : (a * d) * (b * c) = a * c := by
        calc
          (a * d) * (b * c) = (a * c) * (b * d) := by ring
          _ = a * c := by simp [hbd.symm]
      exact eq_or_mul_eq_one_of_three_multiset hthree hmul
  · intro h
    rcases h with rfl | hmul
    · simpa using tensor_witness_of_eq u₀ hu₀
    · exact tensor_witness_of_mul_eq_one u₀ u₁ hu₀ hu₁ hmul

private lemma diag2_same_eq_smul_one (a : ℂ) :
    diag2 a a = a • (1 : Square 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2]

private lemma kron_smul_right (A : Square m) (c : ℂ) (B : Square n) :
    A ⊗ₖ (c • B) = c • (A ⊗ₖ B) := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (@finProdFinEquiv m n).surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (@finProdFinEquiv m n).surjective j
  simp [TwoControl.kron_apply, mul_left_comm]

private lemma det_diag2 (a b : ℂ) : (diag2 a b).det = a * b := by
  simp [diag2, Matrix.det_diagonal]

private lemma det_of_unitary_diag2_decomp {A : Square 2} {a b : ℂ} {U : Square 2}
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

private lemma diag4_unitary (a b c d : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
    diag4 a b c d ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag4, Complex.conj_mul', ha, hb, hc, hd]

private lemma diag4_repeat_norms_of_mem_unitaryGroup {c d : ℂ}
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

@[simp] private lemma finProdFinEquiv_00 : (@finProdFinEquiv 2 2 (0, 0) : Fin 4) = 0 := by
  native_decide

@[simp] private lemma finProdFinEquiv_01 : (@finProdFinEquiv 2 2 (0, 1) : Fin 4) = 1 := by
  native_decide

@[simp] private lemma finProdFinEquiv_10 : (@finProdFinEquiv 2 2 (1, 0) : Fin 4) = 2 := by
  native_decide

@[simp] private lemma finProdFinEquiv_11 : (@finProdFinEquiv 2 2 (1, 1) : Fin 4) = 3 := by
  native_decide

@[simp] private lemma vec4_apply_finProd_00 {α : Type*} (a b c d : α) :
    (![a, b, c, d] : Fin 4 → α) (@finProdFinEquiv 2 2 (0, 0)) = a := by
  rw [finProdFinEquiv_00]
  rfl

@[simp] private lemma vec4_apply_finProd_01 {α : Type*} (a b c d : α) :
    (![a, b, c, d] : Fin 4 → α) (@finProdFinEquiv 2 2 (0, 1)) = b := by
  rw [finProdFinEquiv_01]
  rfl

@[simp] private lemma vec4_apply_finProd_10 {α : Type*} (a b c d : α) :
    (![a, b, c, d] : Fin 4 → α) (@finProdFinEquiv 2 2 (1, 0)) = c := by
  rw [finProdFinEquiv_10]
  rfl

@[simp] private lemma vec4_apply_finProd_11 {α : Type*} (a b c d : α) :
    (![a, b, c, d] : Fin 4 → α) (@finProdFinEquiv 2 2 (1, 1)) = d := by
  rw [finProdFinEquiv_11]
  rfl

private lemma one_kron_diag2 (c d : ℂ) :
    (1 : Square 2) ⊗ₖ diag2 c d = diag4 c d c d := by
  rw [← diag2_one_one]
  simpa using diag2_kron_diag2 1 1 c d

private lemma one_kron_mul_controlledGate_diag2 (P : Square 2) (u₀ u₁ : ℂ) :
    (1 : Square 2) ⊗ₖ P * controlledGate (diag2 u₀ u₁) =
      proj0 ⊗ₖ P + proj1 ⊗ₖ (P * diag2 u₀ u₁) := by
  rw [controlledGate, Matrix.mul_add, ← kron_mul_two, ← kron_mul_two]
  simp

private lemma fromBlocks_diagonal_unitary {n : ℕ} (A D : Square n)
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hD : D ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix.fromBlocks A 0 0 D ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
  have hAleft : A† * A = 1 := by
    simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'] using hA
  have hAright : A * A† = 1 := by
    simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff] using hA
  have hDleft : D† * D = 1 := by
    simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'] using hD
  have hDright : D * D† = 1 := by
    simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff] using hD
  constructor
  · rw [star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, block_one_eq]
    simp [hAleft, hDleft]
  · rw [star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, block_one_eq]
    simp [hAright, hDright]

private lemma blockify_diag4 (a b c d : ℂ) :
    blockify (n := 2) (diag4 a b c d) =
      Matrix.fromBlocks (diag2 a b) 0 0 (diag2 c d) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change diag4 a b c d ((finTwoBlockEquiv 2).symm (Sum.inl i)) ((finTwoBlockEquiv 2).symm (Sum.inl j)) =
      diag2 a b i j
    rw [finTwoBlockEquiv_symm_apply_inl, finTwoBlockEquiv_symm_apply_inl]
    fin_cases i <;> fin_cases j <;> try simp [diag2, diag4]
    all_goals
      first
      | rw [finProdFinEquiv_00]
      | rw [finProdFinEquiv_01]
    all_goals simp
  · change diag4 a b c d ((finTwoBlockEquiv 2).symm (Sum.inl i)) ((finTwoBlockEquiv 2).symm (Sum.inr j)) =
      0
    rw [finTwoBlockEquiv_symm_apply_inl, finTwoBlockEquiv_symm_apply_inr]
    fin_cases i <;> fin_cases j <;> simp [diag4]
  · change diag4 a b c d ((finTwoBlockEquiv 2).symm (Sum.inr i)) ((finTwoBlockEquiv 2).symm (Sum.inl j)) =
      0
    rw [finTwoBlockEquiv_symm_apply_inr, finTwoBlockEquiv_symm_apply_inl]
    fin_cases i <;> fin_cases j <;> simp [diag4]
  · change diag4 a b c d ((finTwoBlockEquiv 2).symm (Sum.inr i)) ((finTwoBlockEquiv 2).symm (Sum.inr j)) =
      diag2 c d i j
    rw [finTwoBlockEquiv_symm_apply_inr, finTwoBlockEquiv_symm_apply_inr]
    fin_cases i <;> fin_cases j <;> try simp [diag2, diag4]
    all_goals
      first
      | rw [finProdFinEquiv_10]
      | rw [finProdFinEquiv_11]
    all_goals simp

private lemma repeated_pair_complement {a b e f c d : ℂ}
    (hab : a ≠ b)
    (h : ({a, b, e, f} : Multiset ℂ) = ({c, d, c, d} : Multiset ℂ)) :
    ({e, f} : Multiset ℂ) = ({a, b} : Multiset ℂ) := by
  have ha_mem : a ∈ ({c, d, c, d} : Multiset ℂ) := by
    rw [← h]
    simp
  have hb_mem : b ∈ ({c, d, c, d} : Multiset ℂ) := by
    rw [← h]
    simp
  rcases (by simpa [Multiset.mem_cons, eq_comm, or_left_comm, or_assoc] using ha_mem :
      a = c ∨ a = d) with hac | had
  · have hbd : b = d := by
      rcases (by simpa [hac, Multiset.mem_cons, eq_comm, or_left_comm, or_assoc] using hb_mem :
          b = a ∨ b = d) with hba | hbd
      · exact False.elim (hab hba.symm)
      · exact hbd
    have hpair : ({a, b, e, f} : Multiset ℂ) = ({a, b, a, b} : Multiset ℂ) := by
      rw [h, hac, hbd]
    have hcons : a ::ₘ b ::ₘ ({e, f} : Multiset ℂ) = a ::ₘ b ::ₘ ({a, b} : Multiset ℂ) := by
      simpa using hpair
    exact (Multiset.cons_inj_right b).mp ((Multiset.cons_inj_right a).mp hcons)
  · have hbc : b = c := by
      rcases (by simpa [had, Multiset.mem_cons, eq_comm, or_left_comm, or_assoc] using hb_mem :
          b = c ∨ b = d) with hbc | hbd
      · exact hbc
      · exact False.elim (hab (had.trans hbd.symm))
    have hcons : a ::ₘ b ::ₘ ({e, f} : Multiset ℂ) = a ::ₘ b ::ₘ ({a, b} : Multiset ℂ) := by
      calc
        a ::ₘ b ::ₘ ({e, f} : Multiset ℂ) = ({a, b, e, f} : Multiset ℂ) := rfl
        _ = ({c, d, c, d} : Multiset ℂ) := h
        _ = ({b, a, b, a} : Multiset ℂ) := by rw [← hbc, ← had]
        _ = b ::ₘ a ::ₘ ({b, a} : Multiset ℂ) := rfl
        _ = a ::ₘ b ::ₘ ({b, a} : Multiset ℂ) := by rw [Multiset.cons_swap]
          _ = a ::ₘ b ::ₘ ({a, b} : Multiset ℂ) := by
            congr 2
            simpa using (Multiset.cons_swap b a (0 : Multiset ℂ))
    exact (Multiset.cons_inj_right b).mp ((Multiset.cons_inj_right a).mp hcons)

private lemma swap2_conjTranspose : swap2† = swap2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2]

private lemma swap2_mul_swap2 : swap2 * swap2 = (1 : Square 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2]

private lemma swap2_unitary : swap2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, show star swap2 = swap2 by
    simpa [star_eq_conjTranspose] using swap2_conjTranspose, swap2_mul_swap2]

private lemma swap2_conj_diag4 (a b c d : ℂ) :
    swap2 * diag4 a b c d * swap2† = diag4 a c b d := by
  rw [swap2_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ, swap2, diag4]

private def cnot : Square 4 :=
  Matrix.of ![![1, 0, 0, 0],
              ![0, 1, 0, 0],
              ![0, 0, 0, 1],
              ![0, 0, 1, 0]]

private lemma cnot_conjTranspose : cnot† = cnot := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cnot]

private lemma cnot_mul_cnot : cnot * cnot = (1 : Square 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cnot]

private lemma cnot_unitary : cnot ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, show star cnot = cnot by
    simpa [star_eq_conjTranspose] using cnot_conjTranspose, cnot_mul_cnot]

private lemma cnot_conj_diag4 (a b c d : ℂ) :
    cnot * diag4 a b c d * cnot† = diag4 a b d c := by
  rw [cnot_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ, cnot, diag4]

/-- **Lemma 3.3** (Eigenvalue condition for controlled gate). -/
lemma section3_lemma_3_3 (u₀ u₁ : ℂ) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) :
    (∃ (P : Square 2), P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      ∃ (U : Square 4), U ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
        ∃ (c d : ℂ),
          (1 : Square 2) ⊗ₖ P * controlledGate (diag2 u₀ u₁) =
          U * diag4 c d c d * U†)
    ↔ u₀ = u₁ ∨ u₀ * u₁ = 1 := by
  constructor
  · intro h
    rcases h with ⟨P, hP, U, hU, c, d, hEq⟩
    let PD : Square 2 := P * diag2 u₀ u₁
    have hD : diag2 u₀ u₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
      diag2_unitary u₀ u₁ hu₀ hu₁
    have hPD : PD ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
      exact Submonoid.mul_mem _ hP hD
    rcases unitary_diag2_exists P hP with ⟨a, b, UP, ha, hb, hUP, hPdiag⟩
    rcases unitary_diag2_exists PD hPD with ⟨e, f, UQ, he, hf, hUQ, hPDdiag⟩
    let W : Square 4 := unblockify (n := 2) (Matrix.fromBlocks UP 0 0 UQ)
    have hW : W ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
      apply (blockify_mem_unitaryGroup_iff (n := 2) (U := W)).1
      simpa [W] using fromBlocks_diagonal_unitary UP UQ hUP hUQ
    have hWblock : blockify (n := 2) W = Matrix.fromBlocks UP 0 0 UQ := by
      simp [W]
    have hBlock :
        (1 : Square 2) ⊗ₖ P * controlledGate (diag2 u₀ u₁) = W * diag4 a b e f * W† := by
      apply (blockify_injective (n := 2))
      calc
        blockify ((1 : Square 2) ⊗ₖ P * controlledGate (diag2 u₀ u₁))
            = Matrix.fromBlocks P 0 0 PD := by
              rw [one_kron_mul_controlledGate_diag2]
              dsimp [PD]
              rw [blockify_add, blockify_proj0_kron, blockify_proj1_kron]
              ext i j
              rcases i with i | i <;> rcases j with j | j <;> simp
        _ = Matrix.fromBlocks (UP * diag2 a b * UP†) 0 0 (UQ * diag2 e f * UQ†) := by
              rw [hPdiag, hPDdiag]
        _ = Matrix.fromBlocks UP 0 0 UQ * blockify (diag4 a b e f) *
              (Matrix.fromBlocks UP 0 0 UQ)† := by
              rw [blockify_diag4, Matrix.fromBlocks_conjTranspose,
                Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
              ext i j
              rcases i with i | i <;> rcases j with j | j <;>
                fin_cases i <;> fin_cases j <;> simp [mul_assoc]
        _ = blockify (W * diag4 a b e f * W†) := by
              rw [blockify_mul, blockify_mul, blockify_conjTranspose,
                hWblock, blockify_diag4]
    have hcharLeft :
        ((1 : Square 2) ⊗ₖ P * controlledGate (diag2 u₀ u₁)).charpoly = (diag4 a b e f).charpoly := by
      rw [hBlock]
      exact charpoly_unitary_conj W _ hW
    have hcharRight :
        ((1 : Square 2) ⊗ₖ P * controlledGate (diag2 u₀ u₁)).charpoly = (diag4 c d c d).charpoly := by
      rw [hEq]
      exact charpoly_unitary_conj U _ hU
    have hroots : ({a, b, e, f} : Multiset ℂ) = ({c, d, c, d} : Multiset ℂ) := by
      rw [← roots_charpoly_diag4 a b e f, ← roots_charpoly_diag4 c d c d, ← hcharLeft, hcharRight]
    by_cases hab : a = b
    · have hPscalar : P = a • (1 : Square 2) := by
        calc
          P = UP * diag2 a b * UP† := hPdiag
          _ = UP * diag2 a a * UP† := by rw [hab]
          _ = UP * (a • (1 : Square 2)) * UP† := by rw [diag2_same_eq_smul_one]
          _ = a • (UP * UP†) := by simp
          _ = a • (1 : Square 2) := by
            have hUU : UP * UP† = 1 := by
              simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff] using hUP
            simp [hUU]
      have hMscalar :
          (1 : Square 2) ⊗ₖ P * controlledGate (diag2 u₀ u₁) = a • diag4 1 1 u₀ u₁ := by
        calc
          (1 : Square 2) ⊗ₖ P * controlledGate (diag2 u₀ u₁)
              = proj0 ⊗ₖ P + proj1 ⊗ₖ (P * diag2 u₀ u₁) := by
                  rw [one_kron_mul_controlledGate_diag2]
          _ = proj0 ⊗ₖ (a • (1 : Square 2)) + proj1 ⊗ₖ (a • diag2 u₀ u₁) := by
            simp [hPscalar]
          _ = a • (proj0 ⊗ₖ (1 : Square 2) + proj1 ⊗ₖ diag2 u₀ u₁) := by
                rw [kron_smul_right, kron_smul_right, smul_add]
          _ = a • diag4 1 1 u₀ u₁ := by
            change a • controlledGate (diag2 u₀ u₁) = a • diag4 1 1 u₀ u₁
            rw [controlledGate_diag2_eq]
      have hOneKronP : ((1 : Square 2) ⊗ₖ P) ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
        kron_unitary_two (1 : Square 2) P (Submonoid.one_mem _) hP
      have hCtrl : controlledGate (diag2 u₀ u₁) ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
        rw [controlledGate_diag2_eq]
        exact diag4_unitary 1 1 u₀ u₁ (by simp) (by simp) hu₀ hu₁
      have hM : ((1 : Square 2) ⊗ₖ P * controlledGate (diag2 u₀ u₁)) ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
        exact Submonoid.mul_mem _ hOneKronP hCtrl
      have hRep : diag4 c d c d ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
        have hconj : U† * (((1 : Square 2) ⊗ₖ P) * controlledGate (diag2 u₀ u₁)) * U = diag4 c d c d := by
          calc
            U† * (((1 : Square 2) ⊗ₖ P) * controlledGate (diag2 u₀ u₁)) * U
                = U† * (U * diag4 c d c d * U†) * U := by rw [hEq]
            _ = diag4 c d c d := by
                have hUleft : U† * U = 1 := by
                  simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'] using hU
                have hUright : U * U† = 1 := by
                  simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff] using hU
                calc
                  U† * (U * diag4 c d c d * U†) * U
                      = (U† * U) * diag4 c d c d * (U† * U) := by simp [mul_assoc]
                  _ = diag4 c d c d := by simp [hUleft]
        simpa [hconj] using unitary_conj_mem_unitaryGroup hM hU
      have ⟨hc, hd⟩ := diag4_repeat_norms_of_mem_unitaryGroup hRep
      have ha0 : a ≠ 0 := by
        intro ha_zero
        have ha' := ha
        simp [ha_zero] at ha'
      let q₀ : ℂ := a⁻¹ * c
      let q₁ : ℂ := a⁻¹ * d
      have hq₀ : ‖q₀‖ = 1 := by
        dsimp [q₀]
        calc
          ‖a⁻¹ * c‖ = ‖a⁻¹‖ * ‖c‖ := norm_mul _ _
          _ = ‖a‖⁻¹ * ‖c‖ := by simp
          _ = 1 := by simp [ha, hc]
      have hq₁ : ‖q₁‖ = 1 := by
        dsimp [q₁]
        calc
          ‖a⁻¹ * d‖ = ‖a⁻¹‖ * ‖d‖ := norm_mul _ _
          _ = ‖a‖⁻¹ * ‖d‖ := by simp
          _ = 1 := by simp [ha, hd]
      have hscaled : diag4 1 1 u₀ u₁ = U * diag4 q₀ q₁ q₀ q₁ * U† := by
        have hEqScalar : a • diag4 1 1 u₀ u₁ = U * diag4 c d c d * U† := by
          calc
            a • diag4 1 1 u₀ u₁ = (1 : Square 2) ⊗ₖ P * controlledGate (diag2 u₀ u₁) := hMscalar.symm
            _ = U * diag4 c d c d * U† := hEq
        have hEq' := congrArg (fun M => a⁻¹ • M) hEqScalar
        calc
          diag4 1 1 u₀ u₁ = a⁻¹ • (a • diag4 1 1 u₀ u₁) := by
            simp [smul_smul, ha0]
          _ = a⁻¹ • (U * diag4 c d c d * U†) := hEq'
          _ = U * (a⁻¹ • diag4 c d c d) * U† := by
            simp [mul_assoc]
          _ = U * diag4 q₀ q₁ q₀ q₁ * U† := by
            congr 2
            ext i j
            fin_cases i <;> fin_cases j <;> simp [diag4, q₀, q₁]
      have hQconj : U† * diag4 1 1 u₀ u₁ * U = diag4 q₀ q₁ q₀ q₁ := by
        calc
          U† * diag4 1 1 u₀ u₁ * U = U† * (U * diag4 q₀ q₁ q₀ q₁ * U†) * U := by rw [hscaled]
          _ = diag4 q₀ q₁ q₀ q₁ := by
              have hUleft : U† * U = 1 := by
                simpa [star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'] using hU
              calc
                U† * (U * diag4 q₀ q₁ q₀ q₁ * U†) * U
                    = (U† * U) * diag4 q₀ q₁ q₀ q₁ * (U† * U) := by simp [mul_assoc]
                _ = diag4 q₀ q₁ q₀ q₁ := by simp [hUleft]
      have hQeq : (1 : Square 2) ⊗ₖ diag2 q₀ q₁ = U† * diag4 1 1 u₀ u₁ * U := by
        rw [one_kron_diag2]
        exact hQconj.symm
      exact (section3_lemma_3_2 u₀ u₁ hu₀ hu₁).mp <| by
        refine ⟨1, diag2 q₀ q₁, U†, ?_, ?_, ?_, ?_⟩
        · exact Submonoid.one_mem _
        · exact diag2_unitary q₀ q₁ hq₀ hq₁
        · exact conjTranspose_mem_unitaryGroup hU
        · simpa using hQeq
    · have hEF : ({e, f} : Multiset ℂ) = ({a, b} : Multiset ℂ) :=
        repeated_pair_complement hab hroots
      have hprod : e * f = a * b := by
        calc
          e * f = ({e, f} : Multiset ℂ).prod := by simp
          _ = ({a, b} : Multiset ℂ).prod := by rw [hEF]
          _ = a * b := by simp
      have hdetP : P.det = a * b := det_of_unitary_diag2_decomp hUP hPdiag
      have hdetPD : PD.det = e * f := det_of_unitary_diag2_decomp hUQ hPDdiag
      have hdetEq : PD.det = P.det := by rw [hdetPD, hprod, hdetP]
      have hdetCalc : PD.det = P.det * (u₀ * u₁) := by
        dsimp [PD]
        rw [Matrix.det_mul, hdetP, det_diag2]
      have hdetNonzero : P.det ≠ 0 := by
        rw [hdetP]
        apply mul_ne_zero
        · intro ha_zero
          have ha' := ha
          simp [ha_zero] at ha'
        · intro hb_zero
          have hb' := hb
          simp [hb_zero] at hb'
      have hcancel : P.det * 1 = P.det * (u₀ * u₁) := by
        calc
          P.det * 1 = P.det := by simp
          _ = PD.det := hdetEq.symm
          _ = P.det * (u₀ * u₁) := hdetCalc
      exact Or.inr ((mul_left_cancel₀ hdetNonzero hcancel).symm)
  · intro h
    rcases h with rfl | hmul
    · refine ⟨1, Submonoid.one_mem _, swap2, swap2_unitary, 1, u₀, ?_⟩
      calc
        (1 : Square 2) ⊗ₖ (1 : Square 2) * controlledGate (diag2 u₀ u₀)
            = controlledGate (diag2 u₀ u₀) := by simp [TwoControl.one_kron_one 2 2]
        _ = diag4 1 1 u₀ u₀ := controlledGate_diag2_eq u₀ u₀
        _ = swap2 * diag4 1 u₀ 1 u₀ * swap2† := by
            symm
            simpa using swap2_conj_diag4 1 u₀ 1 u₀
    · refine ⟨diag2 1 u₀, diag2_unitary 1 u₀ (by simp) hu₀, cnot, cnot_unitary, 1, u₀, ?_⟩
      calc
        (1 : Square 2) ⊗ₖ diag2 1 u₀ * controlledGate (diag2 u₀ u₁) = diag4 1 u₀ u₀ 1 := by
          ext i j
          obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective i
          obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (@finProdFinEquiv 2 2).surjective j
          rw [one_kron_mul_controlledGate_diag2]
          fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
            try simp [TwoControl.kron, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
              proj0, proj1, ketbra, ket0, ket1, diag2, diag4, hmul]
          all_goals
            first
            | rw [finProdFinEquiv_00]
            | rw [finProdFinEquiv_01]
            | rw [finProdFinEquiv_10]
            | rw [finProdFinEquiv_11]
          all_goals simp
        _ = cnot * diag4 1 u₀ 1 u₀ * cnot† := by
              symm
              simpa using cnot_conj_diag4 1 u₀ 1 u₀

end TwoControl

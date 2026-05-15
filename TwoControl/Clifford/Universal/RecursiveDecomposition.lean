import TwoControl.Clifford.Universal.GateSets
import TwoControl.Clifford.Universal.CosineSineStep
import TwoControl.DiagonalizationHelpers
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace TwoControl
namespace Clifford
namespace Universal

/-!
Statements for the recursive Lemma 1 track in `doc.tex`.

This file now serves two purposes.

1. It keeps the already-formalized two-qubit cosine-sine base case alive.
2. It records the honest statement-level scaffold for the recursive proof of
   the paper's Lemma 1, ending at `Synthesizes (EasyGate n) U`.

The key correction compared with the earlier axiom wrappers is that the
demultiplexing and controlled-`R_z` steps are stated with their real input
shapes exposed, rather than hidden behind opaque predicates.
-/

private theorem two_mul_pow_eq_pow_succ (m : ℕ) :
    2 * 2 ^ m = 2 ^ (m + 1) := by
  simp [pow_succ, mul_comm]

private theorem four_mul_pow_eq_pow_add_two (m : ℕ) :
    4 * 2 ^ m = 2 ^ (m + 2) := by
  have h4 : 4 = 2 * 2 := by decide
  rw [h4, Nat.mul_assoc, two_mul_pow_eq_pow_succ]
  simpa [Nat.add_assoc] using two_mul_pow_eq_pow_succ (m + 1)

private theorem blockify_two_by_two_kron_one {n : ℕ} (A : Square 2) :
    blockify (n := n) (A ⊗ₖ (1 : Square n)) =
      Matrix.fromBlocks
        (A 0 0 • (1 : Square n))
        (A 0 1 • (1 : Square n))
        (A 1 0 • (1 : Square n))
        (A 1 1 • (1 : Square n)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simpa [blockify] using (TwoControl.kron_apply (A := A) (B := (1 : Square n)) 0 i 0 j)
  · simpa [blockify] using (TwoControl.kron_apply (A := A) (B := (1 : Square n)) 0 i 1 j)
  · simpa [blockify] using (TwoControl.kron_apply (A := A) (B := (1 : Square n)) 1 i 0 j)
  · simpa [blockify] using (TwoControl.kron_apply (A := A) (B := (1 : Square n)) 1 i 1 j)

private theorem blockify_top_conjugation_of_controlledRzCore (m : ℕ)
    (α : Fin (2 ^ m) → ℝ) (A B : Square 2) :
    blockify (n := 2 ^ m)
      ((A ⊗ₖ (1 : Square (2 ^ m))) *
        unblockify
          (Matrix.fromBlocks
            (Matrix.diagonal fun i => Complex.exp (-Complex.I * (α i / 2)))
            0 0
            (Matrix.diagonal fun i => Complex.exp (Complex.I * (α i / 2)))) *
        (B ⊗ₖ (1 : Square (2 ^ m)))) =
      Matrix.fromBlocks
        (Matrix.diagonal fun i => (A * rz (α i) * B) 0 0)
        (Matrix.diagonal fun i => (A * rz (α i) * B) 0 1)
        (Matrix.diagonal fun i => (A * rz (α i) * B) 1 0)
        (Matrix.diagonal fun i => (A * rz (α i) * B) 1 1) := by
  rw [blockify_mul, blockify_mul, blockify_two_by_two_kron_one, blockify_unblockify,
    blockify_two_by_two_kron_one]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  refine Matrix.fromBlocks_inj.2 ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    by_cases hij : i = j
    · subst j
      simp [rz, diag2, Matrix.mul_apply, Fin.sum_univ_two]
      ring_nf
    · simp [hij]
  · ext i j
    by_cases hij : i = j
    · subst j
      simp [rz, diag2, Matrix.mul_apply, Fin.sum_univ_two]
      ring_nf
    · simp [hij]
  · ext i j
    by_cases hij : i = j
    · subst j
      simp [rz, diag2, Matrix.mul_apply, Fin.sum_univ_two]
      ring_nf
    · simp [hij]
  · ext i j
    by_cases hij : i = j
    · subst j
      simp [rz, diag2, Matrix.mul_apply, Fin.sum_univ_two]
      ring_nf
    · simp [hij]

@[simp] private theorem finProdFinEquiv_41 (i : Fin 4) :
    (@finProdFinEquiv 4 1 (i, 0) : Fin 4) = i := by
  fin_cases i <;> rfl

@[simp] private theorem finProdFinEquiv_14 (i : Fin 4) :
    (@finProdFinEquiv 1 4 (0, i) : Fin 4) = i := by
  fin_cases i <;> rfl

private theorem kron_right_one_four (U : Square 4) :
    U ⊗ₖ (1 : Square 1) = U := by
  ext i j
  let i' : Fin 4 := ((@finProdFinEquiv 4 1).symm i).1
  let j' : Fin 4 := ((@finProdFinEquiv 4 1).symm j).1
  have hi0 : ((@finProdFinEquiv 4 1).symm i).2 = 0 := Subsingleton.elim _ _
  have hj0 : ((@finProdFinEquiv 4 1).symm j).2 = 0 := Subsingleton.elim _ _
  have hi : (@finProdFinEquiv 4 1 (i', 0) : Fin 4) = i := by
    dsimp [i']
    rw [← hi0]
    exact (@finProdFinEquiv 4 1).apply_symm_apply i
  have hj : (@finProdFinEquiv 4 1 (j', 0) : Fin 4) = j := by
    dsimp [j']
    rw [← hj0]
    exact (@finProdFinEquiv 4 1).apply_symm_apply j
  have hi' : i' = i := by
    fin_cases i <;> rfl
  have hj' : j' = j := by
    fin_cases j <;> rfl
  convert (TwoControl.kron_apply (A := U) (B := (1 : Square 1)) i' 0 j' 0) using 1
  · simp [hi, hj]
  · simp [hi', hj']

private theorem one_kron_four (U : Square 4) :
    (1 : Square 1) ⊗ₖ U = U := by
  ext i j
  convert (TwoControl.kron_apply (A := (1 : Square 1)) (B := U) 0 i 0 j) using 1
  simp

private theorem two_kron_one (U : Square 2) :
    U ⊗ₖ (1 : Square 1) = U := by
  ext i j
  let i' : Fin 2 := ((@finProdFinEquiv 2 1).symm i).1
  let j' : Fin 2 := ((@finProdFinEquiv 2 1).symm j).1
  have hi0 : ((@finProdFinEquiv 2 1).symm i).2 = 0 := Subsingleton.elim _ _
  have hj0 : ((@finProdFinEquiv 2 1).symm j).2 = 0 := Subsingleton.elim _ _
  have hi : (@finProdFinEquiv 2 1 (i', 0) : Fin 2) = i := by
    dsimp [i']
    rw [← hi0]
    exact (@finProdFinEquiv 2 1).apply_symm_apply i
  have hj : (@finProdFinEquiv 2 1 (j', 0) : Fin 2) = j := by
    dsimp [j']
    rw [← hj0]
    exact (@finProdFinEquiv 2 1).apply_symm_apply j
  have hi' : i' = i := by
    fin_cases i <;> rfl
  have hj' : j' = j := by
    fin_cases j <;> rfl
  convert (TwoControl.kron_apply (A := U) (B := (1 : Square 1)) i' 0 j' 0) using 1
  · simp [hi, hj]
  · simp [hi', hj']

/-- First-qubit block-diagonal assembly `|0><0| ⊗ U₀ + |1><1| ⊗ U₁`. -/
noncomputable def firstQubitBlockDiag (m : ℕ) (U₀ U₁ : Square (2 ^ m)) :
    Square (2 ^ (m + 1)) :=
  castSquare (two_mul_pow_eq_pow_succ m)
    (unblockify (Matrix.fromBlocks U₀ 0 0 U₁))

/-- Lift an `m`-qubit gate to the lower `m` wires of an `(m+1)`-qubit system. -/
noncomputable def liftLowerUnitary (m : ℕ) (U : Square (2 ^ m)) :
    Square (2 ^ (m + 1)) :=
  firstQubitBlockDiag m U U

/-- Lift a one-qubit gate to the first wire of an `(m+1)`-qubit system. -/
noncomputable def liftTopOneQubit (m : ℕ) (U : Square 2) : Square (2 ^ (m + 1)) :=
  castSquare (two_mul_pow_eq_pow_succ m) (U ⊗ₖ (1 : Square (2 ^ m)))

private noncomputable def topTwoPlacement (m : ℕ) : TwoQubitPlacement (m + 2) :=
  { first := 0
    second := 1
    distinct := by simp
    left := 1
    right := 2 ^ m
    dimension_eq := by
      simpa using four_mul_pow_eq_pow_add_two m
    permutation := Equiv.refl _ }

/-- Embed a two-qubit gate on the top two wires, leaving the remaining `m`
qubits untouched. -/
noncomputable def topTwoUnitary (m : ℕ) (U : Square 4) : Square (2 ^ (m + 2)) :=
  (topTwoPlacement m).embed U

/-- Insert an idle control wire after the target wire of an `(m+1)`-qubit gate. -/
noncomputable def liftMiddleUnitary (m : ℕ) (U : Square (2 ^ (m + 1))) :
    Square (2 ^ (m + 2)) :=
  topTwoUnitary m swap2 * liftLowerUnitary (m + 1) U * topTwoUnitary m swap2

/-- Uniformly controlled `R_y` family on the first wire with `m` control wires. -/
noncomputable def controlledRyFamily (m : ℕ) (θ : Fin (2 ^ m) → ℝ) :
    Square (2 ^ (m + 1)) :=
  castSquare (two_mul_pow_eq_pow_succ m)
    (unblockify
      (Matrix.fromBlocks
        (Matrix.diagonal fun i => ((Real.cos (θ i / 2)) : ℂ))
        (- Matrix.diagonal fun i => ((Real.sin (θ i / 2)) : ℂ))
        (Matrix.diagonal fun i => ((Real.sin (θ i / 2)) : ℂ))
        (Matrix.diagonal fun i => ((Real.cos (θ i / 2)) : ℂ))))

/-- Uniformly controlled `R_z` family on the first wire with `m` control wires. -/
noncomputable def controlledRzFamily (m : ℕ) (α : Fin (2 ^ m) → ℝ) :
    Square (2 ^ (m + 1)) :=
  firstQubitBlockDiag m
    (Matrix.diagonal fun i => Complex.exp (-Complex.I * (α i / 2)))
    (Matrix.diagonal fun i => Complex.exp (Complex.I * (α i / 2)))

/-- Concrete marker for the general `n`-qubit cosine-sine decomposition step.

For `n = m + 1`, the outer factors are block-diagonal on the first qubit and
the middle factor is a uniformly controlled `R_y` family on the remaining
`m` qubits, matching the paper statement. -/
noncomputable def HasGeneralCosineSineStep : (n : ℕ) →
    Square (2 ^ n) → Square (2 ^ n) → Square (2 ^ n) → Square (2 ^ n) → Prop
  | 0, _, _, _, _ => False
  | m + 1, _, P, R, Q =>
      ∃ P₀ P₁ Q₀ Q₁ : Square (2 ^ m),
      ∃ θ : Fin (2 ^ m) → ℝ,
        P = castSquare (two_mul_pow_eq_pow_succ m)
              (unblockify (Matrix.fromBlocks P₀ 0 0 P₁)) ∧
        R = castSquare (two_mul_pow_eq_pow_succ m)
              (unblockify
                (Matrix.fromBlocks
                  (Matrix.diagonal fun i => ((Real.cos (θ i / 2)) : ℂ))
                  (- Matrix.diagonal fun i => ((Real.sin (θ i / 2)) : ℂ))
                  (Matrix.diagonal fun i => ((Real.sin (θ i / 2)) : ℂ))
                  (Matrix.diagonal fun i => ((Real.cos (θ i / 2)) : ℂ)))) ∧
        Q = castSquare (two_mul_pow_eq_pow_succ m)
              (unblockify (Matrix.fromBlocks Q₀ 0 0 Q₁))

/-- External Paige-Wei cosine-sine decomposition interface for arbitrary
`n`-qubit unitaries. -/
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
      simpa [blockify] using Matrix.submatrix_one_equiv (finTwoBlockEquiv n)

private theorem middle_factor_mem_unitaryGroup {N : ℕ} {U P R Q : Square N}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hP : P ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hEq : U = P * R * Q) :
    R ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hPdag : P† ∈ Matrix.unitaryGroup (Fin N) ℂ := conjTranspose_mem_unitaryGroup hP
  have hQdag : Q† ∈ Matrix.unitaryGroup (Fin N) ℂ := conjTranspose_mem_unitaryGroup hQ
  have hPleft : P† * P = (1 : Square N) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hP)
  have hQright : Q * Q† = (1 : Square N) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hQ)
  have hR : R = P† * U * Q† := by
    calc
      R = (1 : Square N) * R * (1 : Square N) := by simp
      _ = (P† * P) * R * (Q * Q†) := by rw [hPleft, hQright]
      _ = P† * U * Q† := by rw [hEq]; simp [mul_assoc]
  rw [hR]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hPdag hU) hQdag

set_option maxHeartbeats 1000000 in
theorem general_cosine_sine_step_exists {n : ℕ} (hn : 1 ≤ n)
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    ∃ P R Q : Square (2 ^ n),
      P ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
      R ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
      Q ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
      HasGeneralCosineSineStep n U P R Q ∧
    U = P * R * Q := by
  rcases n with _ | m
  · cases hn
  · let N : ℕ := 2 ^ m
    let U0 : Square (2 * N) := castSquare (two_mul_pow_eq_pow_succ m).symm U
    have hU0 : U0 ∈ Matrix.unitaryGroup (Fin (2 * N)) ℂ := by
      dsimp [U0, N]
      exact castSquare_mem_unitaryGroup (two_mul_pow_eq_pow_succ m).symm hU
    let Ub : BlockMatrix N := blockify (n := N) U0
    let A : Square N := Ub.toBlocks₁₁
    let B : Square N := Ub.toBlocks₁₂
    let C : Square N := Ub.toBlocks₂₁
    let D : Square N := Ub.toBlocks₂₂
    have hUb : Ub ∈ Matrix.unitaryGroup (Fin N ⊕ Fin N) ℂ := by
      exact (blockify_mem_unitaryGroup_iff (n := N) U0).2 hU0
    have hUbBlocks : Matrix.fromBlocks A B C D = Ub := by
      simpa [Ub, A, B, C, D] using Matrix.fromBlocks_toBlocks Ub
    have hUbLeft : Ub† * Ub = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hUb)
    have hUbRight : Ub * Ub† = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hUb)
    have hBlocksLeft :
        Matrix.fromBlocks
            (A† * A + C† * C)
            (A† * B + C† * D)
            (B† * A + D† * C)
            (B† * B + D† * D) =
          Matrix.fromBlocks (1 : Square N) 0 0 (1 : Square N) := by
      calc
        Matrix.fromBlocks
            (A† * A + C† * C)
            (A† * B + C† * D)
            (B† * A + D† * C)
            (B† * B + D† * D)
            = (Matrix.fromBlocks A B C D)† * Matrix.fromBlocks A B C D := by
                rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
        _ = Ub† * Ub := by rw [hUbBlocks]
        _ = 1 := hUbLeft
        _ = Matrix.fromBlocks (1 : Square N) 0 0 (1 : Square N) := by
          exact BlockHelpers.block_one_eq N
    have hBlocksRight :
        Matrix.fromBlocks
            (A * A† + B * B†)
            (A * C† + B * D†)
            (C * A† + D * B†)
            (C * C† + D * D†) =
          Matrix.fromBlocks (1 : Square N) 0 0 (1 : Square N) := by
      calc
        Matrix.fromBlocks
            (A * A† + B * B†)
            (A * C† + B * D†)
            (C * A† + D * B†)
            (C * C† + D * D†)
            = Matrix.fromBlocks A B C D * (Matrix.fromBlocks A B C D)† := by
                rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
        _ = Ub * Ub† := by rw [hUbBlocks]
        _ = 1 := hUbRight
        _ = Matrix.fromBlocks (1 : Square N) 0 0 (1 : Square N) := by
          exact BlockHelpers.block_one_eq N
    rcases Matrix.fromBlocks_inj.mp hBlocksLeft with ⟨hAA_CC, hAB_CD, _, _⟩
    rcases Matrix.fromBlocks_inj.mp hBlocksRight with ⟨hAA_BB, hAC_BD, _, hCC_DD⟩
    let H : Square N := A† * A
    have hHherm : H.IsHermitian := by
      dsimp [H]
      exact Matrix.isHermitian_conjTranspose_mul_self A
    let eigVals : Fin N → ℝ := hHherm.eigenvalues
    let Ueig : unitary (Square N) := hHherm.eigenvectorUnitary
    have hUeig : (Ueig : Square N) ∈ Matrix.unitaryGroup (Fin N) ℂ := by
      dsimp [Ueig]
      exact ⟨Unitary.coe_star_mul_self _, Unitary.coe_mul_star_self _⟩
    let Q0u : unitary (Square N) := star Ueig
    let Q0 : Square N := Q0u
    have hQ0 : Q0 ∈ Matrix.unitaryGroup (Fin N) ℂ := by
      dsimp [Q0, Q0u, Ueig]
      simpa [Matrix.star_eq_conjTranspose] using conjTranspose_mem_unitaryGroup hUeig
    have hQ0left : Q0† * Q0 = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hQ0)
    have hQ0right : Q0 * Q0† = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hQ0)
    let Delta : Square N := Matrix.diagonal fun i => (eigVals i : ℂ)
    have hHdiag : Q0 * H * Q0† = Delta := by
      dsimp [Q0, Q0u, Ueig, H, Delta, eigVals]
      simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
        hHherm.conjStarAlgAut_star_eigenvectorUnitary
    let A0 : Square N := A * Q0†
    let C0 : Square N := C * Q0†
    have hA0Gram : A0† * A0 = Delta := by
      calc
        A0† * A0 = Q0 * H * Q0† := by
          dsimp [A0, H]
          simp [mul_assoc]
        _ = Delta := hHdiag
    have hCC : C† * C = 1 - H := by
      rw [eq_sub_iff_add_eq]
      simpa [H, add_assoc, add_comm, add_left_comm] using hAA_CC
    have hC0Gram : C0† * C0 = 1 - Delta := by
      calc
        C0† * C0 = Q0 * (C† * C) * Q0† := by
          dsimp [C0]
          simp [mul_assoc]
        _ = Q0 * (1 - H) * Q0† := by rw [hCC]
        _ = Q0 * Q0† - Q0 * H * Q0† := by
              simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc]
        _ = 1 - Delta := by simp [hQ0right, hHdiag]
    have hEig_nonneg : ∀ i, 0 ≤ eigVals i := by
      intro i
      have hdiag : (((‖WithLp.toLp 2 (A0.mulVec (Pi.single i 1))‖ ^ 2 : ℝ)) : ℂ) = (eigVals i : ℂ) := by
        have hinner : inner ℂ (WithLp.toLp 2 (A0.mulVec (Pi.single i 1)))
            (WithLp.toLp 2 (A0.mulVec (Pi.single i 1))) = (A0† * A0) i i := by
          simpa [Matrix.mulVec_single_one] using inner_matrix_col_col A0 A0 i i
        calc
          (((‖WithLp.toLp 2 (A0.mulVec (Pi.single i 1))‖ ^ 2 : ℝ)) : ℂ) = (A0† * A0) i i := by
            simpa [inner_self_eq_norm_sq_to_K] using hinner
          _ = (eigVals i : ℂ) := by simpa [hA0Gram, Delta]
      have hreal : ‖WithLp.toLp 2 (A0.mulVec (Pi.single i 1))‖ ^ 2 = eigVals i := by
        exact_mod_cast hdiag
      nlinarith [sq_nonneg ‖WithLp.toLp 2 (A0.mulVec (Pi.single i 1))‖]
    have hOneSub_nonneg : ∀ i, 0 ≤ 1 - eigVals i := by
      intro i
      have hdiag : (((‖WithLp.toLp 2 (C0.mulVec (Pi.single i 1))‖ ^ 2 : ℝ)) : ℂ) = ((1 - eigVals i : ℝ) : ℂ) := by
        have hinner : inner ℂ (WithLp.toLp 2 (C0.mulVec (Pi.single i 1)))
            (WithLp.toLp 2 (C0.mulVec (Pi.single i 1))) = (C0† * C0) i i := by
          simpa [Matrix.mulVec_single_one] using inner_matrix_col_col C0 C0 i i
        calc
          (((‖WithLp.toLp 2 (C0.mulVec (Pi.single i 1))‖ ^ 2 : ℝ)) : ℂ) = (C0† * C0) i i := by
            simpa [inner_self_eq_norm_sq_to_K] using hinner
          _ = ((1 - eigVals i : ℝ) : ℂ) := by simpa [hC0Gram, Delta]
      have hreal : ‖WithLp.toLp 2 (C0.mulVec (Pi.single i 1))‖ ^ 2 = 1 - eigVals i := by
        exact_mod_cast hdiag
      nlinarith [sq_nonneg ‖WithLp.toLp 2 (C0.mulVec (Pi.single i 1))‖]
    have hC0GramDiag :
        C0† * C0 = Matrix.diagonal (fun i => ((1 - eigVals i : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hC0Gram, Delta]
      · simp [hC0Gram, Delta, hij]
    let c : Fin N → ℝ := fun i => Real.sqrt (eigVals i)
    let s : Fin N → ℝ := fun i => Real.sqrt (1 - eigVals i)
    let Cdiag : Square N := Matrix.diagonal fun i => (c i : ℂ)
    let Sdiag : Square N := Matrix.diagonal fun i => (s i : ℂ)
    let NegSdiag : Square N := Matrix.diagonal fun i => (-(s i : ℂ))
    have hCdiagStar : Cdiag† = Cdiag := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Cdiag]
      · have hji : ¬ j = i := by simpa [eq_comm] using hij
        simp [Cdiag, hij, hji]
    have hSdiagStar : Sdiag† = Sdiag := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Sdiag]
      · have hji : ¬ j = i := by simpa [eq_comm] using hij
        simp [Sdiag, hij, hji]
    rcases TwoControl.exists_unitary_mul_realDiagonal_of_gram_eq_diagonal A0 eigVals hEig_nonneg hA0Gram with
      ⟨P0, hP0, hA0eq0⟩
    rcases TwoControl.exists_unitary_mul_realDiagonal_of_gram_eq_diagonal C0
        (fun i => 1 - eigVals i) hOneSub_nonneg hC0GramDiag with ⟨P1, hP1, hC0eq0⟩
    have hA0eq : A0 = P0 * Cdiag := by
      simpa [c, Cdiag] using hA0eq0
    have hC0eq : C0 = P1 * Sdiag := by
      simpa [s, Sdiag] using hC0eq0
    have hP0leftU : P0† * P0 = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hP0)
    have hP0rightU : P0 * P0† = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hP0)
    have hP1leftU : P1† * P1 = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hP1)
    have hP1rightU : P1 * P1† = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hP1)
    have hc_nonneg : ∀ i, 0 ≤ c i := by
      intro i
      exact Real.sqrt_nonneg _
    have hs_nonneg : ∀ i, 0 ≤ s i := by
      intro i
      exact Real.sqrt_nonneg _
    have hcs : ∀ i, c i ^ 2 + s i ^ 2 = 1 := by
      intro i
      have hc_sq : c i ^ 2 = eigVals i := by
        simp [c, Real.sq_sqrt, hEig_nonneg i]
      have hs_sq : s i ^ 2 = 1 - eigVals i := by
        simp [s, Real.sq_sqrt, hOneSub_nonneg i]
      nlinarith [hc_sq, hs_sq]
    have hCSsum : Cdiag * Cdiag + Sdiag * Sdiag = (1 : Square N) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        have hcs_complex : (((c i ^ 2 + s i ^ 2 : ℝ)) : ℂ) = 1 := by
          exact_mod_cast hcs i
        simpa [Cdiag, Sdiag, pow_two] using hcs_complex
      · simp [Cdiag, Sdiag, hij]
    let B1 : Square N := P0† * B
    let D1 : Square N := P1† * D
    have hAB0 : A0† * B + C0† * D = 0 := by
      calc
        A0† * B + C0† * D = Q0 * (A† * B) + Q0 * (C† * D) := by
          dsimp [A0, C0]
          simp [mul_assoc]
        _ = Q0 * (A† * B + C† * D) := by rw [Matrix.mul_add]
        _ = 0 := by rw [hAB_CD]; simp
    have hAC0 : A0 * C0† + B * D† = 0 := by
      calc
        A0 * C0† + B * D† = A * (Q0† * Q0) * C† + B * D† := by
          dsimp [A0, C0]
          simp [mul_assoc]
        _ = A * C† + B * D† := by simp [hQ0left, mul_assoc]
        _ = 0 := hAC_BD
    have hAA0_BB : A0 * A0† + B * B† = 1 := by
      calc
        A0 * A0† + B * B† = A * (Q0† * Q0) * A† + B * B† := by
          dsimp [A0]
          simp [mul_assoc]
        _ = A * A† + B * B† := by simp [hQ0left, mul_assoc]
        _ = 1 := hAA_BB
    have hCC0_DD : C0 * C0† + D * D† = 1 := by
      calc
        C0 * C0† + D * D† = C * (Q0† * Q0) * C† + D * D† := by
          dsimp [C0]
          simp [mul_assoc]
        _ = C * C† + D * D† := by simp [hQ0left, mul_assoc]
        _ = 1 := hCC_DD
    have hLeftRel : Cdiag * B1 + Sdiag * D1 = 0 := by
      calc
        Cdiag * B1 + Sdiag * D1 = (P0 * Cdiag)† * B + (P1 * Sdiag)† * D := by
          simpa [B1, D1, Matrix.conjTranspose_mul, hCdiagStar, hSdiagStar, mul_assoc]
        _ = A0† * B + C0† * D := by rw [← hA0eq, ← hC0eq]
        _ = 0 := hAB0
    have hRightRel : Cdiag * Sdiag + B1 * D1† = 0 := by
      have h := congrArg (fun M => P0† * M * P1) hAC0
      have htmp : P0† * (A0 * C0† + B * D†) * P1 = Cdiag * Sdiag + B1 * D1† := by
        have hfirst : P0† * (A0 * C0†) * P1 = Cdiag * Sdiag := by
          rw [hA0eq, hC0eq, Matrix.conjTranspose_mul, hSdiagStar]
          calc
          P0† * (P0 * Cdiag * (Sdiag * P1†)) * P1
            = (((P0† * P0) * Cdiag) * Sdiag) * (P1† * P1) := by simp [mul_assoc]
          _ = Cdiag * Sdiag := by simp [hP0leftU, hP1leftU, mul_assoc]
        have hsecond : P0† * (B * D†) * P1 = B1 * D1† := by
          dsimp [B1, D1]
          simp [mul_assoc]
        calc
          P0† * (A0 * C0† + B * D†) * P1
              = P0† * (A0 * C0†) * P1 + P0† * (B * D†) * P1 := by
                  simp [Matrix.mul_add, add_mul, mul_assoc]
          _ = Cdiag * Sdiag + B1 * D1† := by simp [hfirst, hsecond]
      calc
        Cdiag * Sdiag + B1 * D1† = P0† * (A0 * C0† + B * D†) * P1 := htmp.symm
        _ = 0 := by simpa using h
    have hRightRelT : Sdiag * Cdiag + D1 * B1† = 0 := by
      simpa [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hCdiagStar, hSdiagStar,
        B1, D1, mul_assoc, mul_comm] using congrArg Matrix.conjTranspose hRightRel
    have hColRel : B1† * Cdiag + D1† * Sdiag = 0 := by
      simpa [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hCdiagStar, hSdiagStar,
        B1, D1, mul_assoc] using congrArg Matrix.conjTranspose hLeftRel
    have hBmain : Cdiag * Cdiag + B1 * B1† = 1 := by
      have h := congrArg (fun M => P0† * M * P0) hAA0_BB
      have htmp : P0† * (A0 * A0† + B * B†) * P0 = Cdiag * Cdiag + B1 * B1† := by
        have hfirst : P0† * (A0 * A0†) * P0 = Cdiag * Cdiag := by
          rw [hA0eq, Matrix.conjTranspose_mul, hCdiagStar]
          calc
          P0† * (P0 * Cdiag * (Cdiag * P0†)) * P0
            = (((P0† * P0) * Cdiag) * Cdiag) * (P0† * P0) := by simp [mul_assoc]
          _ = Cdiag * Cdiag := by simp [hP0leftU, mul_assoc]
        have hsecond : P0† * (B * B†) * P0 = B1 * B1† := by
          dsimp [B1]
          simp [mul_assoc]
        calc
          P0† * (A0 * A0† + B * B†) * P0
              = P0† * (A0 * A0†) * P0 + P0† * (B * B†) * P0 := by
                  simp [Matrix.mul_add, add_mul, mul_assoc]
          _ = Cdiag * Cdiag + B1 * B1† := by simp [hfirst, hsecond]
      calc
        Cdiag * Cdiag + B1 * B1† = P0† * (A0 * A0† + B * B†) * P0 := htmp.symm
        _ = P0† * P0 := by simpa using h
        _ = 1 := by simpa [hP0leftU]
    have hDmain : Sdiag * Sdiag + D1 * D1† = 1 := by
      have h := congrArg (fun M => P1† * M * P1) hCC0_DD
      have htmp : P1† * (C0 * C0† + D * D†) * P1 = Sdiag * Sdiag + D1 * D1† := by
        have hfirst : P1† * (C0 * C0†) * P1 = Sdiag * Sdiag := by
          rw [hC0eq, Matrix.conjTranspose_mul, hSdiagStar]
          calc
          P1† * (P1 * Sdiag * (Sdiag * P1†)) * P1
            = (((P1† * P1) * Sdiag) * Sdiag) * (P1† * P1) := by simp [mul_assoc]
          _ = Sdiag * Sdiag := by simp [hP1leftU, mul_assoc]
        have hsecond : P1† * (D * D†) * P1 = D1 * D1† := by
          dsimp [D1]
          simp [mul_assoc]
        calc
          P1† * (C0 * C0† + D * D†) * P1
              = P1† * (C0 * C0†) * P1 + P1† * (D * D†) * P1 := by
                  simp [Matrix.mul_add, add_mul, mul_assoc]
          _ = Sdiag * Sdiag + D1 * D1† := by simp [hfirst, hsecond]
      calc
        Sdiag * Sdiag + D1 * D1† = P1† * (C0 * C0† + D * D†) * P1 := htmp.symm
        _ = P1† * P1 := by simpa using h
        _ = 1 := by simpa [hP1leftU]
    have hBGram : B1 * B1† = Sdiag * Sdiag := by
      calc
        B1 * B1† = 1 - Cdiag * Cdiag := by
          rw [eq_sub_iff_add_eq]
          simpa [add_comm, add_left_comm, add_assoc] using hBmain
        _ = Sdiag * Sdiag := by
          rw [← hCSsum]
          abel
    have hDGram : D1 * D1† = Cdiag * Cdiag := by
      calc
        D1 * D1† = 1 - Sdiag * Sdiag := by
          rw [eq_sub_iff_add_eq]
          simpa [add_comm, add_left_comm, add_assoc] using hDmain
        _ = Cdiag * Cdiag := by
          rw [← hCSsum]
          abel
    let Bcol : Fin N → (Fin N → ℂ) := fun i => B1†.mulVec (Pi.single i 1)
    let Dcol : Fin N → (Fin N → ℂ) := fun i => D1†.mulVec (Pi.single i 1)
    have hBnorm_sq_complex (i : Fin N) :
        (((‖WithLp.toLp 2 (Bcol i)‖ ^ 2 : ℝ)) : ℂ) = ((s i ^ 2 : ℝ) : ℂ) := by
      have hdiag : inner ℂ (WithLp.toLp 2 (Bcol i)) (WithLp.toLp 2 (Bcol i)) = (B1 * B1†) i i := by
        simpa [Bcol, Matrix.mulVec_single_one] using inner_matrix_col_col B1† B1† i i
      have hnormsq : (((‖WithLp.toLp 2 (Bcol i)‖ ^ 2 : ℝ)) : ℂ) = (B1 * B1†) i i := by
        simpa [inner_self_eq_norm_sq_to_K] using hdiag
      calc
        (((‖WithLp.toLp 2 (Bcol i)‖ ^ 2 : ℝ)) : ℂ) = (B1 * B1†) i i := hnormsq
        _ = (Sdiag * Sdiag) i i := by rw [hBGram]
        _ = ((s i ^ 2 : ℝ) : ℂ) := by simp [Sdiag, pow_two]
    have hDnorm_sq_complex (i : Fin N) :
        (((‖WithLp.toLp 2 (Dcol i)‖ ^ 2 : ℝ)) : ℂ) = ((c i ^ 2 : ℝ) : ℂ) := by
      have hdiag : inner ℂ (WithLp.toLp 2 (Dcol i)) (WithLp.toLp 2 (Dcol i)) = (D1 * D1†) i i := by
        simpa [Dcol, Matrix.mulVec_single_one] using inner_matrix_col_col D1† D1† i i
      have hnormsq : (((‖WithLp.toLp 2 (Dcol i)‖ ^ 2 : ℝ)) : ℂ) = (D1 * D1†) i i := by
        simpa [inner_self_eq_norm_sq_to_K] using hdiag
      calc
        (((‖WithLp.toLp 2 (Dcol i)‖ ^ 2 : ℝ)) : ℂ) = (D1 * D1†) i i := hnormsq
        _ = (Cdiag * Cdiag) i i := by rw [hDGram]
        _ = ((c i ^ 2 : ℝ) : ℂ) := by simp [Cdiag, pow_two]
    have hBnorm (i : Fin N) : ‖WithLp.toLp 2 (Bcol i)‖ = s i := by
      have hsq : ‖WithLp.toLp 2 (Bcol i)‖ ^ 2 = s i ^ 2 := by
        exact_mod_cast hBnorm_sq_complex i
      have hsqrt := congrArg Real.sqrt hsq
      simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg (WithLp.toLp 2 (Bcol i))),
        abs_of_nonneg (hs_nonneg i)] using hsqrt
    have hDnorm (i : Fin N) : ‖WithLp.toLp 2 (Dcol i)‖ = c i := by
      have hsq : ‖WithLp.toLp 2 (Dcol i)‖ ^ 2 = c i ^ 2 := by
        exact_mod_cast hDnorm_sq_complex i
      have hsqrt := congrArg Real.sqrt hsq
      simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg (WithLp.toLp 2 (Dcol i))),
        abs_of_nonneg (hc_nonneg i)] using hsqrt
    have hBoff : ∀ ⦃i j : Fin N⦄, i ≠ j →
        inner ℂ (WithLp.toLp 2 (Bcol i)) (WithLp.toLp 2 (Bcol j)) = 0 := by
      intro i j hij
      calc
        inner ℂ (WithLp.toLp 2 (Bcol i)) (WithLp.toLp 2 (Bcol j)) = (B1 * B1†) i j := by
          simpa [Bcol, Matrix.mulVec_single_one] using inner_matrix_col_col B1† B1† i j
        _ = 0 := by rw [hBGram]; simp [Sdiag, hij]
    have hDoff : ∀ ⦃i j : Fin N⦄, i ≠ j →
        inner ℂ (WithLp.toLp 2 (Dcol i)) (WithLp.toLp 2 (Dcol j)) = 0 := by
      intro i j hij
      calc
        inner ℂ (WithLp.toLp 2 (Dcol i)) (WithLp.toLp 2 (Dcol j)) = (D1 * D1†) i j := by
          simpa [Dcol, Matrix.mulVec_single_one] using inner_matrix_col_col D1† D1† i j
        _ = 0 := by rw [hDGram]; simp [Cdiag, hij]
    have hBDoff : ∀ ⦃i j : Fin N⦄, i ≠ j →
        inner ℂ (WithLp.toLp 2 (Bcol i)) (WithLp.toLp 2 (Dcol j)) = 0 := by
      intro i j hij
      calc
        inner ℂ (WithLp.toLp 2 (Bcol i)) (WithLp.toLp 2 (Dcol j)) = (B1 * D1†) i j := by
          simpa [Bcol, Dcol, Matrix.mulVec_single_one] using inner_matrix_col_col B1† D1† i j
        _ = 0 := by
          have h := congrFun (congrFun hRightRel i) j
          have hdiag : (Cdiag * Sdiag) i j = 0 := by simp [Cdiag, Sdiag, hij]
          simpa [hdiag] using h
    have hDBoff : ∀ ⦃i j : Fin N⦄, i ≠ j →
        inner ℂ (WithLp.toLp 2 (Dcol i)) (WithLp.toLp 2 (Bcol j)) = 0 := by
      intro i j hij
      calc
        inner ℂ (WithLp.toLp 2 (Dcol i)) (WithLp.toLp 2 (Bcol j)) = (D1 * B1†) i j := by
          simpa [Bcol, Dcol, Matrix.mulVec_single_one] using inner_matrix_col_col D1† B1† i j
        _ = 0 := by
          have h := congrFun (congrFun hRightRelT i) j
          have hdiag : (Sdiag * Cdiag) i j = 0 := by simp [Cdiag, Sdiag, hij]
          simpa [hdiag] using h
    let qcol : Fin N → (Fin N → ℂ) :=
      fun i => if c i = 0 then - Bcol i else ((c i : ℂ)⁻¹) • Dcol i
    have hqnorm : ∀ i, ‖WithLp.toLp 2 (qcol i)‖ = 1 := by
      intro i
      by_cases hci : c i = 0
      · have hs_sq : s i ^ 2 = 1 := by
          nlinarith [hcs i, hci]
        have hs_eq : s i = 1 := by
          nlinarith [hs_nonneg i, hs_sq]
        simpa [qcol, hci, hBnorm i, hs_eq]
      · calc
          ‖WithLp.toLp 2 (qcol i)‖ = ‖((c i : ℂ)⁻¹)‖ * ‖WithLp.toLp 2 (Dcol i)‖ := by
            simp [qcol, hci, norm_smul]
          _ = (c i)⁻¹ * c i := by
            rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc_nonneg i), hDnorm i]
          _ = 1 := by field_simp [hci]
    have hqoff : ∀ ⦃i j : Fin N⦄, i ≠ j →
        inner ℂ (WithLp.toLp 2 (qcol i)) (WithLp.toLp 2 (qcol j)) = 0 := by
      intro i j hij
      by_cases hci : c i = 0
      · by_cases hcj : c j = 0
        · simpa [qcol, hci, hcj] using hBoff hij
        · simpa [qcol, hci, hcj, inner_neg_left, inner_neg_right,
            inner_smul_left, inner_smul_right, hBDoff hij, mul_assoc] using hBDoff hij
      · by_cases hcj : c j = 0
        · simpa [qcol, hci, hcj, inner_neg_left, inner_neg_right,
            inner_smul_left, inner_smul_right, hDBoff hij, mul_assoc] using hDBoff hij
        · simpa [qcol, hci, hcj, inner_smul_left, inner_smul_right, hDoff hij, mul_assoc] using hDoff hij
    let Qmat : Square N := fun r c' => qcol c' r
    have hQmatcol (i : Fin N) : Qmat.mulVec (Pi.single i 1) = qcol i := by
      ext r
      simp [Qmat, Matrix.mulVec, dotProduct, Pi.single_apply]
    rcases exists_unitary_mul_realDiagonal_of_orthogonal_cols Qmat (fun _ => (1 : ℝ))
        (fun _ => by norm_num)
        (by
          intro i j hij
          simpa [hQmatcol i, hQmatcol j] using hqoff hij)
        (by
          intro i
          simpa [hQmatcol i] using hqnorm i) with ⟨R0, hR0, hQmatEq0⟩
    have hQmatEq : Qmat = R0 := by
      simpa using hQmatEq0
    have hqcol (i : Fin N) : qcol i = R0.mulVec (Pi.single i 1) := by
      have h := congrArg (fun M => M.mulVec (Pi.single i 1)) hQmatEq
      simpa [hQmatcol i] using h
    have hColRel_i (i : Fin N) : (c i : ℂ) • Bcol i + (s i : ℂ) • Dcol i = 0 := by
      ext r
      have h := congrFun (congrArg (fun M => M.mulVec (Pi.single i 1)) hColRel) r
      simpa [Bcol, Dcol, Cdiag, Sdiag, Matrix.add_mulVec, Matrix.mulVec_mulVec,
        Matrix.diagonal_mulVec_single, Matrix.mulVec_smul, Matrix.mulVec, dotProduct,
        Pi.single_apply, Pi.smul_apply, one_mul, mul_assoc, mul_comm, mul_left_comm] using h
    have hDcol (i : Fin N) : Dcol i = (c i : ℂ) • (R0.mulVec (Pi.single i 1)) := by
      by_cases hci : c i = 0
      · have hzeroNorm : ‖WithLp.toLp 2 (Dcol i)‖ = 0 := by
          simpa [hci] using hDnorm i
        have hzeroTo : WithLp.toLp 2 (Dcol i) = 0 := by
          exact norm_eq_zero.mp hzeroNorm
        have hzero : Dcol i = 0 := by
          apply WithLp.toLp_injective (p := 2)
          simpa using hzeroTo
        simp [hci, hzero]
      · have hciC : (c i : ℂ) ≠ 0 := by exact_mod_cast hci
        calc
          Dcol i = (c i : ℂ) • qcol i := by
            simp [qcol, hci, smul_smul, inv_mul_cancel₀ hciC]
          _ = (c i : ℂ) • (R0.mulVec (Pi.single i 1)) := by
                exact congrArg (fun v => (c i : ℂ) • v) (hqcol i)
    have hBcol (i : Fin N) : Bcol i = - (s i : ℂ) • (R0.mulVec (Pi.single i 1)) := by
      ext r
      by_cases hci : c i = 0
      · have hs_sq : s i ^ 2 = 1 := by
          simpa [hci] using hcs i
        have hs_eq : s i = 1 := by
          have hsqrt := congrArg Real.sqrt hs_sq
          simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (hs_nonneg i)] using hsqrt
        have hqpoint : qcol i r = R0.mulVec (Pi.single i 1) r := by
          simpa using congrFun (hqcol i) r
        calc
          Bcol i r = (- qcol i) r := by simp [qcol, hci]
          _ = -(R0.mulVec (Pi.single i 1) r) := by simpa [hqpoint]
          _ = (- (s i : ℂ) • (R0.mulVec (Pi.single i 1))) r := by
                simp [Pi.smul_apply, hs_eq]
      · have hciC : (c i : ℂ) ≠ 0 := by exact_mod_cast hci
        have hpoint : (c i : ℂ) * Bcol i r + (s i : ℂ) * Dcol i r = 0 := by
          simpa [Pi.smul_apply] using congrFun (hColRel_i i) r
        have hDpoint : Dcol i r = (c i : ℂ) * (R0.mulVec (Pi.single i 1) r) := by
          simpa [Pi.smul_apply] using congrFun (hDcol i) r
        rw [hDpoint] at hpoint
        have hmul :
            (c i : ℂ) * Bcol i r = (c i : ℂ) * ((- (s i : ℂ) • (R0.mulVec (Pi.single i 1))) r) := by
          calc
            (c i : ℂ) * Bcol i r = - ((s i : ℂ) * ((c i : ℂ) * (R0.mulVec (Pi.single i 1) r))) := by
                exact eq_neg_of_add_eq_zero_left hpoint
            _ = (c i : ℂ) * ((- (s i : ℂ) • (R0.mulVec (Pi.single i 1))) r) := by
                simp [Pi.smul_apply]
                ring
        have hcancel := congrArg (fun z => (c i : ℂ)⁻¹ * z) hmul
        simpa [Pi.smul_apply, hciC, mul_assoc] using hcancel
    have hReqD : D1† = R0 * Cdiag := by
      ext r i
      calc
        D1† r i = Dcol i r := by simpa [Dcol, Matrix.mulVec_single_one]
        _ = ((c i : ℂ) • (R0.mulVec (Pi.single i 1))) r := by
              simpa [Pi.smul_apply] using congrFun (hDcol i) r
        _ = (R0 * Cdiag) r i := by
          have hcol : (R0.mulVec (Pi.single i 1)) r = R0 r i := by
            rw [Matrix.mulVec_single_one]
            rfl
          rw [Pi.smul_apply, hcol]
          simpa [Cdiag, mul_comm] using
            (Matrix.mul_diagonal (d := fun j => (c j : ℂ)) (M := R0) r i).symm
    have hReqB : B1† = R0 * NegSdiag := by
      ext r i
      calc
        B1† r i = Bcol i r := by simpa [Bcol, Matrix.mulVec_single_one]
        _ = ((-(s i : ℂ)) • (R0.mulVec (Pi.single i 1))) r := by
              simpa [Pi.smul_apply] using congrFun (hBcol i) r
        _ = (R0 * NegSdiag) r i := by
          have hcol : (R0.mulVec (Pi.single i 1)) r = R0 r i := by
            rw [Matrix.mulVec_single_one]
            rfl
          rw [Pi.smul_apply, hcol]
          simpa [NegSdiag, mul_comm] using
            (Matrix.mul_diagonal (d := fun j => (-(s j : ℂ))) (M := R0) r i).symm
    let Q1 : Square N := R0†
    have hQ1 : Q1 ∈ Matrix.unitaryGroup (Fin N) ℂ := conjTranspose_mem_unitaryGroup hR0
    have hNegSdiagStar : NegSdiag† = NegSdiag := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [NegSdiag]
      · have hji : j ≠ i := by simpa [eq_comm] using hij
        simp [Matrix.conjTranspose, NegSdiag, Matrix.diagonal_apply_ne, hij, hji]
    have hB1eq : B1 = NegSdiag * Q1 := by
      have h := congrArg Matrix.conjTranspose hReqB
      calc
        B1 = (R0 * NegSdiag)† := by simpa using h
        _ = NegSdiag† * R0† := by rw [Matrix.conjTranspose_mul]
        _ = NegSdiag * Q1 := by simp [Q1, hNegSdiagStar]
    have hD1eq : D1 = Cdiag * Q1 := by
      have h := congrArg Matrix.conjTranspose hReqD
      calc
        D1 = (R0 * Cdiag)† := by simpa using h
        _ = Cdiag† * R0† := by rw [Matrix.conjTranspose_mul]
        _ = Cdiag * Q1 := by simp [Q1, hCdiagStar]
    have hAeq : A = P0 * Cdiag * Q0 := by
      calc
        A = A0 * Q0 := by
              dsimp [A0]
              simp [mul_assoc, hQ0left]
        _ = P0 * Cdiag * Q0 := by rw [hA0eq, mul_assoc]
    have hCeq : C = P1 * Sdiag * Q0 := by
      calc
        C = C0 * Q0 := by
              dsimp [C0]
              simp [mul_assoc, hQ0left]
        _ = P1 * Sdiag * Q0 := by rw [hC0eq, mul_assoc]
    have hBeq : B = P0 * NegSdiag * Q1 := by
      calc
        B = 1 * B := by simp
        _ = (P0 * P0†) * B := by rw [hP0rightU]
        _ = P0 * B1 := by simp [B1, mul_assoc]
        _ = P0 * NegSdiag * Q1 := by rw [hB1eq]; simp [mul_assoc]
    have hDeq : D = P1 * Cdiag * Q1 := by
      calc
        D = 1 * D := by simp
        _ = (P1 * P1†) * D := by rw [hP1rightU]
        _ = P1 * D1 := by simp [D1, mul_assoc]
        _ = P1 * Cdiag * Q1 := by rw [hD1eq]; simp [mul_assoc]
    have hUbDecomp :
        Matrix.fromBlocks A B C D =
          Matrix.fromBlocks P0 0 0 P1 *
            Matrix.fromBlocks Cdiag NegSdiag Sdiag Cdiag *
            Matrix.fromBlocks Q0 0 0 Q1 := by
      rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp [hAeq, hBeq, hCeq, hDeq, mul_assoc]
    have hU0blocks :
        blockify (n := N) U0 =
          blockify (n := N)
            (unblockify (Matrix.fromBlocks P0 0 0 P1) *
              unblockify (Matrix.fromBlocks Cdiag NegSdiag Sdiag Cdiag) *
              unblockify (Matrix.fromBlocks Q0 0 0 Q1)) := by
      calc
        blockify (n := N) U0 = Ub := by rfl
        _ = Matrix.fromBlocks A B C D := by rw [← hUbBlocks]
        _ = Matrix.fromBlocks P0 0 0 P1 *
              Matrix.fromBlocks Cdiag NegSdiag Sdiag Cdiag *
              Matrix.fromBlocks Q0 0 0 Q1 := hUbDecomp
        _ = blockify (n := N) (unblockify (Matrix.fromBlocks P0 0 0 P1)) *
              blockify (n := N) (unblockify (Matrix.fromBlocks Cdiag NegSdiag Sdiag Cdiag)) *
              blockify (n := N) (unblockify (Matrix.fromBlocks Q0 0 0 Q1)) := by simp
        _ = blockify (n := N)
              (unblockify (Matrix.fromBlocks P0 0 0 P1) *
                unblockify (Matrix.fromBlocks Cdiag NegSdiag Sdiag Cdiag) *
                unblockify (Matrix.fromBlocks Q0 0 0 Q1)) := by
              rw [blockify_mul, blockify_mul]
    have hU0eq :
        U0 =
          unblockify (Matrix.fromBlocks P0 0 0 P1) *
            unblockify (Matrix.fromBlocks Cdiag NegSdiag Sdiag Cdiag) *
            unblockify (Matrix.fromBlocks Q0 0 0 Q1) := by
      apply blockify_injective (n := N)
      simpa using hU0blocks
    have hc_le_one : ∀ i, c i ≤ 1 := by
      intro i
      nlinarith [hcs i, hc_nonneg i, hs_nonneg i]
    let θ : Fin N → ℝ := fun i => 2 * Real.arccos (c i)
    have hθcos : ∀ i, Real.cos (θ i / 2) = c i := by
      intro i
      dsimp [θ]
      rw [show ((2 * Real.arccos (c i)) / 2 : ℝ) = Real.arccos (c i) by ring]
      exact Real.cos_arccos (by linarith [hc_nonneg i]) (hc_le_one i)
    have hθsin : ∀ i, Real.sin (θ i / 2) = s i := by
      intro i
      dsimp [θ]
      rw [show ((2 * Real.arccos (c i)) / 2 : ℝ) = Real.arccos (c i) by ring, Real.sin_arccos]
      have hc_sq : c i ^ 2 = eigVals i := by
        simp [c, Real.sq_sqrt, hEig_nonneg i]
      rw [show 1 - c i ^ 2 = 1 - eigVals i by rw [hc_sq]]
    let Pouter : Square (2 ^ (m + 1)) :=
      castSquare (two_mul_pow_eq_pow_succ m) (unblockify (Matrix.fromBlocks P0 0 0 P1))
    let Router : Square (2 ^ (m + 1)) :=
      castSquare (two_mul_pow_eq_pow_succ m)
        (unblockify (Matrix.fromBlocks Cdiag NegSdiag Sdiag Cdiag))
    let Qouter : Square (2 ^ (m + 1)) :=
      castSquare (two_mul_pow_eq_pow_succ m) (unblockify (Matrix.fromBlocks Q0 0 0 Q1))
    have hPouter : Pouter ∈ Matrix.unitaryGroup (Fin (2 ^ (m + 1))) ℂ := by
      dsimp [Pouter]
      exact castSquare_mem_unitaryGroup (two_mul_pow_eq_pow_succ m)
        (unblockify_mem_unitaryGroup (BlockHelpers.fromBlocks_diagonal_unitary P0 P1 hP0 hP1))
    have hQouter : Qouter ∈ Matrix.unitaryGroup (Fin (2 ^ (m + 1))) ℂ := by
      dsimp [Qouter]
      exact castSquare_mem_unitaryGroup (two_mul_pow_eq_pow_succ m)
        (unblockify_mem_unitaryGroup (BlockHelpers.fromBlocks_diagonal_unitary Q0 Q1 hQ0 hQ1))
    have hMidBlocks :
        Matrix.fromBlocks Cdiag NegSdiag Sdiag Cdiag =
          Matrix.fromBlocks
            (Matrix.diagonal fun i => ((Real.cos (θ i / 2)) : ℂ))
            (- Matrix.diagonal fun i => ((Real.sin (θ i / 2)) : ℂ))
            (Matrix.diagonal fun i => ((Real.sin (θ i / 2)) : ℂ))
            (Matrix.diagonal fun i => ((Real.cos (θ i / 2)) : ℂ)) := by
      refine Matrix.fromBlocks_inj.2 ?_
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [Cdiag, Sdiag, NegSdiag, hθcos, hθsin]
        · simp [Cdiag, Sdiag, NegSdiag, hij]
    have hStep : HasGeneralCosineSineStep (m + 1) U Pouter Router Qouter := by
      refine ⟨P0, P1, Q0, Q1, θ, rfl, ?_, rfl⟩
      simpa [Router] using
        congrArg (fun M => castSquare (two_mul_pow_eq_pow_succ m) (unblockify M)) hMidBlocks
    have hU0cast : castSquare (two_mul_pow_eq_pow_succ m) U0 = U := by
      ext i j
      dsimp [U0, castSquare, reindexSquare]
      have hcast_cancel {a b : ℕ} (hab : a = b) (x : Fin b) :
          (Equiv.cast (congrArg Fin hab.symm)).symm
            ((Equiv.cast (congrArg Fin hab)).symm x) = x := by
        cases hab
        rfl
      have hi :
          (Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ m).symm)).symm
            ((Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ m))).symm i) = i := by
        simpa using hcast_cancel (hab := two_mul_pow_eq_pow_succ m) i
      have hj :
          (Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ m).symm)).symm
            ((Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ m))).symm j) = j := by
        simpa using hcast_cancel (hab := two_mul_pow_eq_pow_succ m) j
      rw [hi, hj]
    have hEqCast := congrArg (castSquare (two_mul_pow_eq_pow_succ m)) hU0eq
    have hEq : U = Pouter * Router * Qouter := by
      rw [hU0cast] at hEqCast
      simpa [Pouter, Router, Qouter, castSquare_mul, mul_assoc] using hEqCast
    have hRouter : Router ∈ Matrix.unitaryGroup (Fin (2 ^ (m + 1))) ℂ := by
      exact middle_factor_mem_unitaryGroup hU hPouter hQouter hEq
    exact ⟨Pouter, Router, Qouter, hPouter, hRouter, hQouter, hStep, hEq⟩

private theorem two_qubit_witness_hasGeneralCosineSineStep {U P R Q : Square 4}
    (h : TwoQubitCosineSineWitness U P R Q) :
    HasGeneralCosineSineStep 2 U P R Q := by
  rcases h with ⟨P₀, P₁, Q₀, Q₁, θ₀, θ₁, _, _, _, _, hP, hR, hQ⟩
  change ∃ P₀ P₁ Q₀ Q₁ : Square 2,
      ∃ θ : Fin 2 → ℝ,
        P = castSquare (two_mul_pow_eq_pow_succ 1)
              (unblockify (Matrix.fromBlocks P₀ 0 0 P₁)) ∧
        R = castSquare (two_mul_pow_eq_pow_succ 1)
              (unblockify
                (Matrix.fromBlocks
                  (Matrix.diagonal fun i => ((Real.cos (θ i / 2)) : ℂ))
                  (- Matrix.diagonal fun i => ((Real.sin (θ i / 2)) : ℂ))
                  (Matrix.diagonal fun i => ((Real.sin (θ i / 2)) : ℂ))
                  (Matrix.diagonal fun i => ((Real.cos (θ i / 2)) : ℂ)))) ∧
        Q = castSquare (two_mul_pow_eq_pow_succ 1)
              (unblockify (Matrix.fromBlocks Q₀ 0 0 Q₁))
  refine ⟨P₀, P₁, Q₀, Q₁, ![θ₀, θ₁], ?_, ?_, ?_⟩
  · rw [hP]
    simp [castSquare, reindexSquare,
      CosineSine.blockDiag2, unblockify_fromBlocks, zero_kron_right]
  · rw [hR]
    have hCos :
        Matrix.diagonal (fun i : Fin 2 => Complex.cos (((![θ₀, θ₁] i : ℝ) : ℂ) / 2)) =
          CosineSine.realDiag2 (Real.cos (θ₀ / 2)) (Real.cos (θ₁ / 2)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [CosineSine.realDiag2, diag2]
    have hSin :
        Matrix.diagonal (fun i : Fin 2 => Complex.sin (((![θ₀, θ₁] i : ℝ) : ℂ) / 2)) =
          CosineSine.realDiag2 (Real.sin (θ₀ / 2)) (Real.sin (θ₁ / 2)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [CosineSine.realDiag2, diag2]
    have hNegSin :
        Matrix.diagonal (fun i : Fin 2 => - Complex.sin (((![θ₀, θ₁] i : ℝ) : ℂ) / 2)) =
          - CosineSine.realDiag2 (Real.sin (θ₀ / 2)) (Real.sin (θ₁ / 2)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [CosineSine.realDiag2, diag2]
    simpa [hCos, hSin, hNegSin, castSquare, reindexSquare, CosineSine.csBlockCore] using
      (CosineSine.csBlockCore_eq_conditionalRy (θ₀ := θ₀) (θ₁ := θ₁)
        (hc₀ := rfl) (hc₁ := rfl) (hs₀ := rfl) (hs₁ := rfl)).symm
  · rw [hQ]
    simp [castSquare, reindexSquare,
      CosineSine.blockDiag2, unblockify_fromBlocks, zero_kron_right]

/-- Concrete 2-qubit instance of the Paige-Wei cosine-sine step.

This is the fully proved base case available before the arbitrary-`n`
formalization is completed. -/
theorem general_cosine_sine_step_two_qubit (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ P R Q : Square 4,
      P ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      R ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      Q ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      HasGeneralCosineSineStep 2 U P R Q ∧
      U = P * R * Q := by
  rcases two_qubit_cosine_sine_step U hU with ⟨P, R, Q, hP, hR, hQ, hStep, hEq⟩
  exact ⟨P, R, Q, hP, hR, hQ, two_qubit_witness_hasGeneralCosineSineStep hStep, hEq⟩

/-- General version of the Paige-Wei cosine-sine decomposition used by Lemma 1. -/
def general_cosine_sine_step : {n : ℕ} →
    (hn : 1 ≤ n) →
    (U : Square (2 ^ n)) →
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) →
    ∃ P R Q : Square (2 ^ n),
      P ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
      R ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
      Q ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
      HasGeneralCosineSineStep n U P R Q ∧
      U = P * R * Q
  | 2, _hn, U, hU => by
      simpa using general_cosine_sine_step_two_qubit U hU
  | n, hn, U, hU => general_cosine_sine_step_exists hn U hU

/-! ### Lemma 1 statement scaffold -/

/-- Paper step 2: convert a uniformly controlled `R_y` family into a
uniformly controlled `R_z` family by conjugating on the first wire. -/
theorem controlled_ry_family_via_controlled_rz (m : ℕ)
    (θ : Fin (2 ^ m) → ℝ) :
    controlledRyFamily m θ =
      liftTopOneQubit m phaseSdagger *
        liftTopOneQubit m hadamard2 *
        controlledRzFamily m (fun i => - θ i) *
        liftTopOneQubit m hadamard2 *
        liftTopOneQubit m phaseS := by
  have hInner :
      unblockify
          (Matrix.fromBlocks
            (Matrix.diagonal fun i => ((Real.cos (θ i / 2)) : ℂ))
            (- Matrix.diagonal fun i => ((Real.sin (θ i / 2)) : ℂ))
            (Matrix.diagonal fun i => ((Real.sin (θ i / 2)) : ℂ))
            (Matrix.diagonal fun i => ((Real.cos (θ i / 2)) : ℂ))) =
        ((phaseSdagger * hadamard2) ⊗ₖ (1 : Square (2 ^ m))) *
          unblockify
            (Matrix.fromBlocks
              (Matrix.diagonal fun i => Complex.exp (-Complex.I * ((- θ i) / 2)))
              0 0
              (Matrix.diagonal fun i => Complex.exp (Complex.I * ((- θ i) / 2)))) *
          ((hadamard2 * phaseS) ⊗ₖ (1 : Square (2 ^ m))) := by
    apply blockify_injective (n := 2 ^ m)
    rw [blockify_unblockify]
    trans
      Matrix.fromBlocks
        (Matrix.diagonal fun i => (((phaseSdagger * hadamard2) * rz (- θ i) * (hadamard2 * phaseS)) 0 0))
        (Matrix.diagonal fun i => (((phaseSdagger * hadamard2) * rz (- θ i) * (hadamard2 * phaseS)) 0 1))
        (Matrix.diagonal fun i => (((phaseSdagger * hadamard2) * rz (- θ i) * (hadamard2 * phaseS)) 1 0))
        (Matrix.diagonal fun i => (((phaseSdagger * hadamard2) * rz (- θ i) * (hadamard2 * phaseS)) 1 1))
    refine Matrix.fromBlocks_inj.2 ?_
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext i j
      by_cases hij : i = j
      · subst j
        have h00 := congrArg (fun M => M 0 0) (lemma3_ry_via_rz (θ i))
        simpa [CosineSine.ry, diag2, mul_assoc] using h00
      · simp [hij]
    · ext i j
      by_cases hij : i = j
      · subst j
        have h01 := congrArg (fun M => M 0 1) (lemma3_ry_via_rz (θ i))
        simpa [CosineSine.ry, diag2, mul_assoc] using h01
      · simp [hij]
    · ext i j
      by_cases hij : i = j
      · subst j
        have h10 := congrArg (fun M => M 1 0) (lemma3_ry_via_rz (θ i))
        simpa [CosineSine.ry, diag2, mul_assoc] using h10
      · simp [hij]
    · ext i j
      by_cases hij : i = j
      · subst j
        have h11 := congrArg (fun M => M 1 1) (lemma3_ry_via_rz (θ i))
        simpa [CosineSine.ry, diag2, mul_assoc] using h11
      · simp [hij]
    · simpa [mul_assoc] using
        (blockify_top_conjugation_of_controlledRzCore
          (m := m) (α := fun i => - θ i) (A := phaseSdagger * hadamard2) (B := hadamard2 * phaseS)).symm
  have hPairLeft :
      castSquare (two_mul_pow_eq_pow_succ m)
          (((phaseSdagger * hadamard2) ⊗ₖ (1 : Square (2 ^ m)))) =
        liftTopOneQubit m phaseSdagger * liftTopOneQubit m hadamard2 := by
    calc
      castSquare (two_mul_pow_eq_pow_succ m)
          (((phaseSdagger * hadamard2) ⊗ₖ (1 : Square (2 ^ m))))
          = castSquare (two_mul_pow_eq_pow_succ m)
              ((phaseSdagger ⊗ₖ (1 : Square (2 ^ m))) * (hadamard2 ⊗ₖ (1 : Square (2 ^ m)))) :=
            congrArg (castSquare (two_mul_pow_eq_pow_succ m))
              (by simpa using
                (KronHelpers.kron_mul_reindex phaseSdagger hadamard2
                  (1 : Square (2 ^ m)) (1 : Square (2 ^ m))))
      _ = liftTopOneQubit m phaseSdagger * liftTopOneQubit m hadamard2 := by
            simp [liftTopOneQubit, castSquare_mul]
  have hPairRight :
      castSquare (two_mul_pow_eq_pow_succ m)
          (((hadamard2 * phaseS) ⊗ₖ (1 : Square (2 ^ m)))) =
        liftTopOneQubit m hadamard2 * liftTopOneQubit m phaseS := by
    calc
      castSquare (two_mul_pow_eq_pow_succ m)
          (((hadamard2 * phaseS) ⊗ₖ (1 : Square (2 ^ m))))
          = castSquare (two_mul_pow_eq_pow_succ m)
              ((hadamard2 ⊗ₖ (1 : Square (2 ^ m))) * (phaseS ⊗ₖ (1 : Square (2 ^ m)))) :=
            congrArg (castSquare (two_mul_pow_eq_pow_succ m))
              (by simpa using
                (KronHelpers.kron_mul_reindex hadamard2 phaseS
                  (1 : Square (2 ^ m)) (1 : Square (2 ^ m))))
      _ = liftTopOneQubit m hadamard2 * liftTopOneQubit m phaseS := by
            simp [liftTopOneQubit, castSquare_mul]
  calc
    controlledRyFamily m θ
        = castSquare (two_mul_pow_eq_pow_succ m)
            (unblockify
              (Matrix.fromBlocks
                (Matrix.diagonal fun i => ((Real.cos (θ i / 2)) : ℂ))
                (- Matrix.diagonal fun i => ((Real.sin (θ i / 2)) : ℂ))
                (Matrix.diagonal fun i => ((Real.sin (θ i / 2)) : ℂ))
                (Matrix.diagonal fun i => ((Real.cos (θ i / 2)) : ℂ)))) := by
          rfl
    _ = castSquare (two_mul_pow_eq_pow_succ m)
          (((phaseSdagger * hadamard2) ⊗ₖ (1 : Square (2 ^ m)))) *
            controlledRzFamily m (fun i => - θ i) *
            castSquare (two_mul_pow_eq_pow_succ m)
              (((hadamard2 * phaseS) ⊗ₖ (1 : Square (2 ^ m)))) := by
          simpa [controlledRzFamily, firstQubitBlockDiag, castSquare_mul, mul_assoc] using
            congrArg (castSquare (two_mul_pow_eq_pow_succ m)) hInner
    _ = (liftTopOneQubit m phaseSdagger * liftTopOneQubit m hadamard2) *
          controlledRzFamily m (fun i => - θ i) *
          (liftTopOneQubit m hadamard2 * liftTopOneQubit m phaseS) := by
          rw [hPairLeft, hPairRight]
    _ = liftTopOneQubit m phaseSdagger *
          liftTopOneQubit m hadamard2 *
          controlledRzFamily m (fun i => - θ i) *
          liftTopOneQubit m hadamard2 *
          liftTopOneQubit m phaseS := by
          simp [mul_assoc]

/-- Shende-Bullock-Markov demultiplexing for a first-qubit block-diagonal gate. -/
private theorem firstQubitBlockDiag_mul (m : ℕ)
    (A₀ A₁ B₀ B₁ : Square (2 ^ m)) :
    firstQubitBlockDiag m (A₀ * B₀) (A₁ * B₁) =
      firstQubitBlockDiag m A₀ A₁ * firstQubitBlockDiag m B₀ B₁ := by
  have hBlocks :
      unblockify (Matrix.fromBlocks (A₀ * B₀) 0 0 (A₁ * B₁)) =
        unblockify (Matrix.fromBlocks A₀ 0 0 A₁) *
          unblockify (Matrix.fromBlocks B₀ 0 0 B₁) := by
    apply blockify_injective (n := 2 ^ m)
    simp [Matrix.fromBlocks_multiply]
  simpa [firstQubitBlockDiag, castSquare_mul] using
    congrArg (castSquare (two_mul_pow_eq_pow_succ m)) hBlocks

/-- Shende-Bullock-Markov demultiplexing for a first-qubit block-diagonal gate. -/
theorem general_demultiplexing_step {m : ℕ} (hm : 1 ≤ m)
    (U₀ U₁ : Square (2 ^ m))
    (hU₀ : U₀ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ)
    (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ) :
    ∃ P Q : Square (2 ^ m), ∃ α : Fin (2 ^ m) → ℝ,
      P ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ ∧
      Q ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ ∧
      firstQubitBlockDiag m U₀ U₁ =
        liftLowerUnitary m Q * controlledRzFamily m α * liftLowerUnitary m P := by
  let W : Square (2 ^ m) := U₁ * U₀†
  have hW : W ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
    dsimp [W]
    exact Submonoid.mul_mem _ hU₁ (conjTranspose_mem_unitaryGroup hU₀)
  rcases unitary_diagonal_exists W hW with ⟨z, Q, hzNorm, hQ, hQdiag⟩
  let α : Fin (2 ^ m) → ℝ := fun i => Complex.arg (z i)
  let D₀ : Square (2 ^ m) :=
    Matrix.diagonal fun i => Complex.exp (-Complex.I * (α i / 2))
  let D₁ : Square (2 ^ m) :=
    Matrix.diagonal fun i => Complex.exp (Complex.I * (α i / 2))
  let P : Square (2 ^ m) := D₀† * Q† * U₀
  have hzexp : ∀ i, z i = Complex.exp (α i * Complex.I) := by
    intro i
    simpa [α, hzNorm i, mul_comm] using (Complex.norm_mul_exp_arg_mul_I (z i)).symm
  have hD₀norm : ∀ i, ‖Complex.exp (-Complex.I * (α i / 2))‖ = 1 := by
    intro i
    calc
      ‖Complex.exp (-Complex.I * (α i / 2))‖ = ‖Complex.exp ((-(α i / 2)) * Complex.I)‖ := by
        congr 1
        ring
      _ = 1 := by
        simpa using Complex.norm_exp_ofReal_mul_I (-(α i / 2))
  have hD₀ : D₀ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
    refine diagonal_unitary _ ?_
    intro i
    simpa [D₀] using hD₀norm i
  have hP : P ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
    exact Submonoid.mul_mem _
      (Submonoid.mul_mem _ (conjTranspose_mem_unitaryGroup hD₀)
        (conjTranspose_mem_unitaryGroup hQ))
      hU₀
  have hD₀right : D₀ * D₀† = (1 : Square (2 ^ m)) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hD₀)
  have hQright : Q * Q† = (1 : Square (2 ^ m)) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hQ)
  have hU₀left : U₀† * U₀ = (1 : Square (2 ^ m)) := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hU₀)
  have hQdagU₀' : D₀ * P = Q† * U₀ := by
    calc
      D₀ * P = D₀ * (D₀† * Q† * U₀) := by rfl
      _ = (D₀ * D₀†) * Q† * U₀ := by simp [mul_assoc]
      _ = Q† * U₀ := by rw [hD₀right]; simp
  have hQdagU₀ : Q† * U₀ = D₀ * P := hQdagU₀'.symm
  have hU₀eq' : Q * D₀ * P = U₀ := by
    calc
      Q * D₀ * P = Q * (D₀ * P) := by simp [mul_assoc]
      _ = Q * (Q† * U₀) := by rw [hQdagU₀]
      _ = (Q * Q†) * U₀ := by simp [mul_assoc]
      _ = U₀ := by rw [hQright]; simp
  have hU₀eq : U₀ = Q * D₀ * P := hU₀eq'.symm
  have hDiagStep : Matrix.diagonal z * D₀ = D₁ := by
    dsimp [D₀, D₁]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal_apply]
      rw [hzexp i]
      rw [← Complex.exp_add]
      congr 1
      ring_nf
    · simp [Matrix.diagonal_apply_ne, hij]
  have hU₁eq' : Q * D₁ * P = U₁ := by
    calc
      Q * D₁ * P = Q * (Matrix.diagonal z * D₀) * P := by rw [← hDiagStep]
      _ = Q * Matrix.diagonal z * (D₀ * P) := by simp [mul_assoc]
      _ = Q * Matrix.diagonal z * (Q† * U₀) := by rw [hQdagU₀]
      _ = (Q * Matrix.diagonal z * Q†) * U₀ := by simp [mul_assoc]
      _ = W * U₀ := by rw [← hQdiag]
      _ = (U₁ * U₀†) * U₀ := by rfl
      _ = U₁ * (U₀† * U₀) := by simp [mul_assoc]
      _ = U₁ := by rw [hU₀left]; simp
  have hU₁eq : U₁ = Q * D₁ * P := hU₁eq'.symm
  refine ⟨P, Q, α, hP, hQ, ?_⟩
  calc
    firstQubitBlockDiag m U₀ U₁ = firstQubitBlockDiag m (Q * D₀ * P) (Q * D₁ * P) := by
      rw [hU₀eq, hU₁eq]
    _ = firstQubitBlockDiag m ((Q * D₀) * P) ((Q * D₁) * P) := by
      simp [mul_assoc]
    _ = firstQubitBlockDiag m (Q * D₀) (Q * D₁) * liftLowerUnitary m P := by
      rw [firstQubitBlockDiag_mul]
      simp [liftLowerUnitary]
    _ = (liftLowerUnitary m Q * controlledRzFamily m α) * liftLowerUnitary m P := by
      rw [firstQubitBlockDiag_mul]
      simp [liftLowerUnitary, controlledRzFamily, D₀, D₁]
    _ = liftLowerUnitary m Q * controlledRzFamily m α * liftLowerUnitary m P := by
      simp [mul_assoc]

/-- Base case for the recursive proof: every two-qubit unitary is already an
easy gate. -/
theorem two_qubit_unitary_is_easy_gate (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    Synthesizes (EasyGate 2) U := by
  let p : TwoQubitPlacement 2 :=
    { first := 0
      second := 1
      distinct := by decide
      left := 1
      right := 1
      dimension_eq := by decide
      permutation := Equiv.refl _ }
  have hEmbed : IsEmbeddedTwoQubitGate 2 U U := by
    refine ⟨p, ?_⟩
    dsimp [p, TwoQubitPlacement.embed, TwoQubitPlacement.tensor, castSquare, reindexSquare]
    rw [kron_right_one_four, one_kron_four]
    simp [Matrix.submatrix_id_id]
  refine ⟨[U], ?_, by simp [circuitMatrix]⟩
  intro gate hgate
  rw [List.mem_singleton] at hgate
  subst hgate
  exact EasyGate.of_embedded_two_qubit hU hEmbed

private theorem castFin_symm_val {a b : ℕ} (h : a = b) (x : Fin b) :
    (((Equiv.cast (congrArg Fin h)).symm x).1) = x.1 := by
  cases h
  rfl

private theorem cast_one_mul_symm_divNat {n : ℕ} (x : Fin n) :
    ((Equiv.cast (congrArg Fin (show 1 * n = n by simp))).symm x).divNat = 0 := by
  cases n with
  | zero => exact Fin.elim0 x
  | succ n =>
      apply Fin.eq_of_val_eq
      have h : 1 * Nat.succ n = Nat.succ n := by
        simp
      rw [show ((((Equiv.cast (congrArg Fin h)).symm x).divNat).1) =
          (((Equiv.cast (congrArg Fin h)).symm x).1 / Nat.succ n) by rfl]
      have hval : (((Equiv.cast (congrArg Fin h)).symm x).1) = x.1 :=
        castFin_symm_val h x
      rw [hval]
      exact Nat.div_eq_of_lt x.is_lt

private theorem cast_one_mul_symm_modNat {n : ℕ} (x : Fin n) :
    ((Equiv.cast (congrArg Fin (show 1 * n = n by simp))).symm x).modNat = x := by
  cases n with
  | zero => exact Fin.elim0 x
  | succ n =>
      apply Fin.eq_of_val_eq
      have h : 1 * Nat.succ n = Nat.succ n := by
        simp
      rw [show ((((Equiv.cast (congrArg Fin h)).symm x).modNat).1) =
          (((Equiv.cast (congrArg Fin h)).symm x).1 % Nat.succ n) by rfl]
      have hval : (((Equiv.cast (congrArg Fin h)).symm x).1) = x.1 :=
        castFin_symm_val h x
      rw [hval, Nat.mod_eq_of_lt x.is_lt]

private theorem one_kron_any {n : ℕ} (U : Square n) :
    castSquare (show 1 * n = n by simp) ((1 : Square 1) ⊗ₖ U) = U := by
  ext i j
  simp [castSquare, reindexSquare, Matrix.reindex_apply, TwoControl.kron,
    cast_one_mul_symm_divNat, cast_one_mul_symm_modNat]

private theorem castFin_symm_trans {a b c : ℕ} (hab : a = b) (hbc : b = c)
    (x : Fin c) :
    (Equiv.cast (congrArg Fin hab)).symm ((Equiv.cast (congrArg Fin hbc)).symm x) =
      (Equiv.cast (congrArg Fin (hab.trans hbc))).symm x := by
  cases hab
  cases hbc
  rfl

private theorem castSquare_trans {a b c : ℕ} (hab : a = b) (hbc : b = c)
    (U : Square a) :
    castSquare hbc (castSquare hab U) = castSquare (hab.trans hbc) U := by
  ext i j
  change U ((Equiv.cast (congrArg Fin hab)).symm ((Equiv.cast (congrArg Fin hbc)).symm i))
      ((Equiv.cast (congrArg Fin hab)).symm ((Equiv.cast (congrArg Fin hbc)).symm j)) =
    U ((Equiv.cast (congrArg Fin (hab.trans hbc))).symm i)
      ((Equiv.cast (congrArg Fin (hab.trans hbc))).symm j)
  rw [castFin_symm_trans hab hbc i, castFin_symm_trans hab hbc j]

private theorem castFin_val_local {a b : ℕ} (h : a = b) (x : Fin a) :
    ((Equiv.cast (congrArg Fin h) x).1) = x.1 := by
  cases h
  rfl

private theorem castFin_core_cast_symm_local {a b c : ℕ} (hab : a = b) (hcb : c = b)
    (x : Fin a) :
    (Equiv.cast (congrArg Fin hcb)).symm (cast (congrArg Fin hab) x) =
      cast (congrArg Fin (hab.trans hcb.symm)) x := by
  cases hab
  cases hcb
  rfl

private theorem finProd_assoc_2_encoded_local (n p : ℕ) (a : Fin 2) (b : Fin n) (c : Fin p) :
    (Equiv.cast (congrArg Fin ((Nat.mul_assoc 2 n p).symm)))
      (@finProdFinEquiv 2 (n * p) (a, @finProdFinEquiv n p (b, c))) =
    @finProdFinEquiv (2 * n) p (@finProdFinEquiv 2 n (a, b), c) := by
  apply Fin.eq_of_val_eq
  rw [castFin_val_local]
  simp [finProdFinEquiv, Nat.mul_assoc]
  · ring
  · simp [Nat.mul_assoc]

private theorem finProdFinEquiv_cast_right_local {n p q : ℕ} (hpq : p = q)
    (a : Fin n) (b : Fin p) :
    cast (congrArg Fin (congrArg (fun t => n * t) hpq)) (@finProdFinEquiv n p (a, b)) =
      @finProdFinEquiv n q (a, cast (congrArg Fin hpq) b) := by
  cases hpq
  rfl

private theorem topTwoUnitary_eq_kron (m : ℕ) (U : Square 4) :
    topTwoUnitary m U = castSquare (four_mul_pow_eq_pow_add_two m) (U ⊗ₖ (1 : Square (2 ^ m))) := by
  rw [topTwoUnitary, topTwoPlacement, TwoQubitPlacement.embed, TwoQubitPlacement.tensor]
  rw [← castSquare_trans
    (show 1 * (4 * 2 ^ m) = 4 * 2 ^ m by simp)
    (four_mul_pow_eq_pow_add_two m)
    (((1 : Square 1) ⊗ₖ (U ⊗ₖ (1 : Square (2 ^ m)))))]
  simpa using congrArg (castSquare (four_mul_pow_eq_pow_add_two m))
    (one_kron_any (U ⊗ₖ (1 : Square (2 ^ m))))

private noncomputable def pairBlockEquiv (m : ℕ) :
    Fin 4 × Fin (2 ^ m) ≃ Fin (2 ^ (m + 2)) :=
  (@finProdFinEquiv 4 (2 ^ m)).trans (Equiv.cast (congrArg Fin (four_mul_pow_eq_pow_add_two m)))

@[simp] private theorem finProdFinEquiv_symm_zero :
  (@finProdFinEquiv 2 2).symm (0 : Fin 4) = (0, 0) := by rfl

@[simp] private theorem finProdFinEquiv_symm_one :
  (@finProdFinEquiv 2 2).symm (1 : Fin 4) = (0, 1) := by rfl

@[simp] private theorem finProdFinEquiv_symm_two :
  (@finProdFinEquiv 2 2).symm (2 : Fin 4) = (1, 0) := by rfl

@[simp] private theorem finProdFinEquiv_symm_three :
  (@finProdFinEquiv 2 2).symm (3 : Fin 4) = (1, 1) := by rfl

@[simp] private theorem pairBlockEquiv_cast_symm_apply (m : ℕ) (a : Fin 4)
    (r : Fin (2 ^ m)) :
    (Equiv.cast (congrArg Fin (four_mul_pow_eq_pow_add_two m))).symm
      ((pairBlockEquiv m) (a, r)) = @finProdFinEquiv 4 (2 ^ m) (a, r) := by
  change (Equiv.cast (congrArg Fin (four_mul_pow_eq_pow_add_two m))).symm
      ((Equiv.cast (congrArg Fin (four_mul_pow_eq_pow_add_two m)))
        (@finProdFinEquiv 4 (2 ^ m) (a, r))) = @finProdFinEquiv 4 (2 ^ m) (a, r)
  exact (Equiv.cast (congrArg Fin (four_mul_pow_eq_pow_add_two m))).left_inv _

private noncomputable def pairBlockDiagonal (m : ℕ) (M : Fin (2 ^ m) → Square 4) :
    Square (2 ^ (m + 2)) :=
  Matrix.reindex (pairBlockEquiv m) (pairBlockEquiv m) (Matrix.blockDiagonal M)

private theorem pairBlockDiagonal_mul (m : ℕ)
    (M N : Fin (2 ^ m) → Square 4) :
    pairBlockDiagonal m (fun k => M k * N k) =
      pairBlockDiagonal m M * pairBlockDiagonal m N := by
  let e : Fin 4 × Fin (2 ^ m) ≃ Fin (2 ^ (m + 2)) := pairBlockEquiv m
  change (Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal (fun k => M k * N k)) =
      ((Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal M)) *
        ((Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal N))
  rw [Matrix.blockDiagonal_mul]
  simpa [e, pairBlockDiagonal, Matrix.reindexAlgEquiv_apply] using
    (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul (Matrix.blockDiagonal M) (Matrix.blockDiagonal N)

private theorem pairBlockDiagonal_const (m : ℕ) (U : Square 4) :
    pairBlockDiagonal m (fun _ => U) =
      castSquare (four_mul_pow_eq_pow_add_two m) (U ⊗ₖ (1 : Square (2 ^ m))) := by
  ext i j
  obtain ⟨⟨a, r⟩, hi⟩ := (pairBlockEquiv m).surjective i
  obtain ⟨⟨b, s⟩, hj⟩ := (pairBlockEquiv m).surjective j
  symm at hi
  symm at hj
  subst i
  subst j
  by_cases hrs : r = s
  · subst s
    calc
      pairBlockDiagonal m (fun _ => U) ((pairBlockEquiv m) (a, r)) ((pairBlockEquiv m) (b, r))
          = Matrix.blockDiagonal (fun _ => U) (a, r) (b, r) := by
              simp [pairBlockDiagonal, Matrix.reindex_apply]
      _ = U a b := by
            simpa using (Matrix.blockDiagonal_apply_eq (M := fun _ => U) a b r)
      _ = castSquare (four_mul_pow_eq_pow_add_two m) (U ⊗ₖ (1 : Square (2 ^ m)))
            ((pairBlockEquiv m) (a, r)) ((pairBlockEquiv m) (b, r)) := by
              simp [castSquare, reindexSquare, Matrix.reindexAlgEquiv_apply,
                Matrix.reindex_apply, TwoControl.kron_apply]
  · calc
      pairBlockDiagonal m (fun _ => U) ((pairBlockEquiv m) (a, r)) ((pairBlockEquiv m) (b, s))
          = 0 := by
              calc
                pairBlockDiagonal m (fun _ => U) ((pairBlockEquiv m) (a, r)) ((pairBlockEquiv m) (b, s))
                    = Matrix.blockDiagonal (fun _ => U) (a, r) (b, s) := by
                        simp [pairBlockDiagonal, Matrix.reindex_apply]
                _ = 0 := by
                      simpa using (Matrix.blockDiagonal_apply_ne (M := fun _ => U) a b hrs)
      _ = castSquare (four_mul_pow_eq_pow_add_two m) (U ⊗ₖ (1 : Square (2 ^ m)))
            ((pairBlockEquiv m) (a, r)) ((pairBlockEquiv m) (b, s)) := by
              simp [castSquare, reindexSquare, Matrix.reindexAlgEquiv_apply,
                Matrix.reindex_apply, TwoControl.kron_apply, hrs]

@[simp] private theorem pairBlockDiagonal_apply_same (m : ℕ)
    (M : Fin (2 ^ m) → Square 4) (a b : Fin 4) (r : Fin (2 ^ m)) :
    pairBlockDiagonal m M ((pairBlockEquiv m) (a, r)) ((pairBlockEquiv m) (b, r)) = M r a b := by
  simp [pairBlockDiagonal, Matrix.reindex_apply]

@[simp] private theorem pairBlockDiagonal_apply_ne (m : ℕ)
    (M : Fin (2 ^ m) → Square 4) (a b : Fin 4) {r s : Fin (2 ^ m)} (hrs : r ≠ s) :
    pairBlockDiagonal m M ((pairBlockEquiv m) (a, r)) ((pairBlockEquiv m) (b, s)) = 0 := by
  calc
    pairBlockDiagonal m M ((pairBlockEquiv m) (a, r)) ((pairBlockEquiv m) (b, s))
        = Matrix.blockDiagonal M (a, r) (b, s) := by
            simp [pairBlockDiagonal, Matrix.reindex_apply]
    _ = 0 := by
          simpa using (Matrix.blockDiagonal_apply_ne (M := M) a b hrs)

@[simp] private theorem unblockify_finProdFinEquiv_inl_inl {n : ℕ}
    (M : BlockMatrix n) (i j : Fin n) :
    unblockify M (@finProdFinEquiv 2 n (0, i)) (@finProdFinEquiv 2 n (0, j)) =
      M (Sum.inl i) (Sum.inl j) := by
  simp [unblockify, Matrix.reindex_apply]

@[simp] private theorem unblockify_finProdFinEquiv_inl_inr {n : ℕ}
    (M : BlockMatrix n) (i j : Fin n) :
    unblockify M (@finProdFinEquiv 2 n (0, i)) (@finProdFinEquiv 2 n (1, j)) =
      M (Sum.inl i) (Sum.inr j) := by
  simp [unblockify, Matrix.reindex_apply]

@[simp] private theorem unblockify_finProdFinEquiv_inr_inl {n : ℕ}
    (M : BlockMatrix n) (i j : Fin n) :
    unblockify M (@finProdFinEquiv 2 n (1, i)) (@finProdFinEquiv 2 n (0, j)) =
      M (Sum.inr i) (Sum.inl j) := by
  simp [unblockify, Matrix.reindex_apply]

@[simp] private theorem unblockify_finProdFinEquiv_inr_inr {n : ℕ}
    (M : BlockMatrix n) (i j : Fin n) :
    unblockify M (@finProdFinEquiv 2 n (1, i)) (@finProdFinEquiv 2 n (1, j)) =
      M (Sum.inr i) (Sum.inr j) := by
  simp [unblockify, Matrix.reindex_apply]

private theorem topTwoUnitary_eq_pairBlockDiagonal (m : ℕ) (U : Square 4) :
    topTwoUnitary m U = pairBlockDiagonal m (fun _ => U) := by
  rw [topTwoUnitary_eq_kron, pairBlockDiagonal_const]

private theorem diag4_mul_diag4 (a b c d e f g h : ℂ) :
    diag4 a b c d * diag4 e f g h = diag4 (a * e) (b * f) (c * g) (d * h) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag4, Matrix.mul_apply, Fin.sum_univ_four]

private theorem proj0_eq_diag2 : proj0 = diag2 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, ketbra, ket0, diag2]

private theorem proj1_eq_diag2 : proj1 = diag2 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, ketbra, ket1, diag2]

private theorem localOnFirst_rz_eq (θ : ℝ) :
    localOnFirst (rz θ) =
      diag4 (Complex.exp (((-θ) / 2) * Complex.I))
        (Complex.exp (((-θ) / 2) * Complex.I))
        (Complex.exp ((θ / 2) * Complex.I))
        (Complex.exp ((θ / 2) * Complex.I)) := by
  have hneg : Complex.exp (-Complex.I * (θ / 2 : ℂ)) =
      Complex.exp (((-θ) / 2 : ℝ) * Complex.I) := by
    congr 1
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  have hpos : Complex.exp (Complex.I * (θ / 2 : ℂ)) =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) := by
    congr 1
    simp [mul_comm]
  rw [localOnFirst, rz, hneg, hpos, ← diag2_one_one]
  simpa using
    (diag2_kron_diag2
      (Complex.exp (((-θ) / 2) * Complex.I))
      (Complex.exp ((θ / 2) * Complex.I))
      (1 : ℂ) (1 : ℂ))

private theorem localOnSecond_rz_eq (θ : ℝ) :
    localOnSecond (rz θ) =
      diag4 (Complex.exp (((-θ) / 2) * Complex.I))
        (Complex.exp ((θ / 2) * Complex.I))
        (Complex.exp (((-θ) / 2) * Complex.I))
        (Complex.exp ((θ / 2) * Complex.I)) := by
  have hneg : Complex.exp (-Complex.I * (θ / 2 : ℂ)) =
      Complex.exp (((-θ) / 2 : ℝ) * Complex.I) := by
    congr 1
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  have hpos : Complex.exp (Complex.I * (θ / 2 : ℂ)) =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) := by
    congr 1
    simp [mul_comm]
  rw [localOnSecond, rz, hneg, hpos]
  simpa using
    (DiagonalizationHelpers.one_kron_diag2
      (Complex.exp (((-θ) / 2) * Complex.I))
      (Complex.exp ((θ / 2) * Complex.I)))

private theorem controlledRzPair_eq_diag4 (α₀ α₁ : ℝ) :
    controlledRzPair α₀ α₁ =
      diag4 (Complex.exp (((-α₀) / 2) * Complex.I))
        (Complex.exp (((-α₁) / 2) * Complex.I))
        (Complex.exp ((α₀ / 2) * Complex.I))
        (Complex.exp ((α₁ / 2) * Complex.I)) := by
  have hneg₀ : Complex.exp (-Complex.I * (α₀ / 2 : ℂ)) =
      Complex.exp (((-α₀) / 2 : ℝ) * Complex.I) := by
    congr 1
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  have hneg₁ : Complex.exp (-Complex.I * (α₁ / 2 : ℂ)) =
      Complex.exp (((-α₁) / 2 : ℝ) * Complex.I) := by
    congr 1
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  rw [controlledRzPair, proj0_eq_diag2, proj1_eq_diag2, rz, rz, hneg₀, hneg₁]
  rw [diag2_kron_diag2, diag2_kron_diag2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag4, mul_comm]

private theorem controlledRzPair_reduction_step (α₀ α₁ : ℝ) :
    let beta : ℝ := (α₀ - α₁) / 2
    let gamma : ℝ := (α₀ + α₁) / 2
    controlledRzPair α₀ α₁ =
      cnot * localOnFirst (rz beta) * cnot * localOnFirst (rz gamma) := by
  let beta : ℝ := (α₀ - α₁) / 2
  let gamma : ℝ := (α₀ + α₁) / 2
  have hconj :
      cnot * localOnFirst (rz beta) * cnot =
        diag4 (Complex.exp (((-beta) / 2) * Complex.I))
          (Complex.exp ((beta / 2) * Complex.I))
          (Complex.exp ((beta / 2) * Complex.I))
          (Complex.exp (((-beta) / 2) * Complex.I)) := by
    calc
      cnot * localOnFirst (rz beta) * cnot
          = cnot *
              diag4 (Complex.exp (((-beta) / 2) * Complex.I))
                (Complex.exp (((-beta) / 2) * Complex.I))
                (Complex.exp ((beta / 2) * Complex.I))
                (Complex.exp ((beta / 2) * Complex.I)) * cnot := by
              rw [localOnFirst_rz_eq]
      _ = diag4 (Complex.exp (((-beta) / 2) * Complex.I))
            (Complex.exp ((beta / 2) * Complex.I))
            (Complex.exp ((beta / 2) * Complex.I))
            (Complex.exp (((-beta) / 2) * Complex.I)) := by
            simpa [cnot, GateHelpers.notc_conjTranspose] using
              (GateHelpers.notc_conj_diag4
                (Complex.exp (((-beta) / 2) * Complex.I))
                (Complex.exp (((-beta) / 2) * Complex.I))
                (Complex.exp ((beta / 2) * Complex.I))
                (Complex.exp ((beta / 2) * Complex.I)))
  calc
    controlledRzPair α₀ α₁
        = diag4 (Complex.exp (((-α₀) / 2) * Complex.I))
            (Complex.exp (((-α₁) / 2) * Complex.I))
            (Complex.exp ((α₀ / 2) * Complex.I))
            (Complex.exp ((α₁ / 2) * Complex.I)) := by
            rw [controlledRzPair_eq_diag4]
    _ = diag4 (Complex.exp (((-beta) / 2) * Complex.I))
          (Complex.exp ((beta / 2) * Complex.I))
          (Complex.exp ((beta / 2) * Complex.I))
          (Complex.exp (((-beta) / 2) * Complex.I)) *
          diag4 (Complex.exp (((-gamma) / 2) * Complex.I))
            (Complex.exp (((-gamma) / 2) * Complex.I))
            (Complex.exp ((gamma / 2) * Complex.I))
            (Complex.exp ((gamma / 2) * Complex.I)) := by
          rw [diag4_mul_diag4]
          congr
          · rw [← Complex.exp_add]
            congr 1
            simp [beta, gamma]
            ring
          · rw [← Complex.exp_add]
            congr 1
            simp [beta, gamma]
            ring
          · rw [← Complex.exp_add]
            congr 1
            simp [beta, gamma]
            ring
          · rw [← Complex.exp_add]
            congr 1
            simp [beta, gamma]
            ring
    _ = cnot * localOnFirst (rz beta) * cnot * localOnFirst (rz gamma) := by
          rw [hconj, localOnFirst_rz_eq]

private theorem liftTopOneQubit_isEmbedded (m : ℕ) (U : Square 2) :
    IsEmbeddedOneQubitGate (m + 1) U (liftTopOneQubit m U) := by
  let p : OneQubitPlacement (m + 1) :=
    { target := 0
      left := 1
      right := 2 ^ m
      dimension_eq := by
        simpa using two_mul_pow_eq_pow_succ m
      permutation := Equiv.refl _ }
  left
  refine ⟨p, ?_⟩
  calc
    liftTopOneQubit m U
        = castSquare (two_mul_pow_eq_pow_succ m)
            (castSquare (show 1 * (2 * 2 ^ m) = 2 * 2 ^ m by simp)
              ((1 : Square 1) ⊗ₖ (U ⊗ₖ (1 : Square (2 ^ m))))) := by
            show castSquare (two_mul_pow_eq_pow_succ m) (U ⊗ₖ (1 : Square (2 ^ m))) =
              castSquare (two_mul_pow_eq_pow_succ m)
                (castSquare (show 1 * (2 * 2 ^ m) = 2 * 2 ^ m by simp)
                  ((1 : Square 1) ⊗ₖ (U ⊗ₖ (1 : Square (2 ^ m)))))
            rw [one_kron_any]
    _ = reindexSquare (Equiv.refl (Fin (2 ^ (m + 1))))
          (castSquare p.dimension_eq
            ((1 : Square 1) ⊗ₖ (U ⊗ₖ (1 : Square (2 ^ m))))) := by
          simp [p, castSquare_trans, reindexSquare]
    _ = p.embed U := by
          rfl

private theorem synthesizes_singleton {N : ℕ} {allowed : Square N → Prop} {U : Square N}
    (hU : allowed U) :
    Synthesizes allowed U := by
  refine ⟨[U], ?_, by simp [circuitMatrix]⟩
  intro gate hgate
  rw [List.mem_singleton] at hgate
  subst hgate
  exact hU

private theorem synthesizes_mul {N : ℕ} {allowed : Square N → Prop}
    {U V : Square N}
    (hU : Synthesizes allowed U) (hV : Synthesizes allowed V) :
    Synthesizes allowed (U * V) := by
  rcases hU with ⟨gatesU, hGatesU, rfl⟩
  rcases hV with ⟨gatesV, hGatesV, rfl⟩
  refine ⟨gatesU ++ gatesV, CircuitOver_append hGatesU hGatesV, ?_⟩
  simp [circuitMatrix_append]

private theorem castFin_val {a b : ℕ} (h : a = b) (x : Fin a) :
    ((Equiv.cast (congrArg Fin h) x).1) = x.1 := by
  cases h
  rfl

noncomputable def topTensorEquiv {A B : ℕ} (e : Fin A ≃ Fin B) :
    Fin (2 * A) ≃ Fin (2 * B) :=
  ((@finProdFinEquiv 2 A).symm.trans ((Equiv.refl (Fin 2)).prodCongr e)).trans
    (@finProdFinEquiv 2 B)

private theorem topTensorEquiv_cast {A B : ℕ} (h : A = B) :
    topTensorEquiv (Equiv.cast (congrArg Fin h)) =
      Equiv.cast (congrArg Fin (congrArg (fun x => 2 * x) h)) := by
  cases h
  ext i
  simp [topTensorEquiv, Nat.mod_add_div]

private theorem one_kron_reindexSquare {A B : ℕ} (e : Fin A ≃ Fin B) (U : Square A) :
    ((1 : Square 2) ⊗ₖ reindexSquare e U) =
      reindexSquare (topTensorEquiv e) ((1 : Square 2) ⊗ₖ U) := by
  ext i j
  simp [TwoControl.kron, reindexSquare, topTensorEquiv,
    Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.kroneckerMap_apply]

private theorem castSquare_reindexSquare {B C : ℕ} (e : Fin B ≃ Fin B)
    (h : B = C) (U : Square B) :
    castSquare h (reindexSquare e U) =
      reindexSquare
        (((Equiv.cast (congrArg Fin h)).symm.trans e).trans (Equiv.cast (congrArg Fin h)))
        (castSquare h U) := by
  cases h
  ext i j
  simp [castSquare, reindexSquare, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

private theorem liftLowerUnitary_eq_kron (m : ℕ) (U : Square (2 ^ m)) :
    liftLowerUnitary m U =
      castSquare (two_mul_pow_eq_pow_succ m) ((1 : Square 2) ⊗ₖ U) := by
  rw [liftLowerUnitary, firstQubitBlockDiag, unblockify_fromBlocks]
  simp [TwoControl.zero_kron_right]
  rw [← BlockHelpers.proj0_add_proj1, kron_add_left]

@[simp] private theorem fin_cases_one_const {α : Type*} (x y : α) :
    Fin.cases x (fun _ => y) (1 : Fin 2) = y := by
  rfl

private noncomputable def splitControlIndex (m : ℕ) (b : Fin 2) (r : Fin (2 ^ m)) :
    Fin (2 ^ (m + 1)) :=
  (Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ m))) (@finProdFinEquiv 2 (2 ^ m) (b, r))

@[simp] private theorem splitControlIndex_cast_symm (m : ℕ) (b : Fin 2) (r : Fin (2 ^ m)) :
    (Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ m))).symm (splitControlIndex m b r) =
      @finProdFinEquiv 2 (2 ^ m) (b, r) := by
  unfold splitControlIndex
  exact (Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ m))).left_inv _

@[simp] private theorem splitControlIndex_eq_iff (m : ℕ)
    {b b' : Fin 2} {r s : Fin (2 ^ m)} :
    splitControlIndex m b r = splitControlIndex m b' s ↔ b = b' ∧ r = s := by
  constructor
  · intro h
    have h' := congrArg (fun x =>
      (Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ m))).symm x) h
    simp [splitControlIndex] at h'
    exact h'
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] private theorem pairBlockEquiv_outer_apply (m : ℕ) (u v : Fin 2) (r : Fin (2 ^ m)) :
    (Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ (m + 1)))).symm
      ((pairBlockEquiv m) (@finProdFinEquiv 2 2 (u, v), r)) =
    @finProdFinEquiv 2 (2 ^ (m + 1)) (u, splitControlIndex m v r) := by
  let h24 : 4 * 2 ^ m = 2 * (2 ^ (m + 1)) :=
    by
      have h4 : 4 = 2 * 2 := by norm_num
      calc
        4 * 2 ^ m = (2 * 2) * 2 ^ m := by rw [h4]
        _ = 2 * (2 * 2 ^ m) := by rw [Nat.mul_assoc]
        _ = 2 * (2 ^ (m + 1)) := by rw [two_mul_pow_eq_pow_succ m]
  unfold pairBlockEquiv splitControlIndex
  simp [Equiv.trans_apply]
  rw [castFin_core_cast_symm_local (four_mul_pow_eq_pow_add_two m) (two_mul_pow_eq_pow_succ (m + 1))]
  change cast (congrArg Fin h24) (@finProdFinEquiv 4 (2 ^ m) (@finProdFinEquiv 2 2 (u, v), r)) =
    @finProdFinEquiv 2 (2 ^ (m + 1)) (u,
      (Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ m))) (@finProdFinEquiv 2 (2 ^ m) (v, r)))
  rw [← finProd_assoc_2_encoded_local (n := 2) (p := 2 ^ m) u v r]
  simpa [h24] using
    (finProdFinEquiv_cast_right_local (hpq := two_mul_pow_eq_pow_succ m) u
      (@finProdFinEquiv 2 (2 ^ m) (v, r)))

@[simp] private theorem pairBlockEquiv_outer_symm (m : ℕ) (a : Fin 4) (r : Fin (2 ^ m)) :
    (@finProdFinEquiv 2 (2 ^ (m + 1))).symm
      ((Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ (m + 1)))).symm
        ((pairBlockEquiv m) (a, r))) =
      (((@finProdFinEquiv 2 2).symm a).1,
        splitControlIndex m ((@finProdFinEquiv 2 2).symm a).2 r) := by
  obtain ⟨u, v, rfl⟩ : ∃ u v, @finProdFinEquiv 2 2 (u, v) = a := by
    refine ⟨((@finProdFinEquiv 2 2).symm a).1, ((@finProdFinEquiv 2 2).symm a).2, ?_⟩
    exact (@finProdFinEquiv 2 2).apply_symm_apply a
  rw [pairBlockEquiv_outer_apply]
  simp

@[simp] private theorem pairBlockEquiv_outer_divNat (m : ℕ) (a : Fin 4) (r : Fin (2 ^ m)) :
    ((Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ (m + 1)))).symm
      ((pairBlockEquiv m) (a, r))).divNat = ((@finProdFinEquiv 2 2).symm a).1 := by
  change (((@finProdFinEquiv 2 (2 ^ (m + 1))).symm
      ((Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ (m + 1)))).symm
        ((pairBlockEquiv m) (a, r)))).1) = _
  rw [pairBlockEquiv_outer_symm]

@[simp] private theorem pairBlockEquiv_outer_modNat (m : ℕ) (a : Fin 4) (r : Fin (2 ^ m)) :
    ((Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ (m + 1)))).symm
      ((pairBlockEquiv m) (a, r))).modNat = splitControlIndex m ((@finProdFinEquiv 2 2).symm a).2 r := by
  change (((@finProdFinEquiv 2 (2 ^ (m + 1))).symm
      ((Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ (m + 1)))).symm
        ((pairBlockEquiv m) (a, r)))).2) = _
  rw [pairBlockEquiv_outer_symm]

@[simp] private theorem finTwoBlockEquiv_pairBlockEquiv_outer (m : ℕ) (a : Fin 4) (r : Fin (2 ^ m)) :
    finTwoBlockEquiv (2 ^ (m + 1))
      ((Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ (m + 1)))).symm
        ((pairBlockEquiv m) (a, r))) =
      Fin.cases
        (Sum.inl (splitControlIndex m ((@finProdFinEquiv 2 2).symm a).2 r))
        (fun _ => Sum.inr (splitControlIndex m ((@finProdFinEquiv 2 2).symm a).2 r))
        ((@finProdFinEquiv 2 2).symm a).1 := by
  obtain ⟨u, v, rfl⟩ : ∃ u v, @finProdFinEquiv 2 2 (u, v) = a := by
    refine ⟨((@finProdFinEquiv 2 2).symm a).1, ((@finProdFinEquiv 2 2).symm a).2, ?_⟩
    exact (@finProdFinEquiv 2 2).apply_symm_apply a
  change finTwoProdSumEquiv (2 ^ (m + 1))
      ((@finProdFinEquiv 2 (2 ^ (m + 1))).symm
        ((Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ (m + 1)))).symm
          ((pairBlockEquiv m) (@finProdFinEquiv 2 2 (u, v), r)))) = _
  rw [pairBlockEquiv_outer_symm]
  fin_cases u <;> rfl

@[simp] private theorem finTwoBlockEquiv_pairBlockEquiv_outer_modNat (m : ℕ) (a : Fin 4)
    (r : Fin (2 ^ m)) :
    finTwoBlockEquiv (2 ^ m)
      ((Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ m))).symm
        (((Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ (m + 1)))).symm
          ((pairBlockEquiv m) (a, r))).modNat)) =
      Fin.cases (Sum.inl r) (fun _ => Sum.inr r) ((@finProdFinEquiv 2 2).symm a).2 := by
  rw [pairBlockEquiv_outer_modNat]
  obtain ⟨u, v, rfl⟩ : ∃ u v, @finProdFinEquiv 2 2 (u, v) = a := by
    refine ⟨((@finProdFinEquiv 2 2).symm a).1, ((@finProdFinEquiv 2 2).symm a).2, ?_⟩
    exact (@finProdFinEquiv 2 2).apply_symm_apply a
  fin_cases u <;> fin_cases v <;> simp [splitControlIndex_cast_symm] <;> rfl

private theorem controlledRzFamily_succ_eq_pairBlockDiagonal (m : ℕ)
    (α : Fin (2 ^ (m + 1)) → ℝ) :
    controlledRzFamily (m + 1) α =
      pairBlockDiagonal m (fun r =>
        controlledRzPair (α (splitControlIndex m 0 r)) (α (splitControlIndex m 1 r))) := by
  ext i j
  obtain ⟨⟨a, r⟩, hi⟩ := (pairBlockEquiv m).surjective i
  obtain ⟨⟨b, s⟩, hj⟩ := (pairBlockEquiv m).surjective j
  symm at hi
  symm at hj
  subst i
  subst j
  obtain ⟨u, v, rfl⟩ : ∃ u v, @finProdFinEquiv 2 2 (u, v) = a := by
    refine ⟨((@finProdFinEquiv 2 2).symm a).1, ((@finProdFinEquiv 2 2).symm a).2, ?_⟩
    exact (@finProdFinEquiv 2 2).apply_symm_apply a
  obtain ⟨u', v', rfl⟩ : ∃ u' v', @finProdFinEquiv 2 2 (u', v') = b := by
    refine ⟨((@finProdFinEquiv 2 2).symm b).1, ((@finProdFinEquiv 2 2).symm b).2, ?_⟩
    exact (@finProdFinEquiv 2 2).apply_symm_apply b
  by_cases hrs : r = s
  · subst s
    fin_cases u <;> fin_cases v <;> fin_cases u' <;> fin_cases v'
    all_goals
      simp [controlledRzFamily, firstQubitBlockDiag, castSquare, reindexSquare,
        Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, unblockify,
        controlledRzPair, rz, proj0, proj1, ketbra, ket0, ket1, diag2,
        TwoControl.kron, Matrix.kroneckerMap_apply]
  · fin_cases u <;> fin_cases v <;> fin_cases u' <;> fin_cases v'
    all_goals
      simp [controlledRzFamily, firstQubitBlockDiag, castSquare, reindexSquare,
        Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, unblockify,
        controlledRzPair, rz, proj0, proj1, ketbra, ket0, ket1, diag2, hrs,
        TwoControl.kron, Matrix.kroneckerMap_apply]

private theorem liftLower_controlledRzFamily_eq_pairBlockDiagonal (m : ℕ)
    (β : Fin (2 ^ m) → ℝ) :
    liftLowerUnitary (m + 1) (controlledRzFamily m β) =
      pairBlockDiagonal m (fun r => localOnSecond (rz (β r))) := by
  ext i j
  obtain ⟨⟨a, r⟩, hi⟩ := (pairBlockEquiv m).surjective i
  obtain ⟨⟨b, s⟩, hj⟩ := (pairBlockEquiv m).surjective j
  symm at hi
  symm at hj
  subst i
  subst j
  obtain ⟨u, v, rfl⟩ : ∃ u v, @finProdFinEquiv 2 2 (u, v) = a := by
    refine ⟨((@finProdFinEquiv 2 2).symm a).1, ((@finProdFinEquiv 2 2).symm a).2, ?_⟩
    exact (@finProdFinEquiv 2 2).apply_symm_apply a
  obtain ⟨u', v', rfl⟩ : ∃ u' v', @finProdFinEquiv 2 2 (u', v') = b := by
    refine ⟨((@finProdFinEquiv 2 2).symm b).1, ((@finProdFinEquiv 2 2).symm b).2, ?_⟩
    exact (@finProdFinEquiv 2 2).apply_symm_apply b
  by_cases hrs : r = s
  · subst s
    fin_cases u <;> fin_cases v <;> fin_cases u' <;> fin_cases v'
    all_goals
      simp [liftLowerUnitary, firstQubitBlockDiag, controlledRzFamily, castSquare,
        reindexSquare, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
        unblockify, localOnSecond, rz, diag2,
        TwoControl.kron, Matrix.kroneckerMap_apply]
  · fin_cases u <;> fin_cases v <;> fin_cases u' <;> fin_cases v'
    all_goals
      simp [liftLowerUnitary, firstQubitBlockDiag, controlledRzFamily, castSquare,
        reindexSquare, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
        unblockify, localOnSecond, rz, diag2, hrs,
        TwoControl.kron, Matrix.kroneckerMap_apply]

private theorem liftMiddle_controlledRzFamily_eq_pairBlockDiagonal (m : ℕ)
    (β : Fin (2 ^ m) → ℝ) :
    liftMiddleUnitary m (controlledRzFamily m β) =
      pairBlockDiagonal m (fun r => localOnFirst (rz (β r))) := by
  rw [liftMiddleUnitary, topTwoUnitary_eq_pairBlockDiagonal,
    liftLower_controlledRzFamily_eq_pairBlockDiagonal]
  rw [← pairBlockDiagonal_mul, ← pairBlockDiagonal_mul]
  change pairBlockDiagonal m (fun r => swap2 * localOnSecond (rz (β r)) * swap2) =
    pairBlockDiagonal m (fun r => localOnFirst (rz (β r)))
  apply congrArg
  funext r
  simpa [localOnFirst, localOnSecond] using SwapHelpers.swap2_conj_kron_left (rz (β r))

/-- Möttönen-style reduction of a uniformly controlled `R_z` family by one
control wire. The distinguished control wire stays between the target wire and
the remaining control bundle, so the smaller families are inserted with a
middle-wire lift and separated by two embedded CNOT gates. -/
theorem controlled_rz_reduction_step (m : ℕ)
    (α : Fin (2 ^ (m + 1)) → ℝ) :
    ∃ β γ : Fin (2 ^ m) → ℝ,
      ∃ CX : Square (2 ^ (m + 2)),
        IsEmbeddedTwoQubitGate (m + 2) cnot CX ∧
        controlledRzFamily (m + 1) α =
          CX * liftMiddleUnitary m (controlledRzFamily m β) *
            CX * liftMiddleUnitary m (controlledRzFamily m γ) := by
  let β : Fin (2 ^ m) → ℝ := fun r =>
    (α (splitControlIndex m 0 r) - α (splitControlIndex m 1 r)) / 2
  let γ : Fin (2 ^ m) → ℝ := fun r =>
    (α (splitControlIndex m 0 r) + α (splitControlIndex m 1 r)) / 2
  refine ⟨β, γ, topTwoUnitary m cnot, ⟨⟨topTwoPlacement m, rfl⟩, ?_⟩⟩
  rw [controlledRzFamily_succ_eq_pairBlockDiagonal,
    topTwoUnitary_eq_pairBlockDiagonal,
    liftMiddle_controlledRzFamily_eq_pairBlockDiagonal,
    liftMiddle_controlledRzFamily_eq_pairBlockDiagonal]
  rw [← pairBlockDiagonal_mul, ← pairBlockDiagonal_mul, ← pairBlockDiagonal_mul]
  congr 1
  funext r
  simpa [β, γ, splitControlIndex] using
    (controlledRzPair_reduction_step (α (splitControlIndex m 0 r)) (α (splitControlIndex m 1 r)))

private theorem finProd_assoc_2_encoded (n p : ℕ) (a : Fin 2) (b : Fin n) (c : Fin p) :
    (Equiv.cast (congrArg Fin ((Nat.mul_assoc 2 n p).symm)))
      (@finProdFinEquiv 2 (n * p) (a, @finProdFinEquiv n p (b, c))) =
    @finProdFinEquiv (2 * n) p (@finProdFinEquiv 2 n (a, b), c) := by
  apply Fin.eq_of_val_eq
  rw [castFin_val]
  simp [finProdFinEquiv, Nat.mul_assoc]
  · ring
  · simp [Nat.mul_assoc]

private theorem one_finProdFinEquiv {l : ℕ} (a a' : Fin 2) (b b' : Fin l) :
    (1 : Square (2 * l)) (@finProdFinEquiv 2 l (a, b)) (@finProdFinEquiv 2 l (a', b')) =
      (1 : Square 2) a a' * ((1 : Square l) b b') := by
  by_cases haa : a = a'
  · subst a'
    by_cases hbb : b = b'
    · subst b'
      simp
    · have hneq : (@finProdFinEquiv 2 l (a, b) : Fin (2 * l)) ≠ @finProdFinEquiv 2 l (a, b') := by
        intro h
        apply hbb
        exact congrArg Prod.snd ((@finProdFinEquiv 2 l).injective h)
      simp [hneq, hbb]
  · have hneq : (@finProdFinEquiv 2 l (a, b) : Fin (2 * l)) ≠ @finProdFinEquiv 2 l (a', b') := by
      intro h
      apply haa
      exact congrArg Prod.fst ((@finProdFinEquiv 2 l).injective h)
    simp [hneq, haa]

private theorem one_kron_assoc_identity (l p : ℕ) (W : Square p) :
    castSquare ((Nat.mul_assoc 2 l p).symm) (((1 : Square 2) ⊗ₖ ((1 : Square l) ⊗ₖ W))) =
      ((1 : Square (2 * l)) ⊗ₖ W) := by
  ext i j
  obtain ⟨⟨ab, c⟩, rfl⟩ := (@finProdFinEquiv (2 * l) p).surjective i
  obtain ⟨⟨ab', c'⟩, rfl⟩ := (@finProdFinEquiv (2 * l) p).surjective j
  obtain ⟨⟨a, b⟩, rfl⟩ := (@finProdFinEquiv 2 l).surjective ab
  obtain ⟨⟨a', b'⟩, rfl⟩ := (@finProdFinEquiv 2 l).surjective ab'
  have hi' :
      (Equiv.cast (congrArg Fin ((Nat.mul_assoc 2 l p).symm))).symm
        (@finProdFinEquiv (2 * l) p (@finProdFinEquiv 2 l (a, b), c)) =
      @finProdFinEquiv 2 (l * p) (a, @finProdFinEquiv l p (b, c)) := by
    exact (Equiv.symm_apply_eq _).2 (finProd_assoc_2_encoded l p a b c).symm
  have hj' :
      (Equiv.cast (congrArg Fin ((Nat.mul_assoc 2 l p).symm))).symm
        (@finProdFinEquiv (2 * l) p (@finProdFinEquiv 2 l (a', b'), c')) =
      @finProdFinEquiv 2 (l * p) (a', @finProdFinEquiv l p (b', c')) := by
    exact (Equiv.symm_apply_eq _).2 (finProd_assoc_2_encoded l p a' b' c').symm
  calc
    castSquare ((Nat.mul_assoc 2 l p).symm) (((1 : Square 2) ⊗ₖ ((1 : Square l) ⊗ₖ W)))
        (@finProdFinEquiv (2 * l) p (@finProdFinEquiv 2 l (a, b), c))
        (@finProdFinEquiv (2 * l) p (@finProdFinEquiv 2 l (a', b'), c'))
      = ((1 : Square 2) ⊗ₖ ((1 : Square l) ⊗ₖ W))
          (@finProdFinEquiv 2 (l * p) (a, @finProdFinEquiv l p (b, c)))
          (@finProdFinEquiv 2 (l * p) (a', @finProdFinEquiv l p (b', c'))) := by
            simp [castSquare, reindexSquare, Matrix.reindexAlgEquiv_apply, hi', hj']
    _ = (1 : Square 2) a a' * (((1 : Square l) ⊗ₖ W) (@finProdFinEquiv l p (b, c))
          (@finProdFinEquiv l p (b', c'))) := by
          simpa using
            (TwoControl.kron_apply (A := (1 : Square 2)) (B := ((1 : Square l) ⊗ₖ W))
              a (@finProdFinEquiv l p (b, c)) a' (@finProdFinEquiv l p (b', c'))).symm
    _ = (1 : Square 2) a a' * ((1 : Square l) b b' * W c c') := by
          congr 1
          simpa using (TwoControl.kron_apply (A := (1 : Square l)) (B := W) b c b' c')
    _ = ((1 : Square 2) a a' * (1 : Square l) b b') * W c c' := by
          simp [mul_assoc]
    _ = (1 : Square (2 * l)) (@finProdFinEquiv 2 l (a, b)) (@finProdFinEquiv 2 l (a', b')) *
          W c c' := by
          rw [one_finProdFinEquiv]
    _ = ((1 : Square (2 * l)) ⊗ₖ W)
          (@finProdFinEquiv (2 * l) p (@finProdFinEquiv 2 l (a, b), c))
          (@finProdFinEquiv (2 * l) p (@finProdFinEquiv 2 l (a', b'), c')) := by
          simpa using
            (TwoControl.kron_apply (A := (1 : Square (2 * l))) (B := W)
              (@finProdFinEquiv 2 l (a, b)) c (@finProdFinEquiv 2 l (a', b')) c')

noncomputable def lowerLiftPermutation (m : ℕ) (e : Fin (2 ^ m) ≃ Fin (2 ^ m)) :
    Fin (2 ^ (m + 1)) ≃ Fin (2 ^ (m + 1)) :=
  ((Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ m))).symm.trans (topTensorEquiv e)).trans
    (Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ m)))

noncomputable def lowerOneQubitPlacement {m : ℕ} (p : OneQubitPlacement m) :
    OneQubitPlacement (m + 1) :=
  { target := ⟨p.target.1 + 1, Nat.succ_lt_succ p.target.2⟩
    left := 2 * p.left
    right := p.right
    dimension_eq :=
      (Nat.mul_assoc 2 p.left (2 * p.right)).trans
        ((congrArg (fun x => 2 * x) p.dimension_eq).trans (two_mul_pow_eq_pow_succ m))
    permutation := lowerLiftPermutation m p.permutation }

noncomputable def lowerTwoQubitPlacement {m : ℕ} (p : TwoQubitPlacement m) :
    TwoQubitPlacement (m + 1) :=
  { first := ⟨p.first.1 + 1, Nat.succ_lt_succ p.first.2⟩
    second := ⟨p.second.1 + 1, Nat.succ_lt_succ p.second.2⟩
    distinct := by
      intro h
      apply p.distinct
      apply Fin.ext
      exact Nat.succ.inj (congrArg Fin.val h)
    left := 2 * p.left
    right := p.right
    dimension_eq :=
      (Nat.mul_assoc 2 p.left (4 * p.right)).trans
        ((congrArg (fun x => 2 * x) p.dimension_eq).trans (two_mul_pow_eq_pow_succ m))
    permutation := lowerLiftPermutation m p.permutation }

private theorem liftLower_oneQubit_embed {m : ℕ} (p : OneQubitPlacement m) (U : Square 2) :
    liftLowerUnitary m (p.embed U) = (lowerOneQubitPlacement p).embed U := by
  rw [liftLowerUnitary_eq_kron, OneQubitPlacement.embed, OneQubitPlacement.embed]
  have hCast0 :=
    one_kron_reindexSquare (e := Equiv.cast (congrArg Fin p.dimension_eq)) (U := p.tensor U)
  rw [topTensorEquiv_cast p.dimension_eq] at hCast0
  have hCast :
      ((1 : Square 2) ⊗ₖ castSquare p.dimension_eq (p.tensor U)) =
        castSquare (congrArg (fun x => 2 * x) p.dimension_eq) ((1 : Square 2) ⊗ₖ p.tensor U) := by
    simpa [castSquare] using hCast0
  rw [one_kron_reindexSquare, hCast]
  rw [castSquare_reindexSquare]
  rw [castSquare_trans]
  have hTensor :
      castSquare ((Nat.mul_assoc 2 p.left (2 * p.right)).symm) ((1 : Square 2) ⊗ₖ p.tensor U) =
        (lowerOneQubitPlacement p).tensor U := by
    simpa [lowerOneQubitPlacement, OneQubitPlacement.tensor] using
      one_kron_assoc_identity p.left (2 * p.right) (U ⊗ₖ (1 : Square p.right))
  calc
    reindexSquare (lowerLiftPermutation m p.permutation)
        (castSquare ((congrArg (fun x => 2 * x) p.dimension_eq).trans (two_mul_pow_eq_pow_succ m))
          ((1 : Square 2) ⊗ₖ p.tensor U))
      = reindexSquare (lowerLiftPermutation m p.permutation)
          (castSquare (lowerOneQubitPlacement p).dimension_eq ((lowerOneQubitPlacement p).tensor U)) := by
            rw [← castSquare_trans ((Nat.mul_assoc 2 p.left (2 * p.right)).symm)
              (lowerOneQubitPlacement p).dimension_eq ((1 : Square 2) ⊗ₖ p.tensor U)]
            rw [hTensor]
            simp [lowerOneQubitPlacement]
    _ = (lowerOneQubitPlacement p).embed U := by
          rfl

private theorem liftLower_twoQubit_embed {m : ℕ} (p : TwoQubitPlacement m) (U : Square 4) :
    liftLowerUnitary m (p.embed U) = (lowerTwoQubitPlacement p).embed U := by
  rw [liftLowerUnitary_eq_kron, TwoQubitPlacement.embed, TwoQubitPlacement.embed]
  have hCast0 :=
    one_kron_reindexSquare (e := Equiv.cast (congrArg Fin p.dimension_eq)) (U := p.tensor U)
  rw [topTensorEquiv_cast p.dimension_eq] at hCast0
  have hCast :
      ((1 : Square 2) ⊗ₖ castSquare p.dimension_eq (p.tensor U)) =
        castSquare (congrArg (fun x => 2 * x) p.dimension_eq) ((1 : Square 2) ⊗ₖ p.tensor U) := by
    simpa [castSquare] using hCast0
  rw [one_kron_reindexSquare, hCast]
  rw [castSquare_reindexSquare]
  rw [castSquare_trans]
  have hTensor :
      castSquare ((Nat.mul_assoc 2 p.left (4 * p.right)).symm) ((1 : Square 2) ⊗ₖ p.tensor U) =
        (lowerTwoQubitPlacement p).tensor U := by
    simpa [lowerTwoQubitPlacement, TwoQubitPlacement.tensor] using
      one_kron_assoc_identity p.left (4 * p.right) (U ⊗ₖ (1 : Square p.right))
  calc
    reindexSquare (lowerLiftPermutation m p.permutation)
        (castSquare ((congrArg (fun x => 2 * x) p.dimension_eq).trans (two_mul_pow_eq_pow_succ m))
          ((1 : Square 2) ⊗ₖ p.tensor U))
      = reindexSquare (lowerLiftPermutation m p.permutation)
          (castSquare (lowerTwoQubitPlacement p).dimension_eq ((lowerTwoQubitPlacement p).tensor U)) := by
            rw [← castSquare_trans ((Nat.mul_assoc 2 p.left (4 * p.right)).symm)
              (lowerTwoQubitPlacement p).dimension_eq ((1 : Square 2) ⊗ₖ p.tensor U)]
            rw [hTensor]
            simp [lowerTwoQubitPlacement]
    _ = (lowerTwoQubitPlacement p).embed U := by
          rfl

private theorem liftLower_isEmbeddedOneQubit {m : ℕ} {U : Square 2} {E : Square (2 ^ m)}
    (hE : IsEmbeddedOneQubitGate m U E) :
    IsEmbeddedOneQubitGate (m + 1) U (liftLowerUnitary m E) := by
  rcases hE with hDirect | hRest
  · rcases hDirect with ⟨p, rfl⟩
    rw [liftLower_oneQubit_embed]
    exact IsEmbeddedOneQubitGate.of_placement (lowerOneQubitPlacement p) U
  · rcases hRest with hFirst | hSecond
    · rcases hFirst with ⟨p, rfl⟩
      rw [liftLower_twoQubit_embed]
      exact IsEmbeddedOneQubitGate.of_twoQubit_first (lowerTwoQubitPlacement p) U
    · rcases hSecond with ⟨p, rfl⟩
      rw [liftLower_twoQubit_embed]
      exact IsEmbeddedOneQubitGate.of_twoQubit_second (lowerTwoQubitPlacement p) U

private theorem liftLower_isEmbeddedTwoQubit {m : ℕ} {U : Square 4} {E : Square (2 ^ m)}
    (hE : IsEmbeddedTwoQubitGate m U E) :
    IsEmbeddedTwoQubitGate (m + 1) U (liftLowerUnitary m E) := by
  rcases hE with ⟨p, rfl⟩
  rw [liftLower_twoQubit_embed]
  exact IsEmbeddedTwoQubitGate.of_placement (lowerTwoQubitPlacement p) U

private theorem liftLower_easyGate {m : ℕ} {E : Square (2 ^ m)}
    (hE : EasyGate m E) :
    EasyGate (m + 1) (liftLowerUnitary m E) := by
  rcases hE with hTwo | hRest
  · rcases hTwo with ⟨V, hV, hEmbed⟩
    exact EasyGate.of_embedded_two_qubit hV (liftLower_isEmbeddedTwoQubit hEmbed)
  · rcases hRest with hHadamard | hRest
    · exact EasyGate.hadamard (liftLower_isEmbeddedOneQubit hHadamard)
    · rcases hRest with hS | hRest
      · exact EasyGate.phaseS (liftLower_isEmbeddedOneQubit hS)
      · rcases hRest with hSdagger | hRz
        · exact EasyGate.phaseSdagger (liftLower_isEmbeddedOneQubit hSdagger)
        · rcases hRz with ⟨θ, hRz⟩
          exact EasyGate.rz θ (liftLower_isEmbeddedOneQubit hRz)

@[simp] private theorem liftLowerUnitary_one (m : ℕ) :
    liftLowerUnitary m (1 : Square (2 ^ m)) = 1 := by
  rw [liftLowerUnitary_eq_kron, TwoControl.one_kron_one 2 (2 ^ m)]
  simp

private theorem liftLowerUnitary_mul (m : ℕ) (U V : Square (2 ^ m)) :
    liftLowerUnitary m (U * V) = liftLowerUnitary m U * liftLowerUnitary m V := by
  have hKron :
      ((1 : Square 2) ⊗ₖ (U * V)) =
        ((1 : Square 2) ⊗ₖ U) * ((1 : Square 2) ⊗ₖ V) := by
    simpa using
      (KronHelpers.kron_mul_reindex (A := (1 : Square 2)) (B := (1 : Square 2))
        (C := U) (D := V))
  rw [liftLowerUnitary_eq_kron, liftLowerUnitary_eq_kron, liftLowerUnitary_eq_kron, hKron]
  rw [castSquare_mul]

private theorem circuitMatrix_map_liftLower (m : ℕ) (gates : List (Square (2 ^ m))) :
    circuitMatrix (gates.map (liftLowerUnitary m)) = liftLowerUnitary m (circuitMatrix gates) := by
  induction gates with
  | nil =>
      simp [circuitMatrix]
  | cons gate gates ih =>
    rw [List.map, circuitMatrix_cons, ih, circuitMatrix_cons, liftLowerUnitary_mul]

private theorem synthesizes_liftLower {m : ℕ} {W : Square (2 ^ m)}
    (hW : Synthesizes (EasyGate m) W) :
    Synthesizes (EasyGate (m + 1)) (liftLowerUnitary m W) := by
  rcases hW with ⟨gates, hGates, hEq⟩
  refine ⟨gates.map (liftLowerUnitary m), ?_, ?_⟩
  · intro gate hgate
    rcases List.mem_map.1 hgate with ⟨gate', hgate', rfl⟩
    exact liftLower_easyGate (hGates gate' hgate')
  · rw [hEq]
    symm
    exact circuitMatrix_map_liftLower m gates

private theorem topTwoUnitary_isEmbeddedTwoQubit (m : ℕ) (U : Square 4) :
    IsEmbeddedTwoQubitGate (m + 2) U (topTwoUnitary m U) := by
  exact IsEmbeddedTwoQubitGate.of_placement (topTwoPlacement m) U

private theorem topTwoUnitary_easyGate {m : ℕ} {U : Square 4}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    EasyGate (m + 2) (topTwoUnitary m U) := by
  exact EasyGate.of_embedded_two_qubit hU (topTwoUnitary_isEmbeddedTwoQubit m U)

private theorem synthesizes_liftMiddle {m : ℕ} {W : Square (2 ^ (m + 1))}
    (hW : Synthesizes (EasyGate (m + 1)) W) :
    Synthesizes (EasyGate (m + 2)) (liftMiddleUnitary m W) := by
  have hSwap : Synthesizes (EasyGate (m + 2)) (topTwoUnitary m swap2) := by
    exact synthesizes_singleton (topTwoUnitary_easyGate SwapHelpers.swap2_unitary)
  have hLower : Synthesizes (EasyGate (m + 2)) (liftLowerUnitary (m + 1) W) := by
    exact synthesizes_liftLower hW
  rw [liftMiddleUnitary]
  simpa [mul_assoc] using synthesizes_mul (synthesizes_mul hSwap hLower) hSwap

private theorem liftTopOneQubit_zero (U : Square 2) :
    liftTopOneQubit 0 U = U := by
  simpa [liftTopOneQubit] using two_kron_one U

private theorem firstQubitBlockDiag_unitary_factors {m : ℕ} {A D : Square (2 ^ m)}
    (h : firstQubitBlockDiag m A D ∈ Matrix.unitaryGroup (Fin (2 ^ (m + 1))) ℂ) :
    A ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ ∧ D ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
  let e : Fin (2 * 2 ^ m) ≃ Fin (2 ^ (m + 1)) :=
    Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ m))
  have hReindexed :
      reindexSquare e (unblockify (Matrix.fromBlocks A 0 0 D)) ∈
        Matrix.unitaryGroup (Fin (2 ^ (m + 1))) ℂ := by
    simpa [firstQubitBlockDiag, castSquare, e] using h
  have hUnblocked :
      unblockify (Matrix.fromBlocks A 0 0 D) ∈ Matrix.unitaryGroup (Fin (2 * 2 ^ m)) ℂ := by
    have hSymm := reindexSquare_mem_unitaryGroup (e := e.symm) hReindexed
    simpa [e, reindexSquare, Matrix.reindex_apply] using hSymm
  have hBlock :
      Matrix.fromBlocks A 0 0 D ∈ Matrix.unitaryGroup (Fin (2 ^ m) ⊕ Fin (2 ^ m)) ℂ := by
    simpa using (blockify_mem_unitaryGroup_iff (n := 2 ^ m)
      (U := unblockify (Matrix.fromBlocks A 0 0 D))).2 hUnblocked
  exact BlockHelpers.block_diagonal_unitary A D hBlock

/-- Recursive synthesis of uniformly controlled `R_z` families into the easy
gate set. -/
theorem synthesizes_controlled_rz_family (m : ℕ)
    (α : Fin (2 ^ m) → ℝ) :
    Synthesizes (EasyGate (m + 1)) (controlledRzFamily m α) := by
  induction m with
  | zero =>
      have hDiag0 :
          Matrix.diagonal (fun i : Fin 1 => Complex.exp (-Complex.I * (α i / 2))) =
            Complex.exp (-Complex.I * (α 0 / 2)) • (1 : Square 1) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      have hDiag1 :
          Matrix.diagonal (fun i : Fin 1 => Complex.exp (Complex.I * (α i / 2))) =
            Complex.exp (Complex.I * (α 0 / 2)) • (1 : Square 1) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      have hBlocks :
          castSquare (two_mul_pow_eq_pow_succ 0)
            ((proj0 ⊗ₖ Matrix.diagonal (fun i : Fin 1 => Complex.exp (-Complex.I * (α i / 2)))) +
              proj01 ⊗ₖ (0 : Square 1) + proj10 ⊗ₖ (0 : Square 1) +
              proj1 ⊗ₖ Matrix.diagonal (fun i : Fin 1 => Complex.exp (Complex.I * (α i / 2)))) =
            castSquare (two_mul_pow_eq_pow_succ 0)
              ((proj0 ⊗ₖ (Complex.exp (-Complex.I * (α 0 / 2)) • (1 : Square 1))) +
                proj01 ⊗ₖ (0 : Square 1) + proj10 ⊗ₖ (0 : Square 1) +
                proj1 ⊗ₖ (Complex.exp (Complex.I * (α 0 / 2)) • (1 : Square 1))) := by
        rw [hDiag0, hDiag1]
      have hBase : controlledRzFamily 0 α = rz (α 0) := by
        rw [controlledRzFamily, firstQubitBlockDiag, unblockify_fromBlocks]
        exact hBlocks.trans <| by
          rw [KronHelpers.kron_smul_right, KronHelpers.kron_smul_right]
          rw [two_kron_one, two_kron_one]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [rz, diag2, proj0, proj1, proj01, proj10, ketbra, ket0, ket1,
              castSquare, reindexSquare, Matrix.reindex_apply, TwoControl.kron]
      rw [hBase, ← liftTopOneQubit_zero (rz (α 0))]
      exact synthesizes_singleton (EasyGate.rz (α 0) (liftTopOneQubit_isEmbedded 0 (rz (α 0))))
  | succ m ih =>
      rcases controlled_rz_reduction_step m α with ⟨β, γ, CX, hCX, hEq⟩
      have hCX' : Synthesizes (EasyGate (m + 2)) CX := by
        exact synthesizes_singleton (EasyGate.of_embedded_two_qubit cnot_mem_unitaryGroup hCX)
      have hβ : Synthesizes (EasyGate (m + 1)) (controlledRzFamily m β) := ih β
      have hγ : Synthesizes (EasyGate (m + 1)) (controlledRzFamily m γ) := ih γ
      have hβLift :
          Synthesizes (EasyGate (m + 2))
            (liftMiddleUnitary m (controlledRzFamily m β)) := by
        exact synthesizes_liftMiddle hβ
      have hγLift :
          Synthesizes (EasyGate (m + 2))
            (liftMiddleUnitary m (controlledRzFamily m γ)) := by
        exact synthesizes_liftMiddle hγ
      rw [hEq]
      simpa [mul_assoc] using
        synthesizes_mul
          (synthesizes_mul
            (synthesizes_mul hCX' hβLift)
            hCX')
          hγLift

/-- Recursive synthesis of uniformly controlled `R_y` families into the easy
gate set, via the `R_y`-to-`R_z` conversion. -/
theorem synthesizes_controlled_ry_family (m : ℕ)
    (θ : Fin (2 ^ m) → ℝ) :
    Synthesizes (EasyGate (m + 1)) (controlledRyFamily m θ) := by
  rw [controlled_ry_family_via_controlled_rz]
  have hSdagger :
      Synthesizes (EasyGate (m + 1)) (liftTopOneQubit m phaseSdagger) := by
    exact synthesizes_singleton (EasyGate.phaseSdagger (liftTopOneQubit_isEmbedded m phaseSdagger))
  have hHadamard :
      Synthesizes (EasyGate (m + 1)) (liftTopOneQubit m hadamard2) := by
    exact synthesizes_singleton (EasyGate.hadamard (liftTopOneQubit_isEmbedded m hadamard2))
  have hRz :
      Synthesizes (EasyGate (m + 1)) (controlledRzFamily m (fun i => - θ i)) := by
    exact synthesizes_controlled_rz_family m (fun i => - θ i)
  have hS : Synthesizes (EasyGate (m + 1)) (liftTopOneQubit m phaseS) := by
    exact synthesizes_singleton (EasyGate.phaseS (liftTopOneQubit_isEmbedded m phaseS))
  exact synthesizes_mul
    (synthesizes_mul
      (synthesizes_mul
        (synthesizes_mul hSdagger hHadamard)
        hRz)
      hHadamard)
    hS

/-- Recursive synthesis of a first-qubit block-diagonal unitary into the easy
gate set, via the demultiplexing theorem and recursive exact synthesis on the
lower-wire factors. -/
theorem synthesizes_first_qubit_block_diag {m : ℕ} (hm : 1 ≤ m)
    (ih : ∀ W : Square (2 ^ m),
      W ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ →
        Synthesizes (EasyGate m) W)
    (U₀ U₁ : Square (2 ^ m))
    (hU₀ : U₀ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ)
    (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ) :
    Synthesizes (EasyGate (m + 1)) (firstQubitBlockDiag m U₀ U₁) := by
  rcases general_demultiplexing_step hm U₀ U₁ hU₀ hU₁ with ⟨P, Q, α, hP, hQ, hEq⟩
  have hP' : Synthesizes (EasyGate m) P := ih P hP
  have hQ' : Synthesizes (EasyGate m) Q := ih Q hQ
  have hRz : Synthesizes (EasyGate (m + 1)) (controlledRzFamily m α) :=
    synthesizes_controlled_rz_family m α
  have hPLift : Synthesizes (EasyGate (m + 1)) (liftLowerUnitary m P) := by
    exact synthesizes_liftLower hP'
  have hQLift : Synthesizes (EasyGate (m + 1)) (liftLowerUnitary m Q) := by
    exact synthesizes_liftLower hQ'
  rw [hEq]
  simpa [mul_assoc] using synthesizes_mul (synthesizes_mul hQLift hRz) hPLift

/-- Lemma 1 in `doc.tex`: exact decomposition into the easy gate set.

This is the large recursive lemma we still need to prove before the main
Clifford+T theorem is independent of assumptions. -/
theorem lemma1_decomposition_to_easy_gate_set {n : ℕ} (hn : 2 ≤ n)
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    Synthesizes (EasyGate n) U := by
  have hMain :
      ∀ n, 2 ≤ n →
        ∀ U : Square (2 ^ n),
          U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ →
            Synthesizes (EasyGate n) U := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn U hU
    by_cases hTwo : n = 2
    · subst hTwo
      simpa using two_qubit_unitary_is_easy_gate U hU
    · have hGt : 2 < n := lt_of_le_of_ne hn (Ne.symm hTwo)
      have hNonzero : n ≠ 0 := Nat.ne_of_gt (lt_trans (show 0 < 2 by decide) hGt)
      rcases Nat.exists_eq_succ_of_ne_zero hNonzero with ⟨m, rfl⟩
      have hmTwo : 2 ≤ m := Nat.succ_le_of_lt (Nat.lt_of_succ_lt_succ hGt)
      have hmOne : 1 ≤ m := le_trans (show 1 ≤ 2 by decide) hmTwo
      rcases general_cosine_sine_step (n := m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) U hU with
        ⟨P, R, Q, hP, hR, hQ, hStep, hEq⟩
      rcases hStep with ⟨P₀, P₁, Q₀, Q₁, θ, hPshape, hRshape, hQshape⟩
      have hRec :
          ∀ W : Square (2 ^ m),
            W ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ →
              Synthesizes (EasyGate m) W := by
        intro W hW
        exact ih m (Nat.lt_succ_self m) hmTwo W hW
      have hPshape' : P = firstQubitBlockDiag m P₀ P₁ := by
        simpa [firstQubitBlockDiag] using hPshape
      have hRshape' : R = controlledRyFamily m θ := by
        simpa [controlledRyFamily] using hRshape
      have hQshape' : Q = firstQubitBlockDiag m Q₀ Q₁ := by
        simpa [firstQubitBlockDiag] using hQshape
      have hPBlocks :
          P₀ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ ∧
            P₁ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
        apply firstQubitBlockDiag_unitary_factors (m := m)
        simpa [hPshape'] using hP
      have hQBlocks :
          Q₀ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ ∧
            Q₁ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
        apply firstQubitBlockDiag_unitary_factors (m := m)
        simpa [hQshape'] using hQ
      have hSynthP : Synthesizes (EasyGate (m + 1)) P := by
        rw [hPshape']
        exact synthesizes_first_qubit_block_diag hmOne hRec P₀ P₁ hPBlocks.1 hPBlocks.2
      have hSynthR : Synthesizes (EasyGate (m + 1)) R := by
        rw [hRshape']
        exact synthesizes_controlled_ry_family m θ
      have hSynthQ : Synthesizes (EasyGate (m + 1)) Q := by
        rw [hQshape']
        exact synthesizes_first_qubit_block_diag hmOne hRec Q₀ Q₁ hQBlocks.1 hQBlocks.2
      rw [hEq]
      simpa [mul_assoc] using synthesizes_mul (synthesizes_mul hSynthP hSynthR) hSynthQ
  exact hMain n hn U hU

end Universal
end Clifford
end TwoControl

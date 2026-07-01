import TwoControl.Clifford.Universal.RecursiveDecomposition
import TwoControl.Clifford.Universal.BoundedSynthesis
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace TwoControl
namespace Clifford
namespace Universal

/-!
Bounded exact synthesis for the recursive Lemma 1 layer.

This file is the stage-one counting API for the easy-gate decomposition.  It
does not mention Lemma 12, approximation, or Clifford+T replacement of `R_z`.
-/

private theorem two_mul_pow_eq_pow_succ_bound (m : ℕ) :
    2 * 2 ^ m = 2 ^ (m + 1) := by
  simp [pow_succ, mul_comm]

private theorem four_mul_pow_eq_pow_add_two_bound (m : ℕ) :
    4 * 2 ^ m = 2 ^ (m + 2) := by
  have h4 : 4 = 2 * 2 := by norm_num
  rw [h4, Nat.mul_assoc, two_mul_pow_eq_pow_succ_bound]
  simpa [Nat.add_assoc] using two_mul_pow_eq_pow_succ_bound (m + 1)

private theorem castFin_symm_val_bound {a b : ℕ} (h : a = b) (x : Fin b) :
    (((Equiv.cast (congrArg Fin h)).symm x).1) = x.1 := by
  cases h
  rfl

private theorem castFin_val_bound {a b : ℕ} (h : a = b) (x : Fin a) :
    ((Equiv.cast (congrArg Fin h) x).1) = x.1 := by
  cases h
  rfl

private theorem cast_one_mul_symm_divNat_bound {n : ℕ} (x : Fin n) :
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
        castFin_symm_val_bound h x
      rw [hval]
      exact Nat.div_eq_of_lt x.is_lt

private theorem cast_one_mul_symm_modNat_bound {n : ℕ} (x : Fin n) :
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
        castFin_symm_val_bound h x
      rw [hval, Nat.mod_eq_of_lt x.is_lt]

private theorem one_kron_any_bound {n : ℕ} (U : Square n) :
    castSquare (show 1 * n = n by simp) ((1 : Square 1) ⊗ₖ U) = U := by
  ext i j
  simp [castSquare, reindexSquare, Matrix.reindex_apply, TwoControl.kron,
    cast_one_mul_symm_divNat_bound, cast_one_mul_symm_modNat_bound]

private theorem two_kron_one_bound (U : Square 2) :
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

private theorem kron_right_one_four_bound (U : Square 4) :
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

private theorem one_kron_four_bound (U : Square 4) :
    (1 : Square 1) ⊗ₖ U = U := by
  ext i j
  convert (TwoControl.kron_apply (A := (1 : Square 1)) (B := U) 0 i 0 j) using 1
  simp

private theorem castSquare_trans_bound {a b c : ℕ} (hab : a = b) (hbc : b = c)
    (U : Square a) :
    castSquare hbc (castSquare hab U) = castSquare (hab.trans hbc) U := by
  cases hab
  cases hbc
  rfl

private theorem topTensorEquiv_cast_bound {A B : ℕ} (h : A = B) :
    topTensorEquiv (Equiv.cast (congrArg Fin h)) =
      Equiv.cast (congrArg Fin (congrArg (fun x => 2 * x) h)) := by
  cases h
  ext i
  simp [topTensorEquiv, Nat.mod_add_div]

private theorem one_kron_reindexSquare_bound {A B : ℕ}
    (e : Fin A ≃ Fin B) (U : Square A) :
    ((1 : Square 2) ⊗ₖ reindexSquare e U) =
      reindexSquare (topTensorEquiv e) ((1 : Square 2) ⊗ₖ U) := by
  ext i j
  simp [TwoControl.kron, reindexSquare, topTensorEquiv,
    Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.kroneckerMap_apply]

private theorem castSquare_reindexSquare_bound {B C : ℕ}
    (e : Fin B ≃ Fin B) (h : B = C) (U : Square B) :
    castSquare h (reindexSquare e U) =
      reindexSquare
        (((Equiv.cast (congrArg Fin h)).symm.trans e).trans
          (Equiv.cast (congrArg Fin h)))
        (castSquare h U) := by
  cases h
  ext i j
  simp [castSquare, reindexSquare, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

private theorem liftLowerUnitary_eq_kron_bound (m : ℕ) (U : Square (2 ^ m)) :
    liftLowerUnitary m U =
      castSquare (two_mul_pow_eq_pow_succ_bound m) ((1 : Square 2) ⊗ₖ U) := by
  rw [liftLowerUnitary, firstQubitBlockDiag, unblockify_fromBlocks]
  simp [TwoControl.zero_kron_right]
  rw [← BlockHelpers.proj0_add_proj1, kron_add_left]

private theorem finProd_assoc_2_encoded_bound (n p : ℕ)
    (a : Fin 2) (b : Fin n) (c : Fin p) :
    (Equiv.cast (congrArg Fin ((Nat.mul_assoc 2 n p).symm)))
      (@finProdFinEquiv 2 (n * p) (a, @finProdFinEquiv n p (b, c))) =
    @finProdFinEquiv (2 * n) p (@finProdFinEquiv 2 n (a, b), c) := by
  apply Fin.eq_of_val_eq
  rw [castFin_val_bound]
  simp [finProdFinEquiv, Nat.mul_assoc]
  · ring
  · simp [Nat.mul_assoc]

private theorem one_finProdFinEquiv_bound {l : ℕ}
    (a a' : Fin 2) (b b' : Fin l) :
    (1 : Square (2 * l)) (@finProdFinEquiv 2 l (a, b))
        (@finProdFinEquiv 2 l (a', b')) =
      (1 : Square 2) a a' * ((1 : Square l) b b') := by
  by_cases haa : a = a'
  · subst a'
    by_cases hbb : b = b'
    · subst b'
      simp
    · have hneq :
          (@finProdFinEquiv 2 l (a, b) : Fin (2 * l)) ≠
            @finProdFinEquiv 2 l (a, b') := by
        intro h
        apply hbb
        exact congrArg Prod.snd ((@finProdFinEquiv 2 l).injective h)
      simp [hneq, hbb]
  · have hneq :
        (@finProdFinEquiv 2 l (a, b) : Fin (2 * l)) ≠
          @finProdFinEquiv 2 l (a', b') := by
      intro h
      apply haa
      exact congrArg Prod.fst ((@finProdFinEquiv 2 l).injective h)
    simp [hneq, haa]

private theorem one_kron_assoc_identity_bound (l p : ℕ) (W : Square p) :
    castSquare ((Nat.mul_assoc 2 l p).symm)
        (((1 : Square 2) ⊗ₖ ((1 : Square l) ⊗ₖ W))) =
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
    exact (Equiv.symm_apply_eq _).2
      (finProd_assoc_2_encoded_bound l p a b c).symm
  have hj' :
      (Equiv.cast (congrArg Fin ((Nat.mul_assoc 2 l p).symm))).symm
        (@finProdFinEquiv (2 * l) p (@finProdFinEquiv 2 l (a', b'), c')) =
      @finProdFinEquiv 2 (l * p) (a', @finProdFinEquiv l p (b', c')) := by
    exact (Equiv.symm_apply_eq _).2
      (finProd_assoc_2_encoded_bound l p a' b' c').symm
  calc
    castSquare ((Nat.mul_assoc 2 l p).symm)
        (((1 : Square 2) ⊗ₖ ((1 : Square l) ⊗ₖ W)))
        (@finProdFinEquiv (2 * l) p (@finProdFinEquiv 2 l (a, b), c))
        (@finProdFinEquiv (2 * l) p (@finProdFinEquiv 2 l (a', b'), c'))
        =
      ((1 : Square 2) ⊗ₖ ((1 : Square l) ⊗ₖ W))
        (@finProdFinEquiv 2 (l * p) (a, @finProdFinEquiv l p (b, c)))
        (@finProdFinEquiv 2 (l * p) (a', @finProdFinEquiv l p (b', c'))) := by
          simp [castSquare, reindexSquare, Matrix.reindexAlgEquiv_apply, hi', hj']
    _ = (1 : Square 2) a a' *
          (((1 : Square l) ⊗ₖ W) (@finProdFinEquiv l p (b, c))
            (@finProdFinEquiv l p (b', c'))) := by
          simpa using
            (TwoControl.kron_apply (A := (1 : Square 2))
              (B := ((1 : Square l) ⊗ₖ W))
              a (@finProdFinEquiv l p (b, c)) a'
              (@finProdFinEquiv l p (b', c'))).symm
    _ = (1 : Square 2) a a' * ((1 : Square l) b b' * W c c') := by
          congr 1
          simpa using
            (TwoControl.kron_apply (A := (1 : Square l)) (B := W) b c b' c')
    _ = ((1 : Square 2) a a' * (1 : Square l) b b') * W c c' := by
          simp [mul_assoc]
    _ = (1 : Square (2 * l)) (@finProdFinEquiv 2 l (a, b))
          (@finProdFinEquiv 2 l (a', b')) * W c c' := by
          rw [one_finProdFinEquiv_bound]
    _ = ((1 : Square (2 * l)) ⊗ₖ W)
          (@finProdFinEquiv (2 * l) p (@finProdFinEquiv 2 l (a, b), c))
          (@finProdFinEquiv (2 * l) p (@finProdFinEquiv 2 l (a', b'), c')) := by
          simpa using
            (TwoControl.kron_apply (A := (1 : Square (2 * l))) (B := W)
              (@finProdFinEquiv 2 l (a, b)) c
              (@finProdFinEquiv 2 l (a', b')) c')

private theorem liftLower_oneQubit_embed_bound {m : ℕ}
    (p : OneQubitPlacement m) (U : Square 2) :
    liftLowerUnitary m (p.embed U) = (lowerOneQubitPlacement p).embed U := by
  rw [liftLowerUnitary_eq_kron_bound, OneQubitPlacement.embed, OneQubitPlacement.embed]
  have hCast0 :=
    one_kron_reindexSquare_bound
      (e := Equiv.cast (congrArg Fin p.dimension_eq)) (U := p.tensor U)
  rw [topTensorEquiv_cast_bound p.dimension_eq] at hCast0
  have hCast :
      ((1 : Square 2) ⊗ₖ castSquare p.dimension_eq (p.tensor U)) =
        castSquare (congrArg (fun x => 2 * x) p.dimension_eq)
          ((1 : Square 2) ⊗ₖ p.tensor U) := by
    simpa [castSquare] using hCast0
  rw [one_kron_reindexSquare_bound, hCast]
  rw [castSquare_reindexSquare_bound]
  rw [castSquare_trans_bound]
  have hTensor :
      castSquare ((Nat.mul_assoc 2 p.left (2 * p.right)).symm)
          ((1 : Square 2) ⊗ₖ p.tensor U) =
        (lowerOneQubitPlacement p).tensor U := by
    simpa [lowerOneQubitPlacement, OneQubitPlacement.tensor] using
      one_kron_assoc_identity_bound p.left (2 * p.right) (U ⊗ₖ (1 : Square p.right))
  calc
    reindexSquare (lowerLiftPermutation m p.permutation)
        (castSquare
          ((congrArg (fun x => 2 * x) p.dimension_eq).trans
            (two_mul_pow_eq_pow_succ_bound m))
          ((1 : Square 2) ⊗ₖ p.tensor U))
      =
        reindexSquare (lowerLiftPermutation m p.permutation)
          (castSquare (lowerOneQubitPlacement p).dimension_eq
            ((lowerOneQubitPlacement p).tensor U)) := by
            rw [← castSquare_trans_bound
              ((Nat.mul_assoc 2 p.left (2 * p.right)).symm)
              (lowerOneQubitPlacement p).dimension_eq
              ((1 : Square 2) ⊗ₖ p.tensor U)]
            rw [hTensor]
            simp [lowerOneQubitPlacement]
    _ = (lowerOneQubitPlacement p).embed U := by
          rfl

private theorem liftLower_twoQubit_embed_bound {m : ℕ}
    (p : TwoQubitPlacement m) (U : Square 4) :
    liftLowerUnitary m (p.embed U) = (lowerTwoQubitPlacement p).embed U := by
  rw [liftLowerUnitary_eq_kron_bound, TwoQubitPlacement.embed, TwoQubitPlacement.embed]
  have hCast0 :=
    one_kron_reindexSquare_bound
      (e := Equiv.cast (congrArg Fin p.dimension_eq)) (U := p.tensor U)
  rw [topTensorEquiv_cast_bound p.dimension_eq] at hCast0
  have hCast :
      ((1 : Square 2) ⊗ₖ castSquare p.dimension_eq (p.tensor U)) =
        castSquare (congrArg (fun x => 2 * x) p.dimension_eq)
          ((1 : Square 2) ⊗ₖ p.tensor U) := by
    simpa [castSquare] using hCast0
  rw [one_kron_reindexSquare_bound, hCast]
  rw [castSquare_reindexSquare_bound]
  rw [castSquare_trans_bound]
  have hTensor :
      castSquare ((Nat.mul_assoc 2 p.left (4 * p.right)).symm)
          ((1 : Square 2) ⊗ₖ p.tensor U) =
        (lowerTwoQubitPlacement p).tensor U := by
    simpa [lowerTwoQubitPlacement, TwoQubitPlacement.tensor] using
      one_kron_assoc_identity_bound p.left (4 * p.right) (U ⊗ₖ (1 : Square p.right))
  calc
    reindexSquare (lowerLiftPermutation m p.permutation)
        (castSquare
          ((congrArg (fun x => 2 * x) p.dimension_eq).trans
            (two_mul_pow_eq_pow_succ_bound m))
          ((1 : Square 2) ⊗ₖ p.tensor U))
      =
        reindexSquare (lowerLiftPermutation m p.permutation)
          (castSquare (lowerTwoQubitPlacement p).dimension_eq
            ((lowerTwoQubitPlacement p).tensor U)) := by
            rw [← castSquare_trans_bound
              ((Nat.mul_assoc 2 p.left (4 * p.right)).symm)
              (lowerTwoQubitPlacement p).dimension_eq
              ((1 : Square 2) ⊗ₖ p.tensor U)]
            rw [hTensor]
            simp [lowerTwoQubitPlacement]
    _ = (lowerTwoQubitPlacement p).embed U := by
          rfl

private theorem liftLower_isEmbeddedOneQubit_bound {m : ℕ}
    {U : Square 2} {E : Square (2 ^ m)}
    (hE : IsEmbeddedOneQubitGate m U E) :
    IsEmbeddedOneQubitGate (m + 1) U (liftLowerUnitary m E) := by
  rcases hE with hDirect | hRest
  · rcases hDirect with ⟨p, rfl⟩
    rw [liftLower_oneQubit_embed_bound]
    exact IsEmbeddedOneQubitGate.of_placement (lowerOneQubitPlacement p) U
  · rcases hRest with hFirst | hSecond
    · rcases hFirst with ⟨p, rfl⟩
      rw [liftLower_twoQubit_embed_bound]
      exact IsEmbeddedOneQubitGate.of_twoQubit_first (lowerTwoQubitPlacement p) U
    · rcases hSecond with ⟨p, rfl⟩
      rw [liftLower_twoQubit_embed_bound]
      exact IsEmbeddedOneQubitGate.of_twoQubit_second (lowerTwoQubitPlacement p) U

private theorem liftLower_isEmbeddedTwoQubit_bound {m : ℕ}
    {U : Square 4} {E : Square (2 ^ m)}
    (hE : IsEmbeddedTwoQubitGate m U E) :
    IsEmbeddedTwoQubitGate (m + 1) U (liftLowerUnitary m E) := by
  rcases hE with ⟨p, rfl⟩
  rw [liftLower_twoQubit_embed_bound]
  exact IsEmbeddedTwoQubitGate.of_placement (lowerTwoQubitPlacement p) U

private theorem liftLowerUnitary_one_bound (m : ℕ) :
    liftLowerUnitary m (1 : Square (2 ^ m)) = 1 := by
  rw [liftLowerUnitary_eq_kron_bound, TwoControl.one_kron_one 2 (2 ^ m)]
  simp

private theorem liftLowerUnitary_mul_bound (m : ℕ)
    (U V : Square (2 ^ m)) :
    liftLowerUnitary m (U * V) =
      liftLowerUnitary m U * liftLowerUnitary m V := by
  have hKron :
      ((1 : Square 2) ⊗ₖ (U * V)) =
        ((1 : Square 2) ⊗ₖ U) * ((1 : Square 2) ⊗ₖ V) := by
    simpa using
      (KronHelpers.kron_mul_reindex (A := (1 : Square 2)) (B := (1 : Square 2))
        (C := U) (D := V))
  rw [liftLowerUnitary_eq_kron_bound, liftLowerUnitary_eq_kron_bound,
    liftLowerUnitary_eq_kron_bound, hKron]
  rw [castSquare_mul]

private theorem circuitMatrix_map_liftLower_bound (m : ℕ)
    (gates : List (Square (2 ^ m))) :
    circuitMatrix (gates.map (liftLowerUnitary m)) =
      liftLowerUnitary m (circuitMatrix gates) := by
  induction gates with
  | nil =>
      simp [circuitMatrix, liftLowerUnitary_one_bound]
  | cons gate gates ih =>
      rw [List.map, circuitMatrix_cons, ih, circuitMatrix_cons,
        liftLowerUnitary_mul_bound]

private theorem liftTopOneQubit_zero_bound (U : Square 2) :
    liftTopOneQubit 0 U = U := by
  simpa [liftTopOneQubit] using two_kron_one_bound U

private theorem topTwoUnitary_swap_mul_self_bound (m : ℕ) :
    topTwoUnitary m swap2 * topTwoUnitary m swap2 =
      (1 : Square (2 ^ (m + 2))) := by
  unfold topTwoUnitary
  rw [← TwoQubitPlacement.embed_mul, SwapHelpers.swap2_mul_swap2]
  simp

private noncomputable abbrev topSwapPerm_bound (m : ℕ) :
    Equiv.Perm (Fin (2 ^ (m + 2))) :=
  topSwapPerm m

private theorem topSwapPerm_bound_symm (m : ℕ) :
    (topSwapPerm_bound m).symm = topSwapPerm_bound m :=
  topSwapPerm_symm m

private theorem topTwoUnitary_swap_eq_permMatrix_bound (m : ℕ) :
    topTwoUnitary m swap2 = (topSwapPerm_bound m).permMatrix ℂ :=
  topTwoUnitary_swap_eq_permMatrix m

private theorem permMatrix_conj_eq_reindexSquare_bound {N : ℕ}
    (σ : Equiv.Perm (Fin N)) (hσ : σ.symm = σ) (A : Square N) :
    σ.permMatrix ℂ * A * σ.permMatrix ℂ = reindexSquare σ A := by
  calc
    σ.permMatrix ℂ * A * σ.permMatrix ℂ
        = (A.submatrix σ id).submatrix id σ.symm := by
            rw [PEquiv.toMatrix_toPEquiv_mul]
            rw [PEquiv.mul_toMatrix_toPEquiv]
    _ = reindexSquare σ A := by
          ext i j
          simp [reindexSquare, Matrix.reindex_apply, hσ]

private theorem reindexSquare_reindexSquare_bound {N : ℕ}
    (e f : Fin N ≃ Fin N) (A : Square N) :
    reindexSquare e (reindexSquare f A) =
      reindexSquare (f.trans e) A := by
  ext i j
  simp [reindexSquare, Matrix.reindex_apply]

private noncomputable def middleOneQubitPlacement {m : ℕ}
    (p : OneQubitPlacement (m + 1)) : OneQubitPlacement (m + 2) :=
  let q := lowerOneQubitPlacement p
  { q with permutation := q.permutation.trans (topSwapPerm_bound m) }

private noncomputable def middleTwoQubitPlacement {m : ℕ}
    (p : TwoQubitPlacement (m + 1)) : TwoQubitPlacement (m + 2) :=
  let q := lowerTwoQubitPlacement p
  { q with permutation := q.permutation.trans (topSwapPerm_bound m) }

private theorem topSwap_conj_oneQubitPlacement_bound {m : ℕ}
    (p : OneQubitPlacement (m + 1)) (U : Square 2) :
    topTwoUnitary m swap2 * (lowerOneQubitPlacement p).embed U *
        topTwoUnitary m swap2 =
      (middleOneQubitPlacement p).embed U := by
  rw [topTwoUnitary_swap_eq_permMatrix_bound]
  rw [permMatrix_conj_eq_reindexSquare_bound
    (topSwapPerm_bound m) (topSwapPerm_bound_symm m)]
  rw [OneQubitPlacement.embed, reindexSquare_reindexSquare_bound]
  rfl

private theorem topSwap_conj_twoQubitPlacement_bound {m : ℕ}
    (p : TwoQubitPlacement (m + 1)) (U : Square 4) :
    topTwoUnitary m swap2 * (lowerTwoQubitPlacement p).embed U *
        topTwoUnitary m swap2 =
      (middleTwoQubitPlacement p).embed U := by
  rw [topTwoUnitary_swap_eq_permMatrix_bound]
  rw [permMatrix_conj_eq_reindexSquare_bound
    (topSwapPerm_bound m) (topSwapPerm_bound_symm m)]
  rw [TwoQubitPlacement.embed, reindexSquare_reindexSquare_bound]
  rfl

private theorem liftMiddle_oneQubit_embed_bound {m : ℕ}
    (p : OneQubitPlacement (m + 1)) (U : Square 2) :
    liftMiddleUnitary m (p.embed U) = (middleOneQubitPlacement p).embed U := by
  rw [liftMiddleUnitary, liftLower_oneQubit_embed_bound]
  exact topSwap_conj_oneQubitPlacement_bound p U

private theorem liftMiddle_twoQubit_embed_bound {m : ℕ}
    (p : TwoQubitPlacement (m + 1)) (U : Square 4) :
    liftMiddleUnitary m (p.embed U) = (middleTwoQubitPlacement p).embed U := by
  rw [liftMiddleUnitary, liftLower_twoQubit_embed_bound]
  exact topSwap_conj_twoQubitPlacement_bound p U

private theorem liftMiddle_isEmbeddedOneQubit_bound {m : ℕ}
    {U : Square 2} {E : Square (2 ^ (m + 1))}
    (hE : IsEmbeddedOneQubitGate (m + 1) U E) :
    IsEmbeddedOneQubitGate (m + 2) U (liftMiddleUnitary m E) := by
  rcases hE with hDirect | hRest
  · rcases hDirect with ⟨p, rfl⟩
    rw [liftMiddle_oneQubit_embed_bound]
    exact IsEmbeddedOneQubitGate.of_placement (middleOneQubitPlacement p) U
  · rcases hRest with hFirst | hSecond
    · rcases hFirst with ⟨p, rfl⟩
      rw [liftMiddle_twoQubit_embed_bound]
      exact IsEmbeddedOneQubitGate.of_twoQubit_first (middleTwoQubitPlacement p) U
    · rcases hSecond with ⟨p, rfl⟩
      rw [liftMiddle_twoQubit_embed_bound]
      exact IsEmbeddedOneQubitGate.of_twoQubit_second (middleTwoQubitPlacement p) U

private theorem liftMiddle_isEmbeddedTwoQubit_bound {m : ℕ}
    {U : Square 4} {E : Square (2 ^ (m + 1))}
    (hE : IsEmbeddedTwoQubitGate (m + 1) U E) :
    IsEmbeddedTwoQubitGate (m + 2) U (liftMiddleUnitary m E) := by
  rcases hE with ⟨p, rfl⟩
  rw [liftMiddle_twoQubit_embed_bound]
  exact IsEmbeddedTwoQubitGate.of_placement (middleTwoQubitPlacement p) U

private theorem liftMiddleUnitary_one_bound (m : ℕ) :
    liftMiddleUnitary m (1 : Square (2 ^ (m + 1))) =
      (1 : Square (2 ^ (m + 2))) := by
  rw [liftMiddleUnitary, liftLowerUnitary_one_bound]
  simpa [mul_assoc] using topTwoUnitary_swap_mul_self_bound m

private theorem liftMiddleUnitary_mul_bound (m : ℕ)
    (U V : Square (2 ^ (m + 1))) :
    liftMiddleUnitary m (U * V) =
      liftMiddleUnitary m U * liftMiddleUnitary m V := by
  let S : Square (2 ^ (m + 2)) := topTwoUnitary m swap2
  let LU : Square (2 ^ (m + 2)) := liftLowerUnitary (m + 1) U
  let LV : Square (2 ^ (m + 2)) := liftLowerUnitary (m + 1) V
  have hS : S * S = (1 : Square (2 ^ (m + 2))) := by
    dsimp [S]
    exact topTwoUnitary_swap_mul_self_bound m
  rw [liftMiddleUnitary, liftMiddleUnitary, liftMiddleUnitary,
    liftLowerUnitary_mul_bound]
  change S * (LU * LV) * S = (S * LU * S) * (S * LV * S)
  calc
    S * (LU * LV) * S = S * LU * LV * S := by simp [mul_assoc]
    _ = S * LU * (S * S) * LV * S := by
          rw [hS]
          simp [mul_assoc]
    _ = (S * LU * S) * (S * LV * S) := by simp [mul_assoc]

private theorem circuitMatrix_map_liftMiddle_bound (m : ℕ)
    (gates : List (Square (2 ^ (m + 1)))) :
    circuitMatrix (gates.map (liftMiddleUnitary m)) =
      liftMiddleUnitary m (circuitMatrix gates) := by
  induction gates with
  | nil =>
      simp [circuitMatrix, liftMiddleUnitary_one_bound]
  | cons gate gates ih =>
      rw [List.map, circuitMatrix_cons, ih, circuitMatrix_cons,
        liftMiddleUnitary_mul_bound]

private theorem firstQubitBlockDiag_unitary_factors_bound {m : ℕ}
    {A D : Square (2 ^ m)}
    (h : firstQubitBlockDiag m A D ∈
      Matrix.unitaryGroup (Fin (2 ^ (m + 1))) ℂ) :
    A ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ ∧
      D ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
  let e : Fin (2 * 2 ^ m) ≃ Fin (2 ^ (m + 1)) :=
    Equiv.cast (congrArg Fin (two_mul_pow_eq_pow_succ_bound m))
  have hReindexed :
      reindexSquare e (unblockify (Matrix.fromBlocks A 0 0 D)) ∈
        Matrix.unitaryGroup (Fin (2 ^ (m + 1))) ℂ := by
    simpa [firstQubitBlockDiag, castSquare, e] using h
  have hUnblocked :
      unblockify (Matrix.fromBlocks A 0 0 D) ∈
        Matrix.unitaryGroup (Fin (2 * 2 ^ m)) ℂ := by
    have hSymm := reindexSquare_mem_unitaryGroup (e := e.symm) hReindexed
    simpa [e, reindexSquare, Matrix.reindex_apply] using hSymm
  have hBlock :
      Matrix.fromBlocks A 0 0 D ∈
        Matrix.unitaryGroup (Fin (2 ^ m) ⊕ Fin (2 ^ m)) ℂ := by
    simpa using (blockify_mem_unitaryGroup_iff (n := 2 ^ m)
      (U := unblockify (Matrix.fromBlocks A 0 0 D))).2 hUnblocked
  exact BlockHelpers.block_diagonal_unitary A D hBlock

private theorem two_qubit_unitary_is_easy_gate_bounded (U : Square 4)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    SynthesizesWithLength (EasyGate 2) U 1 := by
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
    rw [kron_right_one_four_bound, one_kron_four_bound]
    simp [Matrix.submatrix_id_id]
  exact synthesizesWithLength_singleton
    (EasyGate.of_embedded_two_qubit hU hEmbed)

/-- Length bound for an `m`-control uniformly controlled `R_z` family in the
easy-gate layer.  The family acts on `m + 1` qubits. -/
def controlledRzBound : ℕ → ℕ
  | 0 => 1
  | m + 1 => 2 * controlledRzBound m + 2

/-- Length bound for an `m`-control uniformly controlled `R_y` family in the
easy-gate layer, implemented by `S† H`, a controlled `R_z`, then `H S`. -/
def controlledRyBound (m : ℕ) : ℕ :=
  controlledRzBound m + 4

/-- Coarse recursive length bound for the paper's Lemma 1 easy-gate synthesis.

This intentionally overcounts the two-qubit base case.  The resulting recurrence
is simple, monotone enough for downstream use, and still has the desired
`O(4^n)` growth. -/
def easyBound : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      4 * easyBound n + 2 * controlledRzBound n + controlledRyBound n

/-- Public version of the top-wire one-qubit embedding fact needed by the
bounded proofs. -/
theorem liftTopOneQubit_isEmbedded_oneQubit (m : ℕ) (U : Square 2) :
    IsEmbeddedOneQubitGate (m + 1) U (liftTopOneQubit m U) := by
  let p : OneQubitPlacement (m + 1) :=
    { target := 0
      left := 1
      right := 2 ^ m
      dimension_eq := by
        simpa using two_mul_pow_eq_pow_succ_bound m
      permutation := Equiv.refl _ }
  left
  refine ⟨p, ?_⟩
  calc
    liftTopOneQubit m U
        = castSquare (two_mul_pow_eq_pow_succ_bound m)
            (castSquare (show 1 * (2 * 2 ^ m) = 2 * 2 ^ m by simp)
              ((1 : Square 1) ⊗ₖ (U ⊗ₖ (1 : Square (2 ^ m))))) := by
            show castSquare (two_mul_pow_eq_pow_succ_bound m)
                (U ⊗ₖ (1 : Square (2 ^ m))) =
              castSquare (two_mul_pow_eq_pow_succ_bound m)
                (castSquare (show 1 * (2 * 2 ^ m) = 2 * 2 ^ m by simp)
                  ((1 : Square 1) ⊗ₖ (U ⊗ₖ (1 : Square (2 ^ m)))))
            rw [one_kron_any_bound]
    _ = reindexSquare (Equiv.refl (Fin (2 ^ (m + 1))))
          (castSquare p.dimension_eq
            ((1 : Square 1) ⊗ₖ (U ⊗ₖ (1 : Square (2 ^ m))))) := by
          simp [p, castSquare_trans_bound, reindexSquare]
    _ = p.embed U := by
          rfl

/-- Public version of the top two-qubit embedding fact needed by the bounded
proofs. -/
theorem topTwoUnitary_isEmbedded_twoQubit (m : ℕ) (U : Square 4) :
    IsEmbeddedTwoQubitGate (m + 2) U (topTwoUnitary m U) := by
  unfold topTwoUnitary
  exact IsEmbeddedTwoQubitGate.of_placement _ U

/-- Lower-wire lifting preserves easy-gate membership. -/
theorem liftLower_easyGate {m : ℕ} {E : Square (2 ^ m)}
    (hE : EasyGate m E) :
    EasyGate (m + 1) (liftLowerUnitary m E) := by
  rcases hE with hTwo | hRest
  · rcases hTwo with ⟨V, hV, hEmbed⟩
    exact EasyGate.of_embedded_two_qubit hV (liftLower_isEmbeddedTwoQubit_bound hEmbed)
  · rcases hRest with hHadamard | hRest
    · exact EasyGate.hadamard (liftLower_isEmbeddedOneQubit_bound hHadamard)
    · rcases hRest with hS | hRest
      · exact EasyGate.phaseS (liftLower_isEmbeddedOneQubit_bound hS)
      · rcases hRest with hSdagger | hRz
        · exact EasyGate.phaseSdagger (liftLower_isEmbeddedOneQubit_bound hSdagger)
        · rcases hRz with ⟨θ, hRz⟩
          exact EasyGate.rz θ (liftLower_isEmbeddedOneQubit_bound hRz)

/-- Middle-wire lifting preserves easy-gate membership. -/
theorem liftMiddle_easyGate {m : ℕ} {E : Square (2 ^ (m + 1))}
    (hE : EasyGate (m + 1) E) :
    EasyGate (m + 2) (liftMiddleUnitary m E) := by
  rcases hE with hTwo | hRest
  · rcases hTwo with ⟨V, hV, hEmbed⟩
    exact EasyGate.of_embedded_two_qubit hV
      (liftMiddle_isEmbeddedTwoQubit_bound hEmbed)
  · rcases hRest with hHadamard | hRest
    · exact EasyGate.hadamard (liftMiddle_isEmbeddedOneQubit_bound hHadamard)
    · rcases hRest with hS | hRest
      · exact EasyGate.phaseS (liftMiddle_isEmbeddedOneQubit_bound hS)
      · rcases hRest with hSdagger | hRz
        · exact EasyGate.phaseSdagger (liftMiddle_isEmbeddedOneQubit_bound hSdagger)
        · rcases hRz with ⟨θ, hRz⟩
          exact EasyGate.rz θ (liftMiddle_isEmbeddedOneQubit_bound hRz)

/-- Lower-wire lifting preserves bounded easy-gate synthesis without increasing
the circuit length. -/
theorem synthesizes_liftLower_bounded {m : ℕ} {W : Square (2 ^ m)} {bound : ℕ}
    (hW : SynthesizesWithLength (EasyGate m) W bound) :
    SynthesizesWithLength
      (EasyGate (m + 1))
      (liftLowerUnitary m W)
      bound := by
  rcases hW with ⟨gates, hGates, hEq, hLen⟩
  refine ⟨gates.map (liftLowerUnitary m), ?_, ?_, ?_⟩
  · intro gate hgate
    rcases List.mem_map.1 hgate with ⟨gate', hgate', rfl⟩
    exact liftLower_easyGate (hGates gate' hgate')
  · rw [hEq]
    symm
    exact circuitMatrix_map_liftLower_bound m gates
  · simpa using hLen

/-- Middle-wire lifting preserves bounded easy-gate synthesis without
increasing the circuit length. -/
theorem synthesizes_liftMiddle_bounded {m : ℕ} {W : Square (2 ^ (m + 1))}
    {bound : ℕ}
    (hW : SynthesizesWithLength (EasyGate (m + 1)) W bound) :
    SynthesizesWithLength
      (EasyGate (m + 2))
      (liftMiddleUnitary m W)
      bound := by
  rcases hW with ⟨gates, hGates, hEq, hLen⟩
  refine ⟨gates.map (liftMiddleUnitary m), ?_, ?_, ?_⟩
  · intro gate hgate
    rcases List.mem_map.1 hgate with ⟨gate', hgate', rfl⟩
    exact liftMiddle_easyGate (hGates gate' hgate')
  · rw [hEq]
    symm
    exact circuitMatrix_map_liftMiddle_bound m gates
  · simpa using hLen

/-- Bounded synthesis of uniformly controlled `R_z` families in the easy-gate
layer. -/
theorem synthesizes_controlled_rz_family_bounded (m : ℕ)
    (α : Fin (2 ^ m) → ℝ) :
    SynthesizesWithLength
      (EasyGate (m + 1))
      (controlledRzFamily m α)
      (controlledRzBound m) := by
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
          castSquare (two_mul_pow_eq_pow_succ_bound 0)
            ((proj0 ⊗ₖ Matrix.diagonal
                (fun i : Fin 1 => Complex.exp (-Complex.I * (α i / 2)))) +
              proj01 ⊗ₖ (0 : Square 1) + proj10 ⊗ₖ (0 : Square 1) +
              proj1 ⊗ₖ Matrix.diagonal
                (fun i : Fin 1 => Complex.exp (Complex.I * (α i / 2)))) =
            castSquare (two_mul_pow_eq_pow_succ_bound 0)
              ((proj0 ⊗ₖ
                  (Complex.exp (-Complex.I * (α 0 / 2)) • (1 : Square 1))) +
                proj01 ⊗ₖ (0 : Square 1) + proj10 ⊗ₖ (0 : Square 1) +
                proj1 ⊗ₖ
                  (Complex.exp (Complex.I * (α 0 / 2)) • (1 : Square 1))) := by
        rw [hDiag0, hDiag1]
      have hBase : controlledRzFamily 0 α = rz (α 0) := by
        rw [controlledRzFamily, firstQubitBlockDiag, unblockify_fromBlocks]
        exact hBlocks.trans <| by
          rw [KronHelpers.kron_smul_right, KronHelpers.kron_smul_right]
          rw [two_kron_one_bound, two_kron_one_bound]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [rz, diag2, proj0, proj1, proj01, proj10, ketbra, ket0, ket1,
              castSquare, reindexSquare, Matrix.reindex_apply, TwoControl.kron]
      rw [hBase, ← liftTopOneQubit_zero_bound (rz (α 0))]
      simpa [controlledRzBound] using
        synthesizesWithLength_singleton
          (EasyGate.rz (α 0)
            (liftTopOneQubit_isEmbedded_oneQubit 0 (rz (α 0))))
  | succ m ih =>
      rcases controlled_rz_reduction_step m α with ⟨β, γ, CX, hCX, hEq⟩
      have hCX' :
          SynthesizesWithLength (EasyGate (m + 2)) CX 1 := by
        exact synthesizesWithLength_singleton
          (EasyGate.of_embedded_two_qubit cnot_mem_unitaryGroup hCX)
      have hβ :
          SynthesizesWithLength (EasyGate (m + 1))
            (controlledRzFamily m β) (controlledRzBound m) := ih β
      have hγ :
          SynthesizesWithLength (EasyGate (m + 1))
            (controlledRzFamily m γ) (controlledRzBound m) := ih γ
      have hβLift :
          SynthesizesWithLength (EasyGate (m + 2))
            (liftMiddleUnitary m (controlledRzFamily m β))
            (controlledRzBound m) := by
        exact synthesizes_liftMiddle_bounded hβ
      have hγLift :
          SynthesizesWithLength (EasyGate (m + 2))
            (liftMiddleUnitary m (controlledRzFamily m γ))
            (controlledRzBound m) := by
        exact synthesizes_liftMiddle_bounded hγ
      have hProduct :=
        synthesizesWithLength_mul
          (synthesizesWithLength_mul
            (synthesizesWithLength_mul hCX' hβLift)
            hCX')
          hγLift
      rw [hEq]
      exact SynthesizesWithLength.mono_bound
        (by simp [controlledRzBound]; omega)
        hProduct

/-- Bounded synthesis of uniformly controlled `R_y` families in the easy-gate
layer. -/
theorem synthesizes_controlled_ry_family_bounded (m : ℕ)
    (θ : Fin (2 ^ m) → ℝ) :
    SynthesizesWithLength
      (EasyGate (m + 1))
      (controlledRyFamily m θ)
      (controlledRyBound m) := by
  rw [controlled_ry_family_via_controlled_rz]
  have hSdagger :
      SynthesizesWithLength (EasyGate (m + 1))
        (liftTopOneQubit m phaseSdagger) 1 := by
    exact synthesizesWithLength_singleton
      (EasyGate.phaseSdagger (liftTopOneQubit_isEmbedded_oneQubit m phaseSdagger))
  have hHadamard :
      SynthesizesWithLength (EasyGate (m + 1))
        (liftTopOneQubit m hadamard2) 1 := by
    exact synthesizesWithLength_singleton
      (EasyGate.hadamard (liftTopOneQubit_isEmbedded_oneQubit m hadamard2))
  have hRz :
      SynthesizesWithLength (EasyGate (m + 1))
        (controlledRzFamily m (fun i => - θ i)) (controlledRzBound m) := by
    exact synthesizes_controlled_rz_family_bounded m (fun i => - θ i)
  have hS :
      SynthesizesWithLength (EasyGate (m + 1))
        (liftTopOneQubit m phaseS) 1 := by
    exact synthesizesWithLength_singleton
      (EasyGate.phaseS (liftTopOneQubit_isEmbedded_oneQubit m phaseS))
  have hProduct :=
    synthesizesWithLength_mul
      (synthesizesWithLength_mul
        (synthesizesWithLength_mul
          (synthesizesWithLength_mul hSdagger hHadamard)
          hRz)
        hHadamard)
      hS
  exact SynthesizesWithLength.mono_bound
    (by dsimp [controlledRyBound]; omega)
    hProduct

/-- Bounded synthesis of a first-qubit block-diagonal unitary into the easy
gate set, assuming bounded synthesis for the lower-wire unitaries. -/
theorem synthesizes_first_qubit_block_diag_bounded {m : ℕ} (hm : 1 ≤ m)
    (ih : ∀ W : Square (2 ^ m),
      W ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ →
        SynthesizesWithLength (EasyGate m) W (easyBound m))
    (U₀ U₁ : Square (2 ^ m))
    (hU₀ : U₀ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ)
    (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ) :
    SynthesizesWithLength
      (EasyGate (m + 1))
      (firstQubitBlockDiag m U₀ U₁)
      (2 * easyBound m + controlledRzBound m) := by
  rcases general_demultiplexing_step hm U₀ U₁ hU₀ hU₁ with
    ⟨P, Q, α, hP, hQ, hEq⟩
  have hP' : SynthesizesWithLength (EasyGate m) P (easyBound m) := ih P hP
  have hQ' : SynthesizesWithLength (EasyGate m) Q (easyBound m) := ih Q hQ
  have hRz :
      SynthesizesWithLength (EasyGate (m + 1))
        (controlledRzFamily m α) (controlledRzBound m) :=
    synthesizes_controlled_rz_family_bounded m α
  have hPLift :
      SynthesizesWithLength (EasyGate (m + 1))
        (liftLowerUnitary m P) (easyBound m) := by
    exact synthesizes_liftLower_bounded hP'
  have hQLift :
      SynthesizesWithLength (EasyGate (m + 1))
        (liftLowerUnitary m Q) (easyBound m) := by
    exact synthesizes_liftLower_bounded hQ'
  have hProduct :=
    synthesizesWithLength_mul (synthesizesWithLength_mul hQLift hRz) hPLift
  rw [hEq]
  exact SynthesizesWithLength.mono_bound
    (by omega)
    hProduct

/-- Bounded version of Lemma 1 from `doc.tex`, using the Lean easy-gate
predicate. -/
theorem lemma1_decomposition_to_easy_gate_set_bounded {n : ℕ} (hn : 2 ≤ n)
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    SynthesizesWithLength (EasyGate n) U (easyBound n) := by
  have hMain :
      ∀ n, 2 ≤ n →
        ∀ U : Square (2 ^ n),
          U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ →
            SynthesizesWithLength (EasyGate n) U (easyBound n) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn U hU
    by_cases hTwo : n = 2
    · subst hTwo
      exact SynthesizesWithLength.mono_bound
        (by norm_num [easyBound, controlledRzBound, controlledRyBound])
        (two_qubit_unitary_is_easy_gate_bounded U hU)
    · have hGt : 2 < n := lt_of_le_of_ne hn (Ne.symm hTwo)
      have hNonzero : n ≠ 0 :=
        Nat.ne_of_gt (lt_trans (show 0 < 2 by decide) hGt)
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
              SynthesizesWithLength (EasyGate m) W (easyBound m) := by
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
        apply firstQubitBlockDiag_unitary_factors_bound (m := m)
        simpa [hPshape'] using hP
      have hQBlocks :
          Q₀ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ ∧
            Q₁ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
        apply firstQubitBlockDiag_unitary_factors_bound (m := m)
        simpa [hQshape'] using hQ
      have hSynthP :
          SynthesizesWithLength (EasyGate (m + 1)) P
            (2 * easyBound m + controlledRzBound m) := by
        rw [hPshape']
        exact synthesizes_first_qubit_block_diag_bounded
          hmOne hRec P₀ P₁ hPBlocks.1 hPBlocks.2
      have hSynthR :
          SynthesizesWithLength (EasyGate (m + 1)) R (controlledRyBound m) := by
        rw [hRshape']
        exact synthesizes_controlled_ry_family_bounded m θ
      have hSynthQ :
          SynthesizesWithLength (EasyGate (m + 1)) Q
            (2 * easyBound m + controlledRzBound m) := by
        rw [hQshape']
        exact synthesizes_first_qubit_block_diag_bounded
          hmOne hRec Q₀ Q₁ hQBlocks.1 hQBlocks.2
      have hProduct :=
        synthesizesWithLength_mul (synthesizesWithLength_mul hSynthP hSynthR) hSynthQ
      rw [hEq]
      exact SynthesizesWithLength.mono_bound
        (by simp [easyBound]; omega)
        hProduct
  exact hMain n hn U hU

/-- Closed form for the controlled-`R_z` recurrence in Lean's indexing. -/
theorem controlledRzBound_closed_form (m : ℕ) :
    controlledRzBound m = 3 * 2 ^ m - 2 := by
  induction m with
  | zero =>
      simp [controlledRzBound]
  | succ m ih =>
      rw [controlledRzBound, ih, pow_succ]
      set p : ℕ := 2 ^ m
      have hp : 1 ≤ p := by
        dsimp [p]
        exact Nat.one_le_pow m 2 (by norm_num)
      rw [Nat.mul_sub_left_distrib]
      omega

/-- Coarse exponential upper bound for controlled-`R_z` synthesis. -/
theorem controlledRzBound_le_three_mul_two_pow (m : ℕ) :
    controlledRzBound m ≤ 3 * 2 ^ m := by
  rw [controlledRzBound_closed_form]
  omega

private theorem easyBound_succ_eq (n : ℕ) :
    easyBound (n + 1) = 4 * easyBound n + 9 * 2 ^ n - 2 := by
  rw [easyBound, controlledRyBound, controlledRzBound_closed_form]
  have hPow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  omega

private theorem easyBound_strong_succ (n : ℕ) :
    2 * easyBound (n + 1) + 9 * 2 ^ (n + 1) ≤ 10 * 4 ^ (n + 1) := by
  induction n with
  | zero =>
      norm_num [easyBound, controlledRyBound, controlledRzBound]
  | succ n ih =>
      calc
        2 * easyBound (n.succ + 1) + 9 * 2 ^ (n.succ + 1)
            ≤ 4 * (2 * easyBound (n + 1) + 9 * 2 ^ (n + 1)) := by
              rw [easyBound_succ_eq (n + 1)]
              rw [pow_succ]
              omega
        _ ≤ 4 * (10 * 4 ^ (n + 1)) := by
              exact Nat.mul_le_mul_left 4 ih
        _ = 10 * 4 ^ (n.succ + 1) := by
              have hidx : n.succ + 1 = (n + 1) + 1 := by omega
              rw [hidx, pow_succ]
              ring

/-- Coarse `4^n` upper bound for the easy-gate recursive synthesis. -/
theorem easyBound_le_five_mul_four_pow (n : ℕ) :
    easyBound n ≤ 5 * 4 ^ n := by
  cases n with
  | zero =>
      simp [easyBound]
  | succ n =>
      have hStrong := easyBound_strong_succ n
      have hDrop : 2 * easyBound (n + 1) ≤ 10 * 4 ^ (n + 1) := by
        exact le_trans (Nat.le_add_right _ _) hStrong
      omega

end Universal
end Clifford
end TwoControl

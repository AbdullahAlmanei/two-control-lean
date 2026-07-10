import RossSelinger.Basic
import KMM.ExactSynthesis
import MatrixCompletion.Completion

namespace RossSelinger

open TwoControl

/-!
Residue vocabulary for the Giles-Selinger Lemma 7.5 close-out.

The paper writes a residue of `Z[ω] / (2)` as a four-bit string
`pqrs`, meaning `pω³ + qω² + rω + s`.  This file keeps that paper order
explicit so Figure 2 can be transcribed without mental basis conversion.
-/

namespace Selinger75

open KMM
open MatrixCompletion
open DyadicCyclotomic

/-- A residue `pω³ + qω² + rω + s` in `Z[ω] / (2)`, stored in the bit order
used in Giles-Selinger's Figure 2. -/
structure Residue where
  p : Bool
  q : Bool
  r : Bool
  s : Bool
deriving DecidableEq, Repr

namespace Residue

def bitOfInt (z : ℤ) : Bool :=
  decide ((z : ZMod 2) = 1)

private theorem zmod2_neg_eq_self (a : ZMod 2) : -a = a := by
  fin_cases a <;> rfl

@[simp] theorem bitOfInt_neg (z : ℤ) :
    bitOfInt (-z) = bitOfInt z := by
  unfold bitOfInt
  rw [Int.cast_neg, zmod2_neg_eq_self]

def ofBits (p q r s : Bool) : Residue :=
  ⟨p, q, r, s⟩

def r0000 : Residue := ofBits false false false false
def r0001 : Residue := ofBits false false false true
def r0010 : Residue := ofBits false false true false
def r0011 : Residue := ofBits false false true true
def r0100 : Residue := ofBits false true false false
def r0101 : Residue := ofBits false true false true
def r0110 : Residue := ofBits false true true false
def r0111 : Residue := ofBits false true true true
def r1000 : Residue := ofBits true false false false
def r1001 : Residue := ofBits true false false true
def r1010 : Residue := ofBits true false true false
def r1011 : Residue := ofBits true false true true
def r1100 : Residue := ofBits true true false false
def r1101 : Residue := ofBits true true false true
def r1110 : Residue := ofBits true true true false
def r1111 : Residue := ofBits true true true true

/-- Multiplication by `ω` on residues.  Since the quotient is modulo `2`,
`ω⁴ = -1` acts as `1`, so this is the cyclic shift described in the paper. -/
def omegaMul (x : Residue) : Residue :=
  ofBits x.q x.r x.s x.p

def omegaPowMul : ℕ → Residue → Residue
  | 0, x => x
  | n + 1, x => omegaMul (omegaPowMul n x)

/-- Addition of residues modulo `2`, i.e. bitwise xor in the paper's
`pω³ + qω² + rω + s` coordinates. -/
def add (x y : Residue) : Residue :=
  ofBits (Bool.xor x.p y.p) (Bool.xor x.q y.q)
    (Bool.xor x.r y.r) (Bool.xor x.s y.s)

/-- Bullet conjugation on residues.  Modulo `2`, the signs from
`ω⁻¹ = -ω³`, `ω⁻² = -ω²`, and `ω⁻³ = -ω` disappear. -/
def bullet (x : Residue) : Residue :=
  ofBits x.r x.q x.p x.s

def reducible (x : Residue) : Prop :=
  x = r0000 ∨ x = r0101 ∨ x = r1010 ∨ x = r1111

/-- Residue of an omega-coordinate numerator, converted from KMM's basis
`x₀ + x₁ω + x₂ω² + x₃ω³` into the paper's displayed order
`pω³ + qω² + rω + s`. -/
def ofOmegaIntCoord (x : OmegaIntCoord) : Residue :=
  ofBits (bitOfInt x.x3) (bitOfInt x.x2) (bitOfInt x.x1) (bitOfInt x.x0)

@[simp] theorem omegaMul_four (x : Residue) :
    omegaPowMul 4 x = x := by
  cases x
  rfl

@[simp] theorem bullet_bullet (x : Residue) :
    bullet (bullet x) = x := by
  cases x
  rfl

end Residue

/-- `r` is the `k`-residue of `z`: after multiplying by `√2^k`, the omega
integer numerator reduces to `r` modulo `2`. -/
def HasResidueAtLevel (z : ℂ) (k : ℕ) (r : Residue) : Prop :=
  ∃ x : OmegaIntCoord,
    z = OmegaIntCoord.val x / sqrtTwoComplex ^ k ∧
      Residue.ofOmegaIntCoord x = r

/-- Every omega-denominator presentation has a residue at that level. -/
theorem exists_hasResidueAtLevel_of_hasOmegaDenominatorExponent
    {z : ℂ} {k : ℕ}
    (h : HasOmegaDenominatorExponent z k) :
    ∃ r : Residue, HasResidueAtLevel z k r := by
  rcases h with ⟨x, hx⟩
  exact ⟨Residue.ofOmegaIntCoord x, x, hx, rfl⟩

/-- Omega-coordinate numerator for complex conjugation. -/
def omegaStarCoord (x : OmegaIntCoord) : OmegaIntCoord where
  x0 := x.x0
  x1 := -x.x3
  x2 := -x.x2
  x3 := -x.x1

/-- Omega-coordinate numerator for the top-right entry `-t†`. -/
def omegaNegStarCoord (x : OmegaIntCoord) : OmegaIntCoord :=
  OmegaIntCoord.neg (omegaStarCoord x)

theorem val_omegaStarCoord (x : OmegaIntCoord) :
    OmegaIntCoord.val (omegaStarCoord x) = star (OmegaIntCoord.val x) := by
  cases x
  simp [omegaStarCoord, OmegaIntCoord.val, star_add, star_mul, star_rsOmegaAlg]
  ring_nf
  simp [rsOmegaAlg_six, rsOmegaAlg_nine]
  ring

theorem val_omegaNegStarCoord (x : OmegaIntCoord) :
    OmegaIntCoord.val (omegaNegStarCoord x) = -star (OmegaIntCoord.val x) := by
  rw [omegaNegStarCoord, OmegaIntCoord.val_neg, val_omegaStarCoord]

theorem residue_omegaStarCoord (x : OmegaIntCoord) :
    Residue.ofOmegaIntCoord (omegaStarCoord x) =
      Residue.bullet (Residue.ofOmegaIntCoord x) := by
  cases x
  simp [omegaStarCoord, Residue.ofOmegaIntCoord, Residue.bullet,
    Residue.ofBits]

theorem residue_omegaNegStarCoord (x : OmegaIntCoord) :
    Residue.ofOmegaIntCoord (omegaNegStarCoord x) =
      Residue.bullet (Residue.ofOmegaIntCoord x) := by
  cases x
  simp [omegaNegStarCoord, omegaStarCoord, OmegaIntCoord.neg,
    Residue.ofOmegaIntCoord, Residue.bullet, Residue.ofBits]

theorem hasResidueAtLevel_star
    {z : ℂ} {k : ℕ} {r : Residue}
    (h : HasResidueAtLevel z k r) :
    HasResidueAtLevel (star z) k (Residue.bullet r) := by
  rcases h with ⟨x, hz, hr⟩
  refine ⟨omegaStarCoord x, ?_, ?_⟩
  · rw [hz]
    simp [val_omegaStarCoord, sqrtTwoComplex]
  · rw [residue_omegaStarCoord, hr]

theorem hasResidueAtLevel_neg_star
    {z : ℂ} {k : ℕ} {r : Residue}
    (h : HasResidueAtLevel z k r) :
    HasResidueAtLevel (-star z) k (Residue.bullet r) := by
  rcases h with ⟨x, hz, hr⟩
  refine ⟨omegaNegStarCoord x, ?_, ?_⟩
  · rw [hz]
    simp [val_omegaNegStarCoord, sqrtTwoComplex]
    ring
  · rw [residue_omegaNegStarCoord, hr]

theorem hasOmegaDenominatorExponent_of_hasResidueAtLevel
    {z : ℂ} {k : ℕ} {r : Residue}
    (h : HasResidueAtLevel z k r) :
    HasOmegaDenominatorExponent z k := by
  rcases h with ⟨x, hz, _hr⟩
  exact ⟨x, hz⟩

theorem hasOmegaDenominatorExponent_star
    {z : ℂ} {k : ℕ}
    (h : HasOmegaDenominatorExponent z k) :
    HasOmegaDenominatorExponent (star z) k := by
  rcases h with ⟨x, hz⟩
  refine ⟨omegaStarCoord x, ?_⟩
  rw [hz]
  simp [val_omegaStarCoord, sqrtTwoComplex]

theorem hasOmegaDenominatorExponent_neg_star
    {z : ℂ} {k : ℕ}
    (h : HasOmegaDenominatorExponent z k) :
    HasOmegaDenominatorExponent (-star z) k := by
  rcases h with ⟨x, hz⟩
  refine ⟨omegaNegStarCoord x, ?_⟩
  rw [hz]
  simp [val_omegaNegStarCoord, sqrtTwoComplex]
  ring

theorem hasOmegaDenominatorExponent_of_normEquation
    {u t : ℂ} {k : ℕ}
    (hu : HasOmegaDenominatorExponent u k)
    (ht : InDyadicCyclotomic t)
    (hNorm : NormEquation u t) :
    HasOmegaDenominatorExponent t k := by
  rcases hu with ⟨x, hx⟩
  have htOmega : InOmegaDyadicCyclotomic t :=
    inOmegaDyadicCyclotomic_of_inDyadicCyclotomic ht
  have hState : IsUnitState u t := by
    simpa [IsUnitState, NormEquation] using hNorm
  have hle : omegaSDE t ≤ k :=
    omegaSDE_second_le_of_unit_state_common_denominator hx htOmega hState
  exact hasOmegaDenominatorExponent_mono
    (hasOmegaDenominatorExponent_omegaSDE htOmega) hle

theorem hasOmegaDenominatorExponent_of_normEquation_legacy
    {u t : ℂ} {k : ℕ}
    (hu : HasDenominatorExponent u k)
    (ht : InDyadicCyclotomic t)
    (hNorm : NormEquation u t) :
    HasOmegaDenominatorExponent t k :=
  hasOmegaDenominatorExponent_of_normEquation
    (hasOmegaDenominatorExponent_of_hasDenominatorExponent hu) ht hNorm

/-- Ross-Selinger Lemma 7.5 denominator synchronization in the paper's
`D[ω]` denominator convention: in a unitary completion, the two entries have
the same least omega-denominator exponent. -/
theorem omegaSDE_eq_of_normEquation
    {u t : ℂ}
    (hu : InDyadicCyclotomic u)
    (ht : InDyadicCyclotomic t)
    (hNorm : NormEquation u t) :
    omegaSDE t = omegaSDE u := by
  have huOmega : InOmegaDyadicCyclotomic u :=
    inOmegaDyadicCyclotomic_of_inDyadicCyclotomic hu
  have htOmega : InOmegaDyadicCyclotomic t :=
    inOmegaDyadicCyclotomic_of_inDyadicCyclotomic ht
  have ht_at_u : HasOmegaDenominatorExponent t (omegaSDE u) :=
    hasOmegaDenominatorExponent_of_normEquation
      (hasOmegaDenominatorExponent_omegaSDE huOmega) ht hNorm
  have hle_tu : omegaSDE t ≤ omegaSDE u :=
    omegaSDE_le_of_hasOmegaDenominatorExponent ht_at_u
  have hNorm_swap : NormEquation t u := by
    simpa [NormEquation, add_comm] using hNorm
  have hu_at_t : HasOmegaDenominatorExponent u (omegaSDE t) :=
    hasOmegaDenominatorExponent_of_normEquation
      (hasOmegaDenominatorExponent_omegaSDE htOmega) hu hNorm_swap
  have hle_ut : omegaSDE u ≤ omegaSDE t :=
    omegaSDE_le_of_hasOmegaDenominatorExponent hu_at_t
  omega

/-- Entrywise `k`-residue relation for a `2 x 2` matrix. -/
def MatrixHasResidueAtLevel (U : Square 2) (k : ℕ)
    (R : Matrix (Fin 2) (Fin 2) Residue) : Prop :=
  ∀ i j : Fin 2, HasResidueAtLevel (U i j) k (R i j)

/-- Every entry of a matrix has an omega-denominator presentation at level `k`. -/
def MatrixHasOmegaDenominatorExponent (U : Square 2) (k : ℕ) : Prop :=
  ∀ i j : Fin 2, HasOmegaDenominatorExponent (U i j) k

/-- `k` is the least omega-denominator exponent of a `2 x 2` matrix, exactly
as in Giles-Selinger's U(2) denominator-exponent definition. -/
def MatrixLeastOmegaDenominatorExponent (U : Square 2) (k : ℕ) : Prop :=
  MatrixHasOmegaDenominatorExponent U k ∧
    ∀ l : ℕ, MatrixHasOmegaDenominatorExponent U l → k ≤ l

@[simp] theorem completionMatrix_apply00 (u t : ℂ) :
    completionMatrix u t 0 0 = u := by
  simp [completionMatrix]

@[simp] theorem completionMatrix_apply01 (u t : ℂ) :
    completionMatrix u t 0 1 = -star t := by
  simp [completionMatrix]

@[simp] theorem completionMatrix_apply10 (u t : ℂ) :
    completionMatrix u t 1 0 = t := by
  simp [completionMatrix]

@[simp] theorem completionMatrix_apply11 (u t : ℂ) :
    completionMatrix u t 1 1 = star u := by
  simp [completionMatrix]

abbrev ResidueMatrix := Matrix (Fin 2) (Fin 2) Residue

namespace ResidueMatrix

def ofRows
    (a00 a01 a10 a11 : Residue) : ResidueMatrix :=
  fun i j =>
    if i = 0 then
      if j = 0 then a00 else a01
    else
      if j = 0 then a10 else a11

@[simp] theorem ofRows_apply00
    (a00 a01 a10 a11 : Residue) :
    ofRows a00 a01 a10 a11 0 0 = a00 := by
  simp [ofRows]

@[simp] theorem ofRows_apply01
    (a00 a01 a10 a11 : Residue) :
    ofRows a00 a01 a10 a11 0 1 = a01 := by
  simp [ofRows]

@[simp] theorem ofRows_apply10
    (a00 a01 a10 a11 : Residue) :
    ofRows a00 a01 a10 a11 1 0 = a10 := by
  simp [ofRows]

@[simp] theorem ofRows_apply11
    (a00 a01 a10 a11 : Residue) :
    ofRows a00 a01 a10 a11 1 1 = a11 := by
  simp [ofRows]

/-- A matrix with omega-denominator presentations has a residue matrix at that
level. -/
theorem exists_matrixHasResidueAtLevel_of_matrixHasOmegaDenominatorExponent
    {U : Square 2} {k : ℕ}
    (hU : MatrixHasOmegaDenominatorExponent U k) :
    ∃ R : ResidueMatrix, MatrixHasResidueAtLevel U k R := by
  rcases exists_hasResidueAtLevel_of_hasOmegaDenominatorExponent (hU 0 0) with
    ⟨r00, hr00⟩
  rcases exists_hasResidueAtLevel_of_hasOmegaDenominatorExponent (hU 0 1) with
    ⟨r01, hr01⟩
  rcases exists_hasResidueAtLevel_of_hasOmegaDenominatorExponent (hU 1 0) with
    ⟨r10, hr10⟩
  rcases exists_hasResidueAtLevel_of_hasOmegaDenominatorExponent (hU 1 1) with
    ⟨r11, hr11⟩
  refine ⟨ofRows r00 r01 r10 r11, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp [ofRows, *]

def omegaMul (M : ResidueMatrix) : ResidueMatrix :=
  fun i j => Residue.omegaMul (M i j)

/-- Residue action of left multiplication by `T = diag(1,ω)`: the second row
is multiplied by `ω`. -/
def leftT (M : ResidueMatrix) : ResidueMatrix :=
  fun i j => if i = 1 then Residue.omegaMul (M i j) else M i j

/-- Residue action of left multiplication by `S = T² = diag(1,ω²)`: the second
row is multiplied by `ω²`. -/
def leftS (M : ResidueMatrix) : ResidueMatrix :=
  fun i j => if i = 1 then Residue.omegaPowMul 2 (M i j) else M i j

/-- The residue action of a Figure 2 `H, k++` edge.  Multiplying by
`H = (1 / √2) [[1,1],[1,-1]]` and then displaying the result at the increased
denominator level sends both rows to the mod-`2` row sum; the sign in the
second row disappears modulo `2`. -/
def leftH_Kpp (M : ResidueMatrix) : ResidueMatrix :=
  fun _ j => Residue.add (M 0 j) (M 1 j)

def secondColumnSMul (M : ResidueMatrix) : ResidueMatrix :=
  fun i j => if j = 1 then Residue.omegaPowMul 2 (M i j) else M i j

def swapColumns (M : ResidueMatrix) : ResidueMatrix :=
  fun i j => if j = 0 then M i 1 else M i 0

/-- The generated right-action equivalence from Giles-Selinger's group
`S = <S, X, omega>`, stated as an inductive relation so later Figure 2 proofs
can use only the generators actually needed. -/
inductive RightEquivalent : ResidueMatrix → ResidueMatrix → Prop
  | refl (M) : RightEquivalent M M
  | omega (M) : RightEquivalent M (omegaMul M)
  | s (M) : RightEquivalent M (secondColumnSMul M)
  | x (M) : RightEquivalent M (swapColumns M)
  | symm {M N} : RightEquivalent M N → RightEquivalent N M
  | trans {M N P} : RightEquivalent M N → RightEquivalent N P →
      RightEquivalent M P

end ResidueMatrix

private theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left
    rfl
  · right
    rfl

private theorem Residue.bitOfInt_add (a b : ℤ) :
    Residue.bitOfInt (a + b) =
      Bool.xor (Residue.bitOfInt a) (Residue.bitOfInt b) := by
  unfold Residue.bitOfInt
  rcases zmod2_eq_zero_or_one (a : ZMod 2) with ha | ha
  · rcases zmod2_eq_zero_or_one (b : ZMod 2) with hb | hb
    · simp [Int.cast_add, ha, hb]
    · simp [Int.cast_add, ha, hb]
  · rcases zmod2_eq_zero_or_one (b : ZMod 2) with hb | hb
    · simp [Int.cast_add, ha, hb]
    · simp [Int.cast_add, ha, hb]

theorem residue_omegaMulCoord (x : OmegaIntCoord) :
    Residue.ofOmegaIntCoord (OmegaIntCoord.omegaMul x) =
      Residue.omegaMul (Residue.ofOmegaIntCoord x) := by
  cases x
  simp [Residue.ofOmegaIntCoord, Residue.omegaMul, OmegaIntCoord.omegaMul,
    Residue.ofBits]

theorem residue_omegaPowMulCoord (n : ℕ) (x : OmegaIntCoord) :
    Residue.ofOmegaIntCoord (OmegaIntCoord.omegaPowMul n x) =
      Residue.omegaPowMul n (Residue.ofOmegaIntCoord x) := by
  induction n with
  | zero =>
      simp [OmegaIntCoord.omegaPowMul, Residue.omegaPowMul]
  | succ n ih =>
      simp [OmegaIntCoord.omegaPowMul, Residue.omegaPowMul,
        residue_omegaMulCoord, ih]

theorem residue_addCoord (x y : OmegaIntCoord) :
    Residue.ofOmegaIntCoord (OmegaIntCoord.add x y) =
      Residue.add (Residue.ofOmegaIntCoord x) (Residue.ofOmegaIntCoord y) := by
  cases x
  cases y
  simp [Residue.ofOmegaIntCoord, Residue.add, OmegaIntCoord.add,
    Residue.ofBits, Residue.bitOfInt_add]

theorem residue_negCoord (x : OmegaIntCoord) :
    Residue.ofOmegaIntCoord (OmegaIntCoord.neg x) =
      Residue.ofOmegaIntCoord x := by
  cases x
  simp [Residue.ofOmegaIntCoord, OmegaIntCoord.neg, Residue.ofBits]

theorem hasResidueAtLevel_omegaMul
    {z : ℂ} {k : ℕ} {r : Residue}
    (h : HasResidueAtLevel z k r) :
    HasResidueAtLevel (rsOmegaAlg * z) k (Residue.omegaMul r) := by
  rcases h with ⟨x, hz, hr⟩
  refine ⟨OmegaIntCoord.omegaMul x, ?_, ?_⟩
  · rw [hz, OmegaIntCoord.val_omegaMul]
    ring
  · rw [residue_omegaMulCoord, hr]

theorem hasResidueAtLevel_omegaPowMul
    (n : ℕ) {z : ℂ} {k : ℕ} {r : Residue}
    (h : HasResidueAtLevel z k r) :
    HasResidueAtLevel (rsOmegaAlg ^ n * z) k (Residue.omegaPowMul n r) := by
  rcases h with ⟨x, hz, hr⟩
  refine ⟨OmegaIntCoord.omegaPowMul n x, ?_, ?_⟩
  · rw [hz, OmegaIntCoord.val_omegaPowMul]
    ring
  · rw [residue_omegaPowMulCoord, hr]

theorem hasResidueAtLevel_neg
    {z : ℂ} {k : ℕ} {r : Residue}
    (h : HasResidueAtLevel z k r) :
    HasResidueAtLevel (-z) k r := by
  rcases h with ⟨x, hz, hr⟩
  refine ⟨OmegaIntCoord.neg x, ?_, ?_⟩
  · rw [hz, OmegaIntCoord.val_neg]
    ring
  · rw [residue_negCoord, hr]

theorem hasResidueAtLevel_hadamard_sum
    {z w : ℂ} {k : ℕ} {rz rw : Residue}
    (hz : HasResidueAtLevel z k rz)
    (hw : HasResidueAtLevel w k rw) :
    HasResidueAtLevel ((z + w) / sqrtTwoComplex) (k + 1)
      (Residue.add rz rw) := by
  rcases hz with ⟨x, hzx, hrx⟩
  rcases hw with ⟨y, hwy, hry⟩
  refine ⟨OmegaIntCoord.add x y, ?_, ?_⟩
  · rw [hzx, hwy, OmegaIntCoord.val_add, pow_succ]
    field_simp [sqrtTwoComplex_ne_zero, pow_ne_zero k sqrtTwoComplex_ne_zero]
  · rw [residue_addCoord, hrx, hry]

theorem matrixHasResidueAtLevel_phaseT_mul
    {U : Square 2} {k : ℕ} {R : ResidueMatrix}
    (hU : MatrixHasResidueAtLevel U k R) :
    MatrixHasResidueAtLevel (TwoControl.Clifford.phaseT * U) k
      (ResidueMatrix.leftT R) := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [TwoControl.Clifford.phaseT, TwoControl.diag2,
      Matrix.mul_apply, Fin.sum_univ_two,
      ResidueMatrix.leftT] using hU 0 0
  · simpa [TwoControl.Clifford.phaseT, TwoControl.diag2,
      Matrix.mul_apply, Fin.sum_univ_two,
      ResidueMatrix.leftT] using hU 0 1
  · simpa [TwoControl.Clifford.phaseT, TwoControl.diag2,
      Matrix.mul_apply, Fin.sum_univ_two,
      ResidueMatrix.leftT, phaseT_scalar_eq_rsOmegaAlg] using
      hasResidueAtLevel_omegaMul (hU 1 0)
  · simpa [TwoControl.Clifford.phaseT, TwoControl.diag2,
      Matrix.mul_apply, Fin.sum_univ_two,
      ResidueMatrix.leftT, phaseT_scalar_eq_rsOmegaAlg] using
      hasResidueAtLevel_omegaMul (hU 1 1)

theorem matrixHasResidueAtLevel_phaseS_mul
    {U : Square 2} {k : ℕ} {R : ResidueMatrix}
    (hU : MatrixHasResidueAtLevel U k R) :
    MatrixHasResidueAtLevel (TwoControl.Clifford.phaseS * U) k
      (ResidueMatrix.leftS R) := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [TwoControl.Clifford.phaseS, TwoControl.diag2,
      Matrix.mul_apply, Fin.sum_univ_two,
      ResidueMatrix.leftS] using hU 0 0
  · simpa [TwoControl.Clifford.phaseS, TwoControl.diag2,
      Matrix.mul_apply, Fin.sum_univ_two,
      ResidueMatrix.leftS] using hU 0 1
  · simpa [TwoControl.Clifford.phaseS, TwoControl.diag2,
      Matrix.mul_apply, Fin.sum_univ_two,
      ResidueMatrix.leftS, ← rsOmegaAlg_sq] using
      hasResidueAtLevel_omegaPowMul 2 (hU 1 0)
  · simpa [TwoControl.Clifford.phaseS, TwoControl.diag2,
      Matrix.mul_apply, Fin.sum_univ_two,
      ResidueMatrix.leftS, ← rsOmegaAlg_sq] using
      hasResidueAtLevel_omegaPowMul 2 (hU 1 1)

theorem matrixHasResidueAtLevel_hadamard_mul
    {U : Square 2} {k : ℕ} {R : ResidueMatrix}
    (hU : MatrixHasResidueAtLevel U k R) :
    MatrixHasResidueAtLevel (TwoControl.Clifford.hadamard2 * U) (k + 1)
      (ResidueMatrix.leftH_Kpp R) := by
  intro i j
  fin_cases i <;> fin_cases j
  · convert hasResidueAtLevel_hadamard_sum (hU 0 0) (hU 1 0) using 1
    simp [TwoControl.Clifford.hadamard2, Matrix.mul_apply, Fin.sum_univ_two,
      sqrtTwoComplex]
    ring
  · convert hasResidueAtLevel_hadamard_sum (hU 0 1) (hU 1 1) using 1
    simp [TwoControl.Clifford.hadamard2, Matrix.mul_apply, Fin.sum_univ_two,
      sqrtTwoComplex]
    ring
  · convert hasResidueAtLevel_hadamard_sum (hU 0 0)
      (hasResidueAtLevel_neg (hU 1 0)) using 1
    simp [TwoControl.Clifford.hadamard2, Matrix.mul_apply, Fin.sum_univ_two,
      sqrtTwoComplex]
    ring
  · convert hasResidueAtLevel_hadamard_sum (hU 0 1)
      (hasResidueAtLevel_neg (hU 1 1)) using 1
    simp [TwoControl.Clifford.hadamard2, Matrix.mul_apply, Fin.sum_univ_two,
      sqrtTwoComplex]
    ring

/-- The `k`-residue shape of a Ross-Selinger completion matrix.

If `u` has residue `ru` and `t` has residue `rt`, then

`completionMatrix u t = [[u, -t†], [t, u†]]`

has residue matrix `[[ru, rt†], [rt, ru†]]`, where `†` on residues is the
paper's bullet operation.  The minus sign in the top-right entry disappears
modulo `2`. -/
theorem completionMatrix_hasResidueAtLevel
    {u t : ℂ} {k : ℕ} {ru rt : Residue}
    (hu : HasResidueAtLevel u k ru)
    (ht : HasResidueAtLevel t k rt) :
    MatrixHasResidueAtLevel (completionMatrix u t) k
      (ResidueMatrix.ofRows ru (Residue.bullet rt)
        rt (Residue.bullet ru)) := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using hu
  · simpa using hasResidueAtLevel_neg_star ht
  · simpa using ht
  · simpa using hasResidueAtLevel_star hu

/-- If both entries of a Ross-Selinger completion have omega-denominator
presentations at level `k`, then the completion matrix has a completion-shaped
residue matrix at that level. -/
theorem completionMatrix_exists_residueAtLevel
    {u t : ℂ} {k : ℕ}
    (hu : HasOmegaDenominatorExponent u k)
    (ht : HasOmegaDenominatorExponent t k) :
    ∃ ru rt : Residue,
      MatrixHasResidueAtLevel (completionMatrix u t) k
        (ResidueMatrix.ofRows ru (Residue.bullet rt)
          rt (Residue.bullet ru)) := by
  rcases exists_hasResidueAtLevel_of_hasOmegaDenominatorExponent hu with
    ⟨ru, hru⟩
  rcases exists_hasResidueAtLevel_of_hasOmegaDenominatorExponent ht with
    ⟨rt, hrt⟩
  refine ⟨ru, rt, ?_⟩
  exact completionMatrix_hasResidueAtLevel (u := u) (t := t) hru hrt

/-- Denominator synchronization for Ross-Selinger completions.

If `u` is displayed at omega-denominator level `k`, `t ∈ D[ω]`, and
`u†u + t†t = 1`, then every entry of the completion matrix
`[[u, -t†], [t, u†]]` has an omega-denominator presentation at the same level
`k`. -/
theorem completionMatrix_hasOmegaDenominatorExponent
    {u t : ℂ} {k : ℕ}
    (hu : HasOmegaDenominatorExponent u k)
    (ht : InDyadicCyclotomic t)
    (hNorm : NormEquation u t) :
    MatrixHasOmegaDenominatorExponent (completionMatrix u t) k := by
  have ht_sync : HasOmegaDenominatorExponent t k :=
    hasOmegaDenominatorExponent_of_normEquation hu ht hNorm
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using hu
  · simpa using hasOmegaDenominatorExponent_neg_star ht_sync
  · simpa using ht_sync
  · simpa using hasOmegaDenominatorExponent_star hu

theorem completionMatrix_hasOmegaDenominatorExponent_legacy
    {u t : ℂ} {k : ℕ}
    (hu : HasDenominatorExponent u k)
    (ht : InDyadicCyclotomic t)
    (hNorm : NormEquation u t) :
    MatrixHasOmegaDenominatorExponent (completionMatrix u t) k :=
  completionMatrix_hasOmegaDenominatorExponent
    (hasOmegaDenominatorExponent_of_hasDenominatorExponent hu) ht hNorm

/-- A Ross-Selinger completion matrix has the same least omega-denominator
exponent as its top-left entry `u`.

This is the matrix-level denominator fact needed by the Giles-Selinger U(2)
Figure 2 theorem: the top-left entry forces the lower bound, and the norm
equation synchronizes the completion entry `t` at the same omega-denominator
level. -/
theorem completionMatrix_leastOmegaDenominatorExponent_of_normEquation
    {u t : ℂ}
    (hu : InDyadicCyclotomic u)
    (ht : InDyadicCyclotomic t)
    (hNorm : NormEquation u t) :
    MatrixLeastOmegaDenominatorExponent
      (completionMatrix u t) (omegaSDE u) := by
  have huOmega : InOmegaDyadicCyclotomic u :=
    inOmegaDyadicCyclotomic_of_inDyadicCyclotomic hu
  refine ⟨?_, ?_⟩
  · exact completionMatrix_hasOmegaDenominatorExponent
      (hasOmegaDenominatorExponent_omegaSDE huOmega) ht hNorm
  · intro l hMl
    have hul : HasOmegaDenominatorExponent u l := by
      simpa using hMl 0 0
    exact omegaSDE_le_of_hasOmegaDenominatorExponent hul

/-- The T-count relation printed at a Figure 2 vertex.  The node asserts
`t + tOffset = 2k`, under the displayed lower bound on `2k`. -/
structure Figure2Node where
  residue : ResidueMatrix
  tOffset : ℕ
  minTwoK : ℕ
deriving DecidableEq, Repr

namespace Figure2

open Residue
open ResidueMatrix

def start : Figure2Node :=
  ⟨ofRows r0001 r0000 r0000 r0001, 0, 0⟩

def r1c3 : Figure2Node :=
  ⟨ofRows r0001 r0000 r0000 r0010, 1, 0⟩

def r2c1 : Figure2Node :=
  ⟨ofRows r0001 r0001 r0001 r0001, 2, 2⟩

def r2c2 : Figure2Node :=
  ⟨ofRows r0001 r0001 r0100 r0100, 2, 2⟩

def r2c3 : Figure2Node :=
  ⟨ofRows r0001 r0010 r0001 r0010, 1, 2⟩

def r2c4 : Figure2Node :=
  ⟨ofRows r0001 r0010 r0100 r1000, 1, 2⟩

def r3c1 : Figure2Node :=
  ⟨ofRows r0001 r0001 r0010 r0010, 1, 2⟩

def r3c2 : Figure2Node :=
  ⟨ofRows r0001 r0001 r1000 r1000, 1, 2⟩

def r3c3 : Figure2Node :=
  ⟨ofRows r0001 r0010 r0010 r0100, 0, 2⟩

def r3c4 : Figure2Node :=
  ⟨ofRows r0001 r0010 r1000 r0001, 0, 2⟩

def r4c1 : Figure2Node :=
  ⟨ofRows r0011 r0011 r0011 r0011, 3, 4⟩

def r4c2 : Figure2Node :=
  ⟨ofRows r0011 r0011 r1100 r1100, 3, 4⟩

def r4c3 : Figure2Node :=
  ⟨ofRows r0011 r0110 r0011 r0110, 2, 4⟩

def r4c4 : Figure2Node :=
  ⟨ofRows r0011 r0110 r1100 r1001, 2, 4⟩

def r5c1 : Figure2Node :=
  ⟨ofRows r0011 r0011 r0110 r0110, 2, 4⟩

def r5c2 : Figure2Node :=
  ⟨ofRows r0011 r0011 r1001 r1001, 2, 4⟩

def r5c3 : Figure2Node :=
  ⟨ofRows r0011 r0110 r0110 r1100, 1, 4⟩

def r5c4 : Figure2Node :=
  ⟨ofRows r0011 r0110 r1001 r0011, 1, 4⟩

def r6c1 : Figure2Node :=
  ⟨ofRows r0101 r0101 r0101 r0101, 4, 6⟩

def r6c3 : Figure2Node :=
  ⟨ofRows r0101 r1010 r0101 r1010, 3, 6⟩

def r7c1 : Figure2Node :=
  ⟨ofRows r1000 r0111 r0111 r1000, 2, 4⟩

def r7c2 : Figure2Node :=
  ⟨ofRows r1000 r0111 r1101 r0010, 2, 4⟩

def r7c3 : Figure2Node :=
  ⟨ofRows r1000 r1110 r0111 r0001, 1, 4⟩

def r7c4 : Figure2Node :=
  ⟨ofRows r1000 r1110 r1101 r0100, 1, 4⟩

def r8c1 : Figure2Node :=
  ⟨ofRows r1000 r0111 r1110 r0001, 1, 4⟩

def r8c2 : Figure2Node :=
  ⟨ofRows r1000 r0111 r1011 r0100, 1, 4⟩

def r8c3 : Figure2Node :=
  ⟨ofRows r1000 r1110 r1110 r0010, 0, 4⟩

def r8c4 : Figure2Node :=
  ⟨ofRows r1000 r1110 r1011 r1000, 0, 4⟩

def levelOneNodes : List Figure2Node :=
  [r2c1, r2c2, r2c3, r2c4, r3c3, r3c4]

def positiveLevelNodes : List Figure2Node :=
  [r4c1, r4c2, r4c3, r4c4, r5c1, r5c2, r5c3, r5c4,
    r7c1, r7c2, r7c3, r7c4, r8c1, r8c2, r8c3, r8c4]

def nodes : List Figure2Node :=
  start :: levelOneNodes ++ positiveLevelNodes

end Figure2

namespace Figure2Node

/-- Level validity for the Figure 2 labels.  Vertices with `minTwoK = 0`
represent the start case `2k = 0`; the other encoded vertices use the
printed lower bound `minTwoK ≤ 2k`. -/
def ValidAtLevel (node : Figure2Node) (k : ℕ) : Prop :=
  node.minTwoK ≤ 2 * k ∧ (node.minTwoK = 0 → 2 * k = 0)

end Figure2Node

/-! ### Residue-level Figure 2 paths

The next definitions are deliberately finite.  They certify the Figure 2 paths
needed for Selinger Lemma 7.5 without building a general graph engine or
claiming circuit evaluation yet: each edge records the residue action and the
printed denominator-level move.
-/

inductive Figure2StepKind where
  | gateT
  | gateS
  | gateH_Kpp
  | reduceKmm
deriving DecidableEq, Repr

namespace Figure2StepKind

def word : Figure2StepKind → CliffordTCircuit
  | gateT => [RossSelingerPrimitive.t]
  | gateS => [RossSelingerPrimitive.s]
  | gateH_Kpp => [RossSelingerPrimitive.h]
  | reduceKmm => []

def tCost : Figure2StepKind → ℕ
  | gateT => 1
  | gateS => 0
  | gateH_Kpp => 0
  | reduceKmm => 0

@[simp] theorem TCount_word (kind : Figure2StepKind) :
    TCount kind.word = kind.tCost := by
  cases kind <;> rfl

theorem gateT_word_residue_action
    {U : Square 2} {k : ℕ} {R : ResidueMatrix}
    (hU : MatrixHasResidueAtLevel U k R) :
    MatrixHasResidueAtLevel
      (CliffordTCircuit.eval Figure2StepKind.gateT.word * U) k
      (ResidueMatrix.leftT R) := by
  simpa [Figure2StepKind.word, CliffordTCircuit.eval,
    RossSelingerPrimitive.eval] using
    matrixHasResidueAtLevel_phaseT_mul hU

theorem gateS_word_residue_action
    {U : Square 2} {k : ℕ} {R : ResidueMatrix}
    (hU : MatrixHasResidueAtLevel U k R) :
    MatrixHasResidueAtLevel
      (CliffordTCircuit.eval Figure2StepKind.gateS.word * U) k
      (ResidueMatrix.leftS R) := by
  simpa [Figure2StepKind.word, CliffordTCircuit.eval,
    RossSelingerPrimitive.eval] using
    matrixHasResidueAtLevel_phaseS_mul hU

theorem gateH_word_residue_action
    {U : Square 2} {k : ℕ} {R : ResidueMatrix}
    (hU : MatrixHasResidueAtLevel U k R) :
    MatrixHasResidueAtLevel
      (CliffordTCircuit.eval Figure2StepKind.gateH_Kpp.word * U) (k + 1)
      (ResidueMatrix.leftH_Kpp R) := by
  simpa [Figure2StepKind.word, CliffordTCircuit.eval,
    RossSelingerPrimitive.eval] using
    matrixHasResidueAtLevel_hadamard_mul hU

def ResidueAction : Figure2StepKind → ResidueMatrix → ResidueMatrix → Prop
  | gateT, source, target => ResidueMatrix.leftT source = target
  | gateS, source, target => ResidueMatrix.leftS source = target
  | gateH_Kpp, source, target => ResidueMatrix.leftH_Kpp source = target
  | reduceKmm, source, target =>
      (source = Figure2.r6c1.residue ∧ target = Figure2.r7c1.residue) ∨
        (source = Figure2.r6c3.residue ∧ target = Figure2.r7c3.residue)

def LevelAction : Figure2StepKind → ℕ → ℕ → Prop
  | gateT, sourceTwoK, targetTwoK => targetTwoK = sourceTwoK
  | gateS, sourceTwoK, targetTwoK => targetTwoK = sourceTwoK
  | gateH_Kpp, sourceTwoK, targetTwoK => targetTwoK = sourceTwoK + 2
  | reduceKmm, sourceTwoK, targetTwoK => sourceTwoK = targetTwoK + 2

end Figure2StepKind

structure Figure2EdgeCertificate (source target : Figure2Node) where
  kind : Figure2StepKind
  residue_ok :
    kind.ResidueAction source.residue target.residue
  level_ok :
    kind.LevelAction source.minTwoK target.minTwoK

inductive Figure2CertifiedPath : Figure2Node → Figure2Node → Type where
  | nil (node : Figure2Node) : Figure2CertifiedPath node node
  | cons {a b c : Figure2Node} :
      Figure2EdgeCertificate a b →
        Figure2CertifiedPath b c →
          Figure2CertifiedPath a c

def Figure2CertifiedPath.tCost :
    {source target : Figure2Node} →
      Figure2CertifiedPath source target → ℕ
  | _, _, Figure2CertifiedPath.nil _ => 0
  | _, _, Figure2CertifiedPath.cons edge rest =>
      edge.kind.tCost + Figure2CertifiedPath.tCost rest

def Figure2CertifiedPath.word :
    {source target : Figure2Node} →
      Figure2CertifiedPath source target → CliffordTCircuit
  | _, _, Figure2CertifiedPath.nil _ => []
  | _, _, Figure2CertifiedPath.cons edge rest =>
      edge.kind.word ++ Figure2CertifiedPath.word rest

@[simp] theorem Figure2CertifiedPath.TCount_word
    {source target : Figure2Node}
    (path : Figure2CertifiedPath source target) :
    TCount (Figure2CertifiedPath.word path) =
      Figure2CertifiedPath.tCost path := by
  induction path with
  | nil _ => rfl
  | cons edge rest ih =>
      simp [Figure2CertifiedPath.word, Figure2CertifiedPath.tCost,
        TCount_append, ih]

structure Figure2PathCertificate where
  target : Figure2Node
  path : Figure2CertifiedPath Figure2.start target
  target_mem : target ∈ Figure2.nodes

namespace Figure2PathCertificate

def word (cert : Figure2PathCertificate) : CliffordTCircuit :=
  cert.path.word

def tCost (cert : Figure2PathCertificate) : ℕ :=
  cert.path.tCost

@[simp] theorem TCount_word (cert : Figure2PathCertificate) :
    TCount cert.word = cert.tCost := by
  simp [word, tCost]

end Figure2PathCertificate

set_option linter.unnecessarySeqFocus false

namespace Figure2Edges

def T_start_r1c3 :
    Figure2EdgeCertificate Figure2.start Figure2.r1c3 where
  kind := Figure2StepKind.gateT
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def H_start_r2c1 :
    Figure2EdgeCertificate Figure2.start Figure2.r2c1 where
  kind := Figure2StepKind.gateH_Kpp
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def H_r1c3_r2c3 :
    Figure2EdgeCertificate Figure2.r1c3 Figure2.r2c3 where
  kind := Figure2StepKind.gateH_Kpp
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def S_r2c1_r2c2 :
    Figure2EdgeCertificate Figure2.r2c1 Figure2.r2c2 where
  kind := Figure2StepKind.gateS
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def S_r2c3_r2c4 :
    Figure2EdgeCertificate Figure2.r2c3 Figure2.r2c4 where
  kind := Figure2StepKind.gateS
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def T_r2c1_r3c1 :
    Figure2EdgeCertificate Figure2.r2c1 Figure2.r3c1 where
  kind := Figure2StepKind.gateT
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def T_r2c2_r3c2 :
    Figure2EdgeCertificate Figure2.r2c2 Figure2.r3c2 where
  kind := Figure2StepKind.gateT
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def T_r2c3_r3c3 :
    Figure2EdgeCertificate Figure2.r2c3 Figure2.r3c3 where
  kind := Figure2StepKind.gateT
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def T_r2c4_r3c4 :
    Figure2EdgeCertificate Figure2.r2c4 Figure2.r3c4 where
  kind := Figure2StepKind.gateT
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def H_r3c1_r4c1 :
    Figure2EdgeCertificate Figure2.r3c1 Figure2.r4c1 where
  kind := Figure2StepKind.gateH_Kpp
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def H_r3c3_r4c3 :
    Figure2EdgeCertificate Figure2.r3c3 Figure2.r4c3 where
  kind := Figure2StepKind.gateH_Kpp
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def S_r4c1_r4c2 :
    Figure2EdgeCertificate Figure2.r4c1 Figure2.r4c2 where
  kind := Figure2StepKind.gateS
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def S_r4c3_r4c4 :
    Figure2EdgeCertificate Figure2.r4c3 Figure2.r4c4 where
  kind := Figure2StepKind.gateS
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def T_r4c1_r5c1 :
    Figure2EdgeCertificate Figure2.r4c1 Figure2.r5c1 where
  kind := Figure2StepKind.gateT
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def T_r4c2_r5c2 :
    Figure2EdgeCertificate Figure2.r4c2 Figure2.r5c2 where
  kind := Figure2StepKind.gateT
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def T_r4c3_r5c3 :
    Figure2EdgeCertificate Figure2.r4c3 Figure2.r5c3 where
  kind := Figure2StepKind.gateT
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def T_r4c4_r5c4 :
    Figure2EdgeCertificate Figure2.r4c4 Figure2.r5c4 where
  kind := Figure2StepKind.gateT
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def H_r5c1_r6c1 :
    Figure2EdgeCertificate Figure2.r5c1 Figure2.r6c1 where
  kind := Figure2StepKind.gateH_Kpp
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def H_r5c3_r6c3 :
    Figure2EdgeCertificate Figure2.r5c3 Figure2.r6c3 where
  kind := Figure2StepKind.gateH_Kpp
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def Reduce_r6c1_r7c1 :
    Figure2EdgeCertificate Figure2.r6c1 Figure2.r7c1 where
  kind := Figure2StepKind.reduceKmm
  residue_ok := by
    left
    exact ⟨rfl, rfl⟩
  level_ok := by rfl

def Reduce_r6c3_r7c3 :
    Figure2EdgeCertificate Figure2.r6c3 Figure2.r7c3 where
  kind := Figure2StepKind.reduceKmm
  residue_ok := by
    right
    exact ⟨rfl, rfl⟩
  level_ok := by rfl

def S_r7c1_r7c2 :
    Figure2EdgeCertificate Figure2.r7c1 Figure2.r7c2 where
  kind := Figure2StepKind.gateS
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def S_r7c3_r7c4 :
    Figure2EdgeCertificate Figure2.r7c3 Figure2.r7c4 where
  kind := Figure2StepKind.gateS
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def T_r7c1_r8c1 :
    Figure2EdgeCertificate Figure2.r7c1 Figure2.r8c1 where
  kind := Figure2StepKind.gateT
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def T_r7c2_r8c2 :
    Figure2EdgeCertificate Figure2.r7c2 Figure2.r8c2 where
  kind := Figure2StepKind.gateT
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def T_r7c3_r8c3 :
    Figure2EdgeCertificate Figure2.r7c3 Figure2.r8c3 where
  kind := Figure2StepKind.gateT
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

def T_r7c4_r8c4 :
    Figure2EdgeCertificate Figure2.r7c4 Figure2.r8c4 where
  kind := Figure2StepKind.gateT
  residue_ok := by
    ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  level_ok := by rfl

end Figure2Edges

namespace Figure2Paths

open Figure2CertifiedPath
open Figure2Edges

def start : Figure2PathCertificate where
  target := Figure2.start
  path := nil Figure2.start
  target_mem := by simp [Figure2.nodes]

def r2c1 : Figure2PathCertificate where
  target := Figure2.r2c1
  path := cons H_start_r2c1 (nil Figure2.r2c1)
  target_mem := by simp [Figure2.nodes, Figure2.levelOneNodes]

def r3c4 : Figure2PathCertificate where
  target := Figure2.r3c4
  path :=
    cons T_start_r1c3 <|
      cons H_r1c3_r2c3 <|
        cons S_r2c3_r2c4 <|
          cons T_r2c4_r3c4 (nil Figure2.r3c4)
  target_mem := by simp [Figure2.nodes, Figure2.levelOneNodes]

def r4c4 : Figure2PathCertificate where
  target := Figure2.r4c4
  path :=
    cons T_start_r1c3 <|
      cons H_r1c3_r2c3 <|
        cons T_r2c3_r3c3 <|
          cons H_r3c3_r4c3 <|
            cons S_r4c3_r4c4 (nil Figure2.r4c4)
  target_mem := by simp [Figure2.nodes, Figure2.positiveLevelNodes]

def r5c2 : Figure2PathCertificate where
  target := Figure2.r5c2
  path :=
    cons H_start_r2c1 <|
      cons T_r2c1_r3c1 <|
        cons H_r3c1_r4c1 <|
          cons S_r4c1_r4c2 <|
            cons T_r4c2_r5c2 (nil Figure2.r5c2)
  target_mem := by simp [Figure2.nodes, Figure2.positiveLevelNodes]

def r7c2 : Figure2PathCertificate where
  target := Figure2.r7c2
  path :=
    cons H_start_r2c1 <|
      cons T_r2c1_r3c1 <|
        cons H_r3c1_r4c1 <|
          cons T_r4c1_r5c1 <|
            cons H_r5c1_r6c1 <|
              cons Reduce_r6c1_r7c1 <|
                cons S_r7c1_r7c2 (nil Figure2.r7c2)
  target_mem := by simp [Figure2.nodes, Figure2.positiveLevelNodes]

def r8c3 : Figure2PathCertificate where
  target := Figure2.r8c3
  path :=
    cons T_start_r1c3 <|
      cons H_r1c3_r2c3 <|
        cons T_r2c3_r3c3 <|
          cons H_r3c3_r4c3 <|
            cons T_r4c3_r5c3 <|
              cons H_r5c3_r6c3 <|
                cons Reduce_r6c3_r7c3 <|
                  cons T_r7c3_r8c3 (nil Figure2.r8c3)
  target_mem := by simp [Figure2.nodes, Figure2.positiveLevelNodes]

end Figure2Paths

@[simp] private theorem Figure2Paths_start_tCost :
    Figure2Paths.start.tCost = 0 := by
  rfl

@[simp] private theorem Figure2Paths_start_target_tOffset :
    Figure2Paths.start.target.tOffset = 0 := by
  rfl

@[simp] private theorem Figure2Paths_r2c1_tCost :
    Figure2Paths.r2c1.tCost = 0 := by
  rfl

@[simp] private theorem Figure2Paths_r2c1_target_tOffset :
    Figure2Paths.r2c1.target.tOffset = 2 := by
  rfl

@[simp] private theorem Figure2Paths_r3c4_tCost :
    Figure2Paths.r3c4.tCost = 2 := by
  rfl

@[simp] private theorem Figure2Paths_r3c4_target_tOffset :
    Figure2Paths.r3c4.target.tOffset = 0 := by
  rfl

@[simp] private theorem Figure2Paths_r4c4_tCost :
    Figure2Paths.r4c4.tCost = 2 := by
  rfl

@[simp] private theorem Figure2Paths_r4c4_target_tOffset :
    Figure2Paths.r4c4.target.tOffset = 2 := by
  rfl

@[simp] private theorem Figure2Paths_r5c2_tCost :
    Figure2Paths.r5c2.tCost = 2 := by
  rfl

@[simp] private theorem Figure2Paths_r5c2_target_tOffset :
    Figure2Paths.r5c2.target.tOffset = 2 := by
  rfl

@[simp] private theorem Figure2Paths_r7c2_tCost :
    Figure2Paths.r7c2.tCost = 2 := by
  rfl

@[simp] private theorem Figure2Paths_r7c2_target_tOffset :
    Figure2Paths.r7c2.target.tOffset = 2 := by
  rfl

@[simp] private theorem Figure2Paths_r8c3_tCost :
    Figure2Paths.r8c3.tCost = 4 := by
  rfl

@[simp] private theorem Figure2Paths_r8c3_target_tOffset :
    Figure2Paths.r8c3.target.tOffset = 0 := by
  rfl

inductive Figure2SelectedCompletionPath : Figure2PathCertificate → Prop where
  | start : Figure2SelectedCompletionPath Figure2Paths.start
  | r2c1 : Figure2SelectedCompletionPath Figure2Paths.r2c1
  | r3c4 : Figure2SelectedCompletionPath Figure2Paths.r3c4
  | r4c4 : Figure2SelectedCompletionPath Figure2Paths.r4c4
  | r5c2 : Figure2SelectedCompletionPath Figure2Paths.r5c2
  | r7c2 : Figure2SelectedCompletionPath Figure2Paths.r7c2
  | r8c3 : Figure2SelectedCompletionPath Figure2Paths.r8c3

/-- The subset of selected paths that can occur as branch targets in
`figure2_completion_branch`. -/
inductive Figure2BranchPath : Figure2PathCertificate → Prop where
  | start : Figure2BranchPath Figure2Paths.start
  | r2c1 : Figure2BranchPath Figure2Paths.r2c1
  | r4c4 : Figure2BranchPath Figure2Paths.r4c4
  | r5c2 : Figure2BranchPath Figure2Paths.r5c2
  | r7c2 : Figure2BranchPath Figure2Paths.r7c2

/-- Selected Figure 2 path-to-word synthesis for the completion-shaped
vertices used by Selinger Lemma 7.5.

This theorem is intentionally scoped to the seven selected vertices.  It turns
their certified Figure 2 paths into concrete Clifford+T words and proves the
printed `t + offset = 2k` T-count bound.  Reduction edges contribute no gate:
they certify denominator normalization, not a left multiplication by a physical
generator. -/
theorem figure2_selected_node_synthesizes
    {cert : Figure2PathCertificate}
    (hselected : Figure2SelectedCompletionPath cert)
    {k : ℕ}
    (hvalid : cert.target.ValidAtLevel k) :
    ∃ C : CliffordTCircuit,
      C = cert.word ∧
        TCount C = cert.tCost ∧
          TCount C ≤ 2 * k - cert.target.tOffset := by
  cases hselected
  · refine ⟨Figure2PathCertificate.word Figure2Paths.start, rfl, ?_, ?_⟩
    · exact Figure2PathCertificate.TCount_word Figure2Paths.start
    · have hk0 : 2 * k = 0 := hvalid.2 (by rfl)
      have hT := Figure2PathCertificate.TCount_word Figure2Paths.start
      rw [hT]
      simp
  · refine ⟨Figure2PathCertificate.word Figure2Paths.r2c1, rfl, ?_, ?_⟩
    · exact Figure2PathCertificate.TCount_word Figure2Paths.r2c1
    · have hT := Figure2PathCertificate.TCount_word Figure2Paths.r2c1
      rw [hT]
      simp
  · refine ⟨Figure2PathCertificate.word Figure2Paths.r3c4, rfl, ?_, ?_⟩
    · exact Figure2PathCertificate.TCount_word Figure2Paths.r3c4
    · have hmin : 2 ≤ 2 * k := by
        simpa [Figure2Paths.r3c4, Figure2.r3c4] using hvalid.1
      have hT := Figure2PathCertificate.TCount_word Figure2Paths.r3c4
      rw [hT]
      simp
      omega
  · refine ⟨Figure2PathCertificate.word Figure2Paths.r4c4, rfl, ?_, ?_⟩
    · exact Figure2PathCertificate.TCount_word Figure2Paths.r4c4
    · have hmin : 4 ≤ 2 * k := by
        simpa [Figure2Paths.r4c4, Figure2.r4c4] using hvalid.1
      have hT := Figure2PathCertificate.TCount_word Figure2Paths.r4c4
      rw [hT]
      simp
      omega
  · refine ⟨Figure2PathCertificate.word Figure2Paths.r5c2, rfl, ?_, ?_⟩
    · exact Figure2PathCertificate.TCount_word Figure2Paths.r5c2
    · have hmin : 4 ≤ 2 * k := by
        simpa [Figure2Paths.r5c2, Figure2.r5c2] using hvalid.1
      have hT := Figure2PathCertificate.TCount_word Figure2Paths.r5c2
      rw [hT]
      simp
      omega
  · refine ⟨Figure2PathCertificate.word Figure2Paths.r7c2, rfl, ?_, ?_⟩
    · exact Figure2PathCertificate.TCount_word Figure2Paths.r7c2
    · have hmin : 4 ≤ 2 * k := by
        simpa [Figure2Paths.r7c2, Figure2.r7c2] using hvalid.1
      have hT := Figure2PathCertificate.TCount_word Figure2Paths.r7c2
      rw [hT]
      simp
      omega
  · refine ⟨Figure2PathCertificate.word Figure2Paths.r8c3, rfl, ?_, ?_⟩
    · exact Figure2PathCertificate.TCount_word Figure2Paths.r8c3
    · have hmin : 4 ≤ 2 * k := by
        simpa [Figure2Paths.r8c3, Figure2.r8c3] using hvalid.1
      have hT := Figure2PathCertificate.TCount_word Figure2Paths.r8c3
      rw [hT]
      simp
      omega

/-- Selected-path synthesis specialized to Figure 2 branch targets, yielding
the Ross-Selinger branch bound directly. -/
theorem figure2_branch_path_synthesizes
    {cert : Figure2PathCertificate}
    (hbranchPath : Figure2BranchPath cert)
    {k : ℕ}
    (hvalid : cert.target.ValidAtLevel k) :
    ∃ C : CliffordTCircuit,
      C = cert.word ∧
        TCount C ≤ rossLevelTCount k := by
  rcases figure2_selected_node_synthesizes
      (cert := cert)
      (hselected := by
        cases hbranchPath with
        | start => exact Figure2SelectedCompletionPath.start
        | r2c1 => exact Figure2SelectedCompletionPath.r2c1
        | r4c4 => exact Figure2SelectedCompletionPath.r4c4
        | r5c2 => exact Figure2SelectedCompletionPath.r5c2
        | r7c2 => exact Figure2SelectedCompletionPath.r7c2)
      hvalid with ⟨C, hC, hT, hBound⟩
  refine ⟨C, hC, ?_⟩
  cases hbranchPath with
  | start =>
      have hk0 : k = 0 := by
        have h2k0 : 2 * k = 0 := hvalid.2 (by rfl)
        omega
      rw [hT]
      simp [rossLevelTCount, hk0]
  | r2c1 =>
      have hmin : 2 ≤ 2 * k := by
        simpa [Figure2Paths.r2c1, Figure2.r2c1] using hvalid.1
      have hoff : Figure2Paths.r2c1.target.tOffset = 2 := rfl
      exact hBound.trans (by
        rw [hoff]
        unfold rossLevelTCount
        split <;> omega)
  | r4c4 =>
      have hmin : 4 ≤ 2 * k := by
        simpa [Figure2Paths.r4c4, Figure2.r4c4] using hvalid.1
      have hoff : Figure2Paths.r4c4.target.tOffset = 2 := rfl
      exact hBound.trans (by
        rw [hoff]
        unfold rossLevelTCount
        split <;> omega)
  | r5c2 =>
      have hmin : 4 ≤ 2 * k := by
        simpa [Figure2Paths.r5c2, Figure2.r5c2] using hvalid.1
      have hoff : Figure2Paths.r5c2.target.tOffset = 2 := rfl
      exact hBound.trans (by
        rw [hoff]
        unfold rossLevelTCount
        split <;> omega)
  | r7c2 =>
      have hmin : 4 ≤ 2 * k := by
        simpa [Figure2Paths.r7c2, Figure2.r7c2] using hvalid.1
      have hoff : Figure2Paths.r7c2.target.tOffset = 2 := rfl
      exact hBound.trans (by
        rw [hoff]
        unfold rossLevelTCount
        split <;> omega)

inductive Figure2Branch where
  | direct
  | phaseT
deriving DecidableEq, Repr

namespace Figure2Branch

def completionResidue (ru rt : Residue) : ResidueMatrix :=
  ResidueMatrix.ofRows ru (Residue.bullet rt) rt (Residue.bullet ru)

def branchResidue : Figure2Branch → Residue → Residue → ResidueMatrix
  | direct, ru, rt => completionResidue ru rt
  | phaseT, ru, rt => completionResidue ru (Residue.omegaMul rt)

end Figure2Branch

/-- A Figure 2 branch certificate for a completion-shaped residue class.

The `direct` branch uses the completion matrix residue itself.  The `phaseT`
branch uses the residue of `T U T†`, which keeps `u` fixed and rotates the
completion entry `t` by `ω`.  The certificate records the Figure 2 vertex and
the arithmetic inequality that its printed `t + offset = 2k` label gives the
Ross-Selinger branch bound. -/
def Figure2BranchCertificate
    (k : ℕ) (ru rt : Residue) : Prop :=
  ∃ (branch : Figure2Branch) (node : Figure2Node),
    node ∈ Figure2.nodes ∧
      node.residue = Figure2Branch.branchResidue branch ru rt ∧
        node.minTwoK ≤ 2 * k ∧
          2 * k - node.tOffset ≤ rossLevelTCount k

private theorem figure2_cert_start {k : ℕ}
    (hzero : 2 * k = 0) :
    Figure2BranchCertificate k Residue.r0001 Residue.r0000 := by
  refine ⟨Figure2Branch.direct, Figure2.start, ?_, ?_, ?_, ?_⟩
  · simp [Figure2.nodes, Figure2.start]
  · decide
  · simp [Figure2.start]
  · have hk : k = 0 := by omega
    simp [Figure2.start, rossLevelTCount, hk]

private theorem figure2_cert_level_one_direct {k : ℕ}
    (hmin : 2 ≤ 2 * k) :
    Figure2BranchCertificate k Residue.r0001 Residue.r0001 := by
  let node : Figure2Node :=
    ⟨ResidueMatrix.ofRows Residue.r0001 Residue.r0001
      Residue.r0001 Residue.r0001, 2, 2⟩
  refine ⟨Figure2Branch.direct, node, ?_, ?_, hmin, ?_⟩
  · simp [node, Figure2.nodes, Figure2.levelOneNodes, Figure2.r2c1]
  · decide
  · unfold rossLevelTCount
    change 2 * k - 2 ≤ if k = 0 then 0 else 2 * k - 2
    split <;> omega

private theorem figure2_cert_level_one_phase {k : ℕ}
    (hmin : 2 ≤ 2 * k) :
    Figure2BranchCertificate k Residue.r0001 Residue.r1000 := by
  let node : Figure2Node :=
    ⟨ResidueMatrix.ofRows Residue.r0001 Residue.r0001
      Residue.r0001 Residue.r0001, 2, 2⟩
  refine ⟨Figure2Branch.phaseT, node, ?_, ?_, hmin, ?_⟩
  · simp [node, Figure2.nodes, Figure2.levelOneNodes, Figure2.r2c1]
  · decide
  · unfold rossLevelTCount
    change 2 * k - 2 ≤ if k = 0 then 0 else 2 * k - 2
    split <;> omega

private theorem figure2_cert_pos_direct_0011_1100 {k : ℕ}
    (hmin : 4 ≤ 2 * k) :
    Figure2BranchCertificate k Residue.r0011 Residue.r1100 := by
  let node : Figure2Node :=
    ⟨ResidueMatrix.ofRows Residue.r0011 Residue.r0110
      Residue.r1100 Residue.r1001, 2, 4⟩
  refine ⟨Figure2Branch.direct, node, ?_, ?_, hmin, ?_⟩
  · simp [node, Figure2.nodes, Figure2.positiveLevelNodes, Figure2.r4c4]
  · decide
  · unfold rossLevelTCount
    change 2 * k - 2 ≤ if k = 0 then 0 else 2 * k - 2
    split <;> omega

private theorem figure2_cert_pos_direct_0011_1001 {k : ℕ}
    (hmin : 4 ≤ 2 * k) :
    Figure2BranchCertificate k Residue.r0011 Residue.r1001 := by
  let node : Figure2Node :=
    ⟨ResidueMatrix.ofRows Residue.r0011 Residue.r0011
      Residue.r1001 Residue.r1001, 2, 4⟩
  refine ⟨Figure2Branch.direct, node, ?_, ?_, hmin, ?_⟩
  · simp [node, Figure2.nodes, Figure2.positiveLevelNodes, Figure2.r5c2]
  · decide
  · unfold rossLevelTCount
    change 2 * k - 2 ≤ if k = 0 then 0 else 2 * k - 2
    split <;> omega

private theorem figure2_cert_pos_direct_1000_1101 {k : ℕ}
    (hmin : 4 ≤ 2 * k) :
    Figure2BranchCertificate k Residue.r1000 Residue.r1101 := by
  let node : Figure2Node :=
    ⟨ResidueMatrix.ofRows Residue.r1000 Residue.r0111
      Residue.r1101 Residue.r0010, 2, 4⟩
  refine ⟨Figure2Branch.direct, node, ?_, ?_, hmin, ?_⟩
  · simp [node, Figure2.nodes, Figure2.positiveLevelNodes, Figure2.r7c2]
  · decide
  · unfold rossLevelTCount
    change 2 * k - 2 ≤ if k = 0 then 0 else 2 * k - 2
    split <;> omega

private theorem figure2_cert_pos_phase_1000_1110 {k : ℕ}
    (hmin : 4 ≤ 2 * k) :
    Figure2BranchCertificate k Residue.r1000 Residue.r1110 := by
  let node : Figure2Node :=
    ⟨ResidueMatrix.ofRows Residue.r1000 Residue.r0111
      Residue.r1101 Residue.r0010, 2, 4⟩
  refine ⟨Figure2Branch.phaseT, node, ?_, ?_, hmin, ?_⟩
  · simp [node, Figure2.nodes, Figure2.positiveLevelNodes, Figure2.r7c2]
  · decide
  · unfold rossLevelTCount
    change 2 * k - 2 ≤ if k = 0 then 0 else 2 * k - 2
    split <;> omega

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- The finite Figure 2 branch theorem for completion-shaped residues.

If a completion-shaped residue matrix occurs at a Figure 2 vertex valid for
level `k`, then either that vertex itself or the `T U T†` branch has the sharp
Ross-Selinger `T`-count bound.  The proof is the finite table check from
Figure 2: the bad completion vertices with offset `0` are exactly repaired by
rotating `t` once by `ω`. -/
theorem figure2_completion_branch
    {k : ℕ} {ru rt : Residue} {node : Figure2Node}
    (hnode : node ∈ Figure2.nodes)
    (hres :
      node.residue = Figure2Branch.completionResidue ru rt)
    (hvalid : node.ValidAtLevel k) :
    Figure2BranchCertificate k ru rt := by
  have hmin : node.minTwoK ≤ 2 * k := hvalid.1
  have hstart : node.minTwoK = 0 → 2 * k = 0 := hvalid.2
  simp [Figure2.nodes, Figure2.start, Figure2.levelOneNodes,
    Figure2.positiveLevelNodes] at hnode
  rcases hnode with hnode | hnode | hnode | hnode | hnode | hnode |
    hnode | hnode | hnode | hnode | hnode | hnode | hnode | hnode |
    hnode | hnode | hnode | hnode | hnode | hnode | hnode | hnode |
    hnode
  all_goals
    subst node
    rcases ru with ⟨p₁, q₁, r₁, s₁⟩
    rcases rt with ⟨p₂, q₂, r₂, s₂⟩
    cases p₁ <;> cases q₁ <;> cases r₁ <;> cases s₁ <;>
      cases p₂ <;> cases q₂ <;> cases r₂ <;> cases s₂ <;>
        simp only [Figure2Branch.completionResidue,
          Figure2Branch.branchResidue, ResidueMatrix.ofRows,
          Residue.bullet, Residue.omegaMul, Residue.ofBits,
          Residue.r0000, Residue.r0001, Residue.r0010, Residue.r0011,
          Residue.r0100, Residue.r0101, Residue.r0110, Residue.r0111,
          Residue.r1000, Residue.r1001, Residue.r1010, Residue.r1011,
          Residue.r1100, Residue.r1101, Residue.r1110, Residue.r1111] at hres
    all_goals try contradiction
    all_goals first
      | exact figure2_cert_start (hstart (by rfl))
      | exact figure2_cert_level_one_direct (by
          simpa [Figure2.r2c1, Figure2.r2c2, Figure2.r2c3, Figure2.r2c4,
            Figure2.r3c3, Figure2.r3c4] using hmin)
      | exact figure2_cert_level_one_phase (by
          simpa [Figure2.r2c1, Figure2.r2c2, Figure2.r2c3, Figure2.r2c4,
            Figure2.r3c3, Figure2.r3c4] using hmin)
      | exact figure2_cert_pos_direct_0011_1100 (by
          simpa [Figure2.r4c1, Figure2.r4c2, Figure2.r4c3, Figure2.r4c4,
            Figure2.r5c1, Figure2.r5c2, Figure2.r5c3, Figure2.r5c4,
            Figure2.r7c1, Figure2.r7c2, Figure2.r7c3, Figure2.r7c4,
            Figure2.r8c1, Figure2.r8c2, Figure2.r8c3, Figure2.r8c4] using hmin)
      | exact figure2_cert_pos_direct_0011_1001 (by
          simpa [Figure2.r4c1, Figure2.r4c2, Figure2.r4c3, Figure2.r4c4,
            Figure2.r5c1, Figure2.r5c2, Figure2.r5c3, Figure2.r5c4,
            Figure2.r7c1, Figure2.r7c2, Figure2.r7c3, Figure2.r7c4,
            Figure2.r8c1, Figure2.r8c2, Figure2.r8c3, Figure2.r8c4] using hmin)
      | exact figure2_cert_pos_direct_1000_1101 (by
          simpa [Figure2.r4c1, Figure2.r4c2, Figure2.r4c3, Figure2.r4c4,
            Figure2.r5c1, Figure2.r5c2, Figure2.r5c3, Figure2.r5c4,
            Figure2.r7c1, Figure2.r7c2, Figure2.r7c3, Figure2.r7c4,
            Figure2.r8c1, Figure2.r8c2, Figure2.r8c3, Figure2.r8c4] using hmin)
      | exact figure2_cert_pos_phase_1000_1110 (by
          simpa [Figure2.r4c1, Figure2.r4c2, Figure2.r4c3, Figure2.r4c4,
            Figure2.r5c1, Figure2.r5c2, Figure2.r5c3, Figure2.r5c4,
            Figure2.r7c1, Figure2.r7c2, Figure2.r7c3, Figure2.r7c4,
            Figure2.r8c1, Figure2.r8c2, Figure2.r8c3, Figure2.r8c4] using hmin)

/-- A branch-certificate witness upgraded with an explicit selected Figure 2
path certificate that carries a concrete Clifford+T word and its printed
`2k - offset` T-count relation. -/
def Figure2BranchPathWitness
    (k : ℕ) (ru rt : Residue) : Prop :=
  ∃ (branch : Figure2Branch) (cert : Figure2PathCertificate),
    Figure2SelectedCompletionPath cert ∧
      cert.target.residue = Figure2Branch.branchResidue branch ru rt ∧
        cert.target.ValidAtLevel k ∧
          2 * k - cert.target.tOffset ≤ rossLevelTCount k

private theorem figure2_witness_start {k : ℕ}
    (hvalid : Figure2.start.ValidAtLevel k)
    (hzero : 2 * k = 0) :
    Figure2BranchPathWitness k Residue.r0001 Residue.r0000 := by
  refine ⟨Figure2Branch.direct, Figure2Paths.start,
    Figure2SelectedCompletionPath.start, ?_, ?_, ?_⟩
  · decide
  · simpa [Figure2Paths.start, Figure2.start] using hvalid
  · have hk : k = 0 := by omega
    simp [Figure2Paths.start, Figure2.start, rossLevelTCount, hk]

private theorem figure2_witness_level_one_direct {k : ℕ}
    (hvalid : Figure2.r2c1.ValidAtLevel k)
  :
    Figure2BranchPathWitness k Residue.r0001 Residue.r0001 := by
  refine ⟨Figure2Branch.direct, Figure2Paths.r2c1,
    Figure2SelectedCompletionPath.r2c1, ?_, ?_, ?_⟩
  · decide
  · simpa [Figure2Paths.r2c1, Figure2.r2c1] using hvalid
  · unfold rossLevelTCount
    change 2 * k - 2 ≤ if k = 0 then 0 else 2 * k - 2
    split <;> omega

private theorem figure2_witness_level_one_phase {k : ℕ}
    (hvalid : Figure2.r2c1.ValidAtLevel k)
  :
    Figure2BranchPathWitness k Residue.r0001 Residue.r1000 := by
  refine ⟨Figure2Branch.phaseT, Figure2Paths.r2c1,
    Figure2SelectedCompletionPath.r2c1, ?_, ?_, ?_⟩
  · decide
  · simpa [Figure2Paths.r2c1, Figure2.r2c1] using hvalid
  · unfold rossLevelTCount
    change 2 * k - 2 ≤ if k = 0 then 0 else 2 * k - 2
    split <;> omega

private theorem figure2_witness_pos_direct_0011_1100 {k : ℕ}
    (hvalid : Figure2.r4c4.ValidAtLevel k)
  :
    Figure2BranchPathWitness k Residue.r0011 Residue.r1100 := by
  refine ⟨Figure2Branch.direct, Figure2Paths.r4c4,
    Figure2SelectedCompletionPath.r4c4, ?_, ?_, ?_⟩
  · decide
  · simpa [Figure2Paths.r4c4, Figure2.r4c4] using hvalid
  · unfold rossLevelTCount
    change 2 * k - 2 ≤ if k = 0 then 0 else 2 * k - 2
    split <;> omega

private theorem figure2_witness_pos_direct_0011_1001 {k : ℕ}
    (hvalid : Figure2.r5c2.ValidAtLevel k)
  :
    Figure2BranchPathWitness k Residue.r0011 Residue.r1001 := by
  refine ⟨Figure2Branch.direct, Figure2Paths.r5c2,
    Figure2SelectedCompletionPath.r5c2, ?_, ?_, ?_⟩
  · decide
  · simpa [Figure2Paths.r5c2, Figure2.r5c2] using hvalid
  · unfold rossLevelTCount
    change 2 * k - 2 ≤ if k = 0 then 0 else 2 * k - 2
    split <;> omega

private theorem figure2_witness_pos_direct_1000_1101 {k : ℕ}
    (hvalid : Figure2.r7c2.ValidAtLevel k)
  :
    Figure2BranchPathWitness k Residue.r1000 Residue.r1101 := by
  refine ⟨Figure2Branch.direct, Figure2Paths.r7c2,
    Figure2SelectedCompletionPath.r7c2, ?_, ?_, ?_⟩
  · decide
  · simpa [Figure2Paths.r7c2, Figure2.r7c2] using hvalid
  · unfold rossLevelTCount
    change 2 * k - 2 ≤ if k = 0 then 0 else 2 * k - 2
    split <;> omega

private theorem figure2_witness_pos_phase_1000_1110 {k : ℕ}
    (hvalid : Figure2.r7c2.ValidAtLevel k)
  :
    Figure2BranchPathWitness k Residue.r1000 Residue.r1110 := by
  refine ⟨Figure2Branch.phaseT, Figure2Paths.r7c2,
    Figure2SelectedCompletionPath.r7c2, ?_, ?_, ?_⟩
  · decide
  · simpa [Figure2Paths.r7c2, Figure2.r7c2] using hvalid
  · unfold rossLevelTCount
    change 2 * k - 2 ≤ if k = 0 then 0 else 2 * k - 2
    split <;> omega

/-- Finite Figure 2 branch selection upgraded to an explicit selected-path
certificate carrying a concrete Clifford+T word and branch-local T-count bound.
-/
theorem figure2_completion_branch_with_selected_path
    {k : ℕ} {ru rt : Residue} {node : Figure2Node}
    (hnode : node ∈ Figure2.nodes)
    (hres :
      node.residue = Figure2Branch.completionResidue ru rt)
    (hvalid : node.ValidAtLevel k) :
    Figure2BranchPathWitness k ru rt := by
  have hmin : node.minTwoK ≤ 2 * k := hvalid.1
  have hstart : node.minTwoK = 0 → 2 * k = 0 := hvalid.2
  simp [Figure2.nodes, Figure2.start, Figure2.levelOneNodes,
    Figure2.positiveLevelNodes] at hnode
  rcases hnode with hnode | hnode | hnode | hnode | hnode | hnode |
    hnode | hnode | hnode | hnode | hnode | hnode | hnode | hnode |
    hnode | hnode | hnode | hnode | hnode | hnode | hnode | hnode |
    hnode
  all_goals
    subst node
    rcases ru with ⟨p₁, q₁, r₁, s₁⟩
    rcases rt with ⟨p₂, q₂, r₂, s₂⟩
    cases p₁ <;> cases q₁ <;> cases r₁ <;> cases s₁ <;>
      cases p₂ <;> cases q₂ <;> cases r₂ <;> cases s₂ <;>
        simp only [Figure2Branch.completionResidue,
          Figure2Branch.branchResidue, ResidueMatrix.ofRows,
          Residue.bullet, Residue.omegaMul, Residue.ofBits,
          Residue.r0000, Residue.r0001, Residue.r0010, Residue.r0011,
          Residue.r0100, Residue.r0101, Residue.r0110, Residue.r0111,
          Residue.r1000, Residue.r1001, Residue.r1010, Residue.r1011,
          Residue.r1100, Residue.r1101, Residue.r1110, Residue.r1111] at hres
    all_goals try contradiction
    all_goals first
      | exact figure2_witness_start (by simpa [Figure2.start] using hvalid)
          (hstart (by rfl))
      | exact figure2_witness_level_one_direct
          (by simpa [Figure2.r2c1] using hvalid)
      | exact figure2_witness_level_one_phase
          (by simpa [Figure2.r2c1] using hvalid)
      | exact figure2_witness_pos_direct_0011_1100
          (by simpa [Figure2.r4c4] using hvalid)
      | exact figure2_witness_pos_direct_0011_1001
          (by simpa [Figure2.r5c2] using hvalid)
      | exact figure2_witness_pos_direct_1000_1101
          (by simpa [Figure2.r7c2] using hvalid)
      | exact figure2_witness_pos_phase_1000_1110
          (by simpa [Figure2.r7c2] using hvalid)

/-- Selected-path synthesis consequence of the finite Figure 2 completion
branch theorem. This still packages only the branch/path-side synthesis and
T-count accounting; the remaining MA/U(2) evaluation bridge is separate. -/
theorem figure2_completion_branch_selected_node_synthesizes
    {k : ℕ} {ru rt : Residue} {node : Figure2Node}
    (hnode : node ∈ Figure2.nodes)
    (hres :
      node.residue = Figure2Branch.completionResidue ru rt)
    (hvalid : node.ValidAtLevel k) :
    ∃ (branch : Figure2Branch) (cert : Figure2PathCertificate)
      (C : CliffordTCircuit),
      Figure2SelectedCompletionPath cert ∧
        cert.target.residue = Figure2Branch.branchResidue branch ru rt ∧
          C = cert.word ∧
            TCount C ≤ rossLevelTCount k := by
  rcases figure2_completion_branch_with_selected_path hnode hres hvalid with
    ⟨branch, cert, hselected, htarget, htargetValid, hbranchBound⟩
  rcases figure2_selected_node_synthesizes hselected htargetValid with
    ⟨C, hC, _hCountEq, hCountNode⟩
  refine ⟨branch, cert, C, hselected, htarget, hC, ?_⟩
  exact hCountNode.trans hbranchBound

end Selinger75

end RossSelinger

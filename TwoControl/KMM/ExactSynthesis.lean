import TwoControl.KMM.Denominator
import MatrixCompletion.Completion
import TwoControl.RossSelinger.Basic
import Mathlib.NumberTheory.Real.Irrational

namespace TwoControl.KMM

open DyadicCyclotomic MatrixCompletion
open TwoControl.Clifford
open TwoControl.RossSelinger

/-!
Kliuchnikov-Maslov-Mosca exact synthesis.

The oracle proof only needs the non-optimal consequence: every `2 × 2` unitary
whose entries lie in `D[ω]` has an exact Clifford+T implementation.  The proof
path below mirrors the KMM paper:

1. reduce unitary implementation to state preparation;
2. use denominator-change lemmas for `HT^k`;
3. discharge the `sde ≤ 3` base case by a finite certificate/table;
4. run the decomposition algorithm.
-/

/-- A vector/state over the KMM ring. -/
def StateEntriesInDyadicCyclotomic (z w : ℂ) : Prop :=
  InDyadicCyclotomic z ∧ InDyadicCyclotomic w

/-- A normalized one-qubit state. -/
def IsUnitState (z w : ℂ) : Prop :=
  star z * z + star w * w = 1

/-- Column vector for `|0⟩`. -/
noncomputable def ket0Column : Matrix (Fin 2) (Fin 1) ℂ :=
  Matrix.of ![![(1 : ℂ)], ![(0 : ℂ)]]

/-- Column vector for the state `z|0⟩ + w|1⟩`. -/
noncomputable def stateColumn (z w : ℂ) : Matrix (Fin 2) (Fin 1) ℂ :=
  Matrix.of ![![z], ![w]]

private lemma rsOmegaAlg_unit :
    star rsOmegaAlg * rsOmegaAlg = 1 := by
  have hs : star sqrtTwoComplex = sqrtTwoComplex := by simp [sqrtTwoComplex]
  simp [rsOmegaAlg, hs]
  field_simp [sqrtTwoComplex_ne_zero]
  ring_nf
  simp [sqrtTwoComplex_sq, Complex.I_sq]
  norm_num

private lemma rsOmegaAlg_pow_unit (n : ℕ) :
    star (rsOmegaAlg ^ n) * (rsOmegaAlg ^ n) = 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        star (rsOmegaAlg ^ (n + 1)) * (rsOmegaAlg ^ (n + 1))
            = (star rsOmegaAlg * rsOmegaAlg) *
                (star (rsOmegaAlg ^ n) * (rsOmegaAlg ^ n)) := by
                rw [pow_succ]
                simp [star_mul]
                ring
        _ = 1 := by rw [rsOmegaAlg_unit, ih]; norm_num

private lemma applyHTPowToState_unit_of_tau_unit
    {τ z w : ℂ}
    (hτ : star τ * τ = 1)
    (hState : IsUnitState z w) :
    IsUnitState ((z + τ * w) / sqrtTwoComplex)
      ((z - τ * w) / sqrtTwoComplex) := by
  unfold IsUnitState at *
  have hsstar : star sqrtTwoComplex = sqrtTwoComplex := by simp [sqrtTwoComplex]
  simp [star_add, star_sub, star_mul, hsstar]
  field_simp [sqrtTwoComplex_ne_zero]
  ring_nf
  calc
    star z * z * 2 + star w * star τ * τ * w * 2
        = (star z * z + star w * w) * 2 := by
            rw [show star w * star τ * τ * w * 2 = star w * w * 2 by
              calc
                star w * star τ * τ * w * 2
                    = (star τ * τ) * (star w * w) * 2 := by ring
                _ = star w * w * 2 := by rw [hτ]; ring]
            ring
    _ = sqrtTwoComplex ^ 2 := by
          rw [hState, sqrtTwoComplex_sq]
          norm_num

/-- State-level action of `H T^k`: first apply `T^k = diag(1, ω^k)`, then
Hadamard.  This matches the circuit convention where matrices multiply column
states from the left and list heads are leftmost matrices. -/
noncomputable def applyHTPowToState (k : Fin 4) (z w : ℂ) : ℂ × ℂ :=
  let τ := rsOmegaAlg ^ (k : ℕ)
  (((z + τ * w) / sqrtTwoComplex),
   ((z - τ * w) / sqrtTwoComplex))

theorem applyHTPowToState_entries
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (k : Fin 4) :
    let z' := (applyHTPowToState k z w).1
    let w' := (applyHTPowToState k z w).2
    StateEntriesInDyadicCyclotomic z' w' := by
  rcases hEntries with ⟨hz, hw⟩
  let τ := rsOmegaAlg ^ (k : ℕ)
  have hτ : InDyadicCyclotomic τ := rsOmegaAlg_pow_in_dyadic (k : ℕ)
  have hτw : InDyadicCyclotomic (τ * w) := InDyadicCyclotomic.mul hτ hw
  have hplus : InDyadicCyclotomic ((z + τ * w) / sqrtTwoComplex) :=
    InDyadicCyclotomic.div_sqrtTwo (InDyadicCyclotomic.add hz hτw)
  have hminus : InDyadicCyclotomic ((z - τ * w) / sqrtTwoComplex) :=
    InDyadicCyclotomic.div_sqrtTwo
      (InDyadicCyclotomic.add hz (InDyadicCyclotomic.neg hτw))
  simpa [applyHTPowToState, τ, sub_eq_add_neg] using And.intro hplus hminus

/-- The elementary norm identity behind the `H T^k` state update. -/
theorem applyHTPowToState_unit_identity
    {z w : ℂ}
    (hState : IsUnitState z w)
    (k : Fin 4) :
    let z' := (applyHTPowToState k z w).1
    let w' := (applyHTPowToState k z w).2
    IsUnitState z' w' := by
  simpa [applyHTPowToState] using
    applyHTPowToState_unit_of_tau_unit
      (τ := rsOmegaAlg ^ (k : ℕ)) (z := z) (w := w)
      (rsOmegaAlg_pow_unit (k : ℕ)) hState

theorem applyHTPowToState_unit
    {z w : ℂ}
    (hState : IsUnitState z w)
    (k : Fin 4) :
    let z' := (applyHTPowToState k z w).1
    let w' := (applyHTPowToState k z w).2
    IsUnitState z' w' :=
  applyHTPowToState_unit_identity hState k

/-- Numerator coordinate in `ℤ[ω] = ℤ[√2, i]`, before applying a dyadic
denominator. -/
noncomputable def cyclotomicIntegerCoord (a b c d : ℤ) : ℂ :=
  ((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
    ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I

/-- At denominator level `k`, the numerator of `x` is divisible by `√2` in
the coordinate ring.  The definition deliberately stores both the level-`k`
presentation and a quotient numerator, so denominator lowering can be proved
without relying on uniqueness of coordinates. -/
def NumeratorAtLevelDivisibleBySqrtTwo (x : ℂ) (k : ℕ) : Prop :=
  ∃ a b c d A B C D : ℤ,
    x = cyclotomicIntegerCoord a b c d / sqrtTwoComplex ^ k ∧
    cyclotomicIntegerCoord a b c d =
      sqrtTwoComplex * cyclotomicIntegerCoord A B C D

private theorem numeratorAtLevelDivisibleBySqrtTwo_of_even_realCoord
    {x : ℂ} {k : ℕ} {P Q : ℤ}
    (hEven : Even P)
    (hx : x = cyclotomicIntegerCoord P Q 0 0 / sqrtTwoComplex ^ k) :
    NumeratorAtLevelDivisibleBySqrtTwo x k := by
  rcases hEven with ⟨R, hR⟩
  refine ⟨P, Q, 0, 0, Q, R, 0, 0, hx, ?_⟩
  rw [hR]
  simp [cyclotomicIntegerCoord]
  ring_nf
  simp [sqrtTwoComplex_sq]

/-- Convert a selected finite KMM residue result for a real norm numerator
`P + √2 Q` into the concrete denominator-lowering witness used by the legacy
complex API. -/
private theorem numeratorAtLevelDivisibleBySqrtTwo_of_selected_residue
    {x : ℂ} {k n : ℕ} {P Q : ℤ}
    (hn : 1 ≤ n) (hn4 : n ≤ 4)
    (hres :
      OmegaResidue.sqrtTwoGDEEqPair n (P : ZMod 8) (Q : ZMod 8) = true)
    (hx : x = cyclotomicIntegerCoord P Q 0 0 / sqrtTwoComplex ^ k) :
    NumeratorAtLevelDivisibleBySqrtTwo x k := by
  exact numeratorAtLevelDivisibleBySqrtTwo_of_even_realCoord
    (OmegaResidue.even_left_of_sqrtTwoGDEEqPair_pos hn hn4 hres) hx

private theorem hasDenominatorExponent_of_real_norm_div_sqrtTwo_three
    {x : ℂ} {k : ℕ} {P Q : ℤ}
    (hk : 3 ≤ k)
    (hP : (4 : ℤ) ∣ P)
    (hQ : Even Q)
    (hx : x = cyclotomicIntegerCoord P Q 0 0 / sqrtTwoComplex ^ k) :
    HasDenominatorExponent x (k - 3) := by
  rcases hP with ⟨A, hA⟩
  rcases hQ with ⟨B, hB⟩
  subst P
  subst Q
  refine ⟨B, A, 0, 0, ?_⟩
  have hpow : sqrtTwoComplex ^ k =
      sqrtTwoComplex ^ 3 * sqrtTwoComplex ^ (k - 3) := by
    calc
      sqrtTwoComplex ^ k = sqrtTwoComplex ^ (3 + (k - 3)) := by
        rw [show 3 + (k - 3) = k by omega]
      _ = sqrtTwoComplex ^ 3 * sqrtTwoComplex ^ (k - 3) := by
        rw [pow_add]
  rw [hx, hpow]
  field_simp [pow_ne_zero 3 sqrtTwoComplex_ne_zero,
    pow_ne_zero (k - 3) sqrtTwoComplex_ne_zero]
  simp [cyclotomicIntegerCoord, sqrtTwoComplex_sq]
  field_simp [sqrtTwoComplex_ne_zero]
  rw [show sqrtTwoComplex ^ 3 = (2 : ℂ) * sqrtTwoComplex by
      rw [show sqrtTwoComplex ^ 3 = sqrtTwoComplex ^ 2 * sqrtTwoComplex by ring]
      rw [sqrtTwoComplex_sq]]
  rw [show (2 : ℂ) * sqrtTwoComplex * ((B : ℂ) + (A : ℂ) * sqrtTwoComplex) =
      2 * (B : ℂ) * sqrtTwoComplex + 2 * (A : ℂ) * sqrtTwoComplex ^ 2 by ring]
  rw [sqrtTwoComplex_sq]
  ring

private theorem hasDenominatorExponent_of_real_norm_div_sqrtTwo_four
    {x : ℂ} {k : ℕ} {P Q : ℤ}
    (hk : 4 ≤ k)
    (hP : (4 : ℤ) ∣ P)
    (hQ : (4 : ℤ) ∣ Q)
    (hx : x = cyclotomicIntegerCoord P Q 0 0 / sqrtTwoComplex ^ k) :
    HasDenominatorExponent x (k - 4) := by
  rcases hP with ⟨A, hA⟩
  rcases hQ with ⟨B, hB⟩
  subst P
  subst Q
  refine ⟨A, B, 0, 0, ?_⟩
  have hpow : sqrtTwoComplex ^ k =
      sqrtTwoComplex ^ 4 * sqrtTwoComplex ^ (k - 4) := by
    calc
      sqrtTwoComplex ^ k = sqrtTwoComplex ^ (4 + (k - 4)) := by
        rw [show 4 + (k - 4) = k by omega]
      _ = sqrtTwoComplex ^ 4 * sqrtTwoComplex ^ (k - 4) := by
        rw [pow_add]
  have hs4 : sqrtTwoComplex ^ 4 = (4 : ℂ) := by
    rw [show sqrtTwoComplex ^ 4 = (sqrtTwoComplex ^ 2) ^ 2 by ring]
    rw [sqrtTwoComplex_sq]
    norm_num
  rw [hx, hpow, hs4]
  field_simp [pow_ne_zero (k - 4) sqrtTwoComplex_ne_zero]
  simp [cyclotomicIntegerCoord]
  ring

private theorem hasDenominatorExponent_of_selected_residue_ge_three
    {x : ℂ} {k n : ℕ} {P Q : ℤ}
    (hn : 3 ≤ n) (hn4 : n ≤ 4) (hk : n ≤ k)
    (hres :
      OmegaResidue.sqrtTwoGDEEqPair n (P : ZMod 8) (Q : ZMod 8) = true)
    (hx : x = cyclotomicIntegerCoord P Q 0 0 / sqrtTwoComplex ^ k) :
    HasDenominatorExponent x (k - n) := by
  interval_cases n
  · exact hasDenominatorExponent_of_real_norm_div_sqrtTwo_three
      hk
      (OmegaResidue.four_dvd_left_of_sqrtTwoGDEEqPair_ge_three
        (by omega) (by omega) hres)
      (OmegaResidue.even_right_of_sqrtTwoGDEEqPair_ge_three
        (by omega) (by omega) hres)
      hx
  · exact hasDenominatorExponent_of_real_norm_div_sqrtTwo_four
      hk
      (OmegaResidue.four_dvd_left_of_sqrtTwoGDEEqPair_ge_three
        (by omega) (by omega) hres)
      (OmegaResidue.four_dvd_right_of_sqrtTwoGDEEqPair_four hres)
      hx

private theorem omega_norm_coord_as_legacy (x : OmegaIntCoord) :
    star (OmegaIntCoord.val x) * OmegaIntCoord.val x =
      cyclotomicIntegerCoord (OmegaIntCoord.P x) (OmegaIntCoord.Q x) 0 0 := by
  rw [OmegaIntCoord.norm_val]
  simp [cyclotomicIntegerCoord]

private theorem numeratorAtLevelDivisibleBySqrtTwo_of_selected_omega_residue
    {candidate : ℂ} {level n : ℕ}
    (hn : 1 ≤ n) (hn4 : n ≤ 4)
    (k : Fin 4) (x y : OmegaIntCoord)
    (hres :
      let t := OmegaResidue.transformed (k : ℕ)
        (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y)
      OmegaResidue.sqrtTwoGDEEqPair n
        (OmegaResidue.P t) (OmegaResidue.Q t) = true)
    (hcandidate :
      candidate =
        star (OmegaIntCoord.val
          (OmegaIntCoord.add x (OmegaIntCoord.omegaPowMul (k : ℕ) y))) *
          OmegaIntCoord.val
            (OmegaIntCoord.add x (OmegaIntCoord.omegaPowMul (k : ℕ) y)) /
          sqrtTwoComplex ^ level) :
    NumeratorAtLevelDivisibleBySqrtTwo candidate level := by
  let tInt := OmegaIntCoord.add x (OmegaIntCoord.omegaPowMul (k : ℕ) y)
  have hresInt :
      OmegaResidue.sqrtTwoGDEEqPair n
        ((OmegaIntCoord.P tInt : ℤ) : ZMod 8)
        ((OmegaIntCoord.Q tInt : ℤ) : ZMod 8) = true := by
    rw [show OmegaResidue.transformed (k : ℕ)
        (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y) =
          OmegaResidue.ofIntCoord tInt by
            dsimp [tInt]
            exact (OmegaResidue.ofIntCoord_transformed (k : ℕ) x y).symm]
      at hres
    simpa [OmegaResidue.P_ofIntCoord, OmegaResidue.Q_ofIntCoord] using hres
  refine numeratorAtLevelDivisibleBySqrtTwo_of_selected_residue
    (x := candidate) (k := level) (n := n)
    (P := OmegaIntCoord.P tInt) (Q := OmegaIntCoord.Q tInt)
    hn hn4 hresInt ?_
  rw [hcandidate, omega_norm_coord_as_legacy]

theorem hasDenominatorExponent_of_numeratorAtLevelDivisibleBySqrtTwo
    {x : ℂ} {k : ℕ}
    (hdiv : NumeratorAtLevelDivisibleBySqrtTwo x k) :
    HasDenominatorExponent x k := by
  rcases hdiv with ⟨a, b, c, d, A, B, C, D, hx, hnum⟩
  exact ⟨a, b, c, d, by simpa [cyclotomicIntegerCoord] using hx⟩

/-- Lower a dyadic denominator by one when the numerator at that level is
divisible by `√2`. -/
theorem hasDenominatorExponent_lower_of_sqrtTwo_dvd
    {x : ℂ} {k : ℕ}
    (_hk : HasDenominatorExponent x k)
    (hdiv : NumeratorAtLevelDivisibleBySqrtTwo x k)
    (hpos : 0 < k) :
    HasDenominatorExponent x (k - 1) := by
  rcases hdiv with ⟨a, b, c, d, A, B, C, D, hx, hnum⟩
  refine ⟨A, B, C, D, ?_⟩
  have hkpow : sqrtTwoComplex ^ k =
      sqrtTwoComplex * sqrtTwoComplex ^ (k - 1) := by
    calc
      sqrtTwoComplex ^ k = sqrtTwoComplex ^ ((k - 1) + 1) := by
        congr 1
        omega
      _ = sqrtTwoComplex * sqrtTwoComplex ^ (k - 1) := by
        rw [pow_succ]
        ring
  rw [hx, hnum, hkpow]
  field_simp [sqrtTwoComplex_ne_zero, pow_ne_zero (k - 1) sqrtTwoComplex_ne_zero]
  simp [cyclotomicIntegerCoord]
  ring

private theorem applyHTPowToState_norm_formula
    (k : Fin 4) (z w : ℂ) :
    star ((applyHTPowToState k z w).1) *
        ((applyHTPowToState k z w).1)
      =
        (star z * z +
            star z * (rsOmegaAlg ^ (k : ℕ) * w) +
            star (rsOmegaAlg ^ (k : ℕ) * w) * z +
            star (rsOmegaAlg ^ (k : ℕ) * w) *
              (rsOmegaAlg ^ (k : ℕ) * w)) / 2 := by
  have hsstar : star sqrtTwoComplex = sqrtTwoComplex := by simp [sqrtTwoComplex]
  simp [applyHTPowToState, star_add, star_mul, hsstar]
  field_simp [sqrtTwoComplex_ne_zero]
  rw [sqrtTwoComplex_sq]
  ring

theorem applyHTPowToState_norm_formula_k0 (z w : ℂ) :
    star ((applyHTPowToState (0 : Fin 4) z w).1) *
        ((applyHTPowToState (0 : Fin 4) z w).1)
      =
        (star z * z + star z * w + star w * z + star w * w) / 2 := by
  simpa using applyHTPowToState_norm_formula (0 : Fin 4) z w

theorem applyHTPowToState_norm_formula_k1 (z w : ℂ) :
    star ((applyHTPowToState (1 : Fin 4) z w).1) *
        ((applyHTPowToState (1 : Fin 4) z w).1)
      =
        (star z * z +
            star z * (rsOmegaAlg * w) +
            star (rsOmegaAlg * w) * z +
            star (rsOmegaAlg * w) * (rsOmegaAlg * w)) / 2 := by
  simpa using applyHTPowToState_norm_formula (1 : Fin 4) z w

theorem applyHTPowToState_norm_formula_k2 (z w : ℂ) :
    star ((applyHTPowToState (2 : Fin 4) z w).1) *
        ((applyHTPowToState (2 : Fin 4) z w).1)
      =
        (star z * z +
            star z * (rsOmegaAlg ^ (2 : ℕ) * w) +
            star (rsOmegaAlg ^ (2 : ℕ) * w) * z +
            star (rsOmegaAlg ^ (2 : ℕ) * w) *
              (rsOmegaAlg ^ (2 : ℕ) * w)) / 2 := by
  simpa using applyHTPowToState_norm_formula (2 : Fin 4) z w

theorem applyHTPowToState_norm_formula_k3 (z w : ℂ) :
    star ((applyHTPowToState (3 : Fin 4) z w).1) *
        ((applyHTPowToState (3 : Fin 4) z w).1)
      =
        (star z * z +
            star z * (rsOmegaAlg ^ (3 : ℕ) * w) +
            star (rsOmegaAlg ^ (3 : ℕ) * w) * z +
            star (rsOmegaAlg ^ (3 : ℕ) * w) *
              (rsOmegaAlg ^ (3 : ℕ) * w)) / 2 := by
  simpa using applyHTPowToState_norm_formula (3 : Fin 4) z w

private theorem kmm_choice_k0_of_norm_candidate
    {z w : ℂ}
    (h :
      NumeratorAtLevelDivisibleBySqrtTwo
        ((star z * z + star z * w + star w * z + star w * w) / 2)
        (DenNormSDE z)) :
    NumeratorAtLevelDivisibleBySqrtTwo
      (star ((applyHTPowToState (0 : Fin 4) z w).1) *
        ((applyHTPowToState (0 : Fin 4) z w).1))
      (DenNormSDE z) := by
  rw [applyHTPowToState_norm_formula_k0]
  exact h

private theorem kmm_choice_k1_of_norm_candidate
    {z w : ℂ}
    (h :
      NumeratorAtLevelDivisibleBySqrtTwo
        ((star z * z +
            star z * (rsOmegaAlg * w) +
            star (rsOmegaAlg * w) * z +
            star (rsOmegaAlg * w) * (rsOmegaAlg * w)) / 2)
        (DenNormSDE z)) :
    NumeratorAtLevelDivisibleBySqrtTwo
      (star ((applyHTPowToState (1 : Fin 4) z w).1) *
        ((applyHTPowToState (1 : Fin 4) z w).1))
      (DenNormSDE z) := by
  rw [applyHTPowToState_norm_formula_k1]
  exact h

private theorem kmm_choice_k2_of_norm_candidate
    {z w : ℂ}
    (h :
      NumeratorAtLevelDivisibleBySqrtTwo
        ((star z * z +
            star z * (rsOmegaAlg ^ (2 : ℕ) * w) +
            star (rsOmegaAlg ^ (2 : ℕ) * w) * z +
            star (rsOmegaAlg ^ (2 : ℕ) * w) *
              (rsOmegaAlg ^ (2 : ℕ) * w)) / 2)
        (DenNormSDE z)) :
    NumeratorAtLevelDivisibleBySqrtTwo
      (star ((applyHTPowToState (2 : Fin 4) z w).1) *
        ((applyHTPowToState (2 : Fin 4) z w).1))
      (DenNormSDE z) := by
  rw [applyHTPowToState_norm_formula_k2]
  exact h

private theorem kmm_choice_k3_of_norm_candidate
    {z w : ℂ}
    (h :
      NumeratorAtLevelDivisibleBySqrtTwo
        ((star z * z +
            star z * (rsOmegaAlg ^ (3 : ℕ) * w) +
            star (rsOmegaAlg ^ (3 : ℕ) * w) * z +
            star (rsOmegaAlg ^ (3 : ℕ) * w) *
              (rsOmegaAlg ^ (3 : ℕ) * w)) / 2)
        (DenNormSDE z)) :
    NumeratorAtLevelDivisibleBySqrtTwo
      (star ((applyHTPowToState (3 : Fin 4) z w).1) *
        ((applyHTPowToState (3 : Fin 4) z w).1))
      (DenNormSDE z) := by
  rw [applyHTPowToState_norm_formula_k3]
  exact h

/-- Finite KMM parity choice in the paper's omega-coordinate API.

This is the bridge from integer omega-basis denominator numerators to the
kernel-checked finite residue table in `OmegaArithmetic`.  The remaining
complex-coordinate lift below is separate: it has to connect the project's
legacy `a + b√2 + (c+d√2)i` denominator presentations to these KMM numerator
conditions. -/
private theorem kmm_four_choice_parity
    {j d : Nat}
    (hj : j = 0 ∨ j = 1)
    {x y : OmegaIntCoord}
    (hcompat :
      OmegaResidue.compatiblePair j
        (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y) = true)
    (hd : d ∈ ([1, 2, 3] : List Nat)) :
    ∃ k : Fin 4,
      let t := OmegaResidue.transformed (k : ℕ)
        (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y)
      OmegaResidue.sqrtTwoGDEEqPair (d + j)
        (OmegaResidue.P t) (OmegaResidue.Q t) = true :=
  OmegaResidue.intCoord_choice_for_d hj hcompat hd

private theorem norm_candidate_eq_common_omega_numerator
    {z w : ℂ} {r : ℕ} (k : Fin 4) (x y : OmegaIntCoord)
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hw : w = OmegaIntCoord.val y / sqrtTwoComplex ^ r) :
    ((star z * z +
          star z * (rsOmegaAlg ^ (k : ℕ) * w) +
          star (rsOmegaAlg ^ (k : ℕ) * w) * z +
          star (rsOmegaAlg ^ (k : ℕ) * w) *
            (rsOmegaAlg ^ (k : ℕ) * w)) / 2)
      =
        star (OmegaIntCoord.val
          (OmegaIntCoord.add x (OmegaIntCoord.omegaPowMul (k : ℕ) y))) *
          OmegaIntCoord.val
            (OmegaIntCoord.add x (OmegaIntCoord.omegaPowMul (k : ℕ) y)) /
          sqrtTwoComplex ^ (2 * r + 2) := by
  have hs : sqrtTwoComplex ≠ 0 := sqrtTwoComplex_ne_zero
  have hsstar : star (sqrtTwoComplex ^ r) = sqrtTwoComplex ^ r := by
    simp [sqrtTwoComplex]
  have hpow : sqrtTwoComplex ^ (2 * r + 2) =
      2 * (sqrtTwoComplex ^ r * sqrtTwoComplex ^ r) := by
    rw [show 2 * r + 2 = r + r + 2 by omega]
    rw [pow_add, pow_add, sqrtTwoComplex_sq]
    ring
  let A := OmegaIntCoord.val
    (OmegaIntCoord.add x (OmegaIntCoord.omegaPowMul (k : ℕ) y))
  have hsum :
      z + rsOmegaAlg ^ (k : ℕ) * w = A / sqrtTwoComplex ^ r := by
    dsimp [A]
    rw [hz, hw, OmegaIntCoord.val_add, OmegaIntCoord.val_omegaPowMul]
    ring
  have hcandidate :
      (star z * z +
          star z * (rsOmegaAlg ^ (k : ℕ) * w) +
          star (rsOmegaAlg ^ (k : ℕ) * w) * z +
          star (rsOmegaAlg ^ (k : ℕ) * w) *
            (rsOmegaAlg ^ (k : ℕ) * w)) / 2 =
        star (z + rsOmegaAlg ^ (k : ℕ) * w) *
          (z + rsOmegaAlg ^ (k : ℕ) * w) / 2 := by
    simp [star_add]
    ring
  rw [hcandidate, hsum]
  dsimp [A]
  rw [hpow]
  simp [star_div, hsstar]
  field_simp [hs, pow_ne_zero r hs]
  have hsstar' : (starRingEnd ℂ) sqrtTwoComplex ^ r = sqrtTwoComplex ^ r := by
    simpa using hsstar
  rw [hsstar']
  ring

private theorem numeratorAtLevelDivisibleBySqrtTwo_of_common_omega_choice
    {z w : ℂ} {r level n : ℕ}
    (hn : 1 ≤ n) (hn4 : n ≤ 4)
    (k : Fin 4) (x y : OmegaIntCoord)
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hw : w = OmegaIntCoord.val y / sqrtTwoComplex ^ r)
    (hlevel : level = 2 * r + 2)
    (hres :
      let t := OmegaResidue.transformed (k : ℕ)
        (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y)
      OmegaResidue.sqrtTwoGDEEqPair n
        (OmegaResidue.P t) (OmegaResidue.Q t) = true) :
    NumeratorAtLevelDivisibleBySqrtTwo
      ((star z * z +
          star z * (rsOmegaAlg ^ (k : ℕ) * w) +
          star (rsOmegaAlg ^ (k : ℕ) * w) * z +
          star (rsOmegaAlg ^ (k : ℕ) * w) *
            (rsOmegaAlg ^ (k : ℕ) * w)) / 2)
      level := by
  subst level
  exact numeratorAtLevelDivisibleBySqrtTwo_of_selected_omega_residue
    hn hn4 k x y hres
    (norm_candidate_eq_common_omega_numerator k x y hz hw)

private theorem hasDenominatorExponent_of_common_omega_choice_ge_three
    {z w : ℂ} {r target n : ℕ}
    (hn : 3 ≤ n) (hn4 : n ≤ 4)
    (hnlevel : n ≤ 2 * r + 2)
    (k : Fin 4) (x y : OmegaIntCoord)
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hw : w = OmegaIntCoord.val y / sqrtTwoComplex ^ r)
    (htarget : target = 2 * r + 2 - n)
    (hres :
      let t := OmegaResidue.transformed (k : ℕ)
        (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y)
      OmegaResidue.sqrtTwoGDEEqPair n
        (OmegaResidue.P t) (OmegaResidue.Q t) = true) :
    HasDenominatorExponent
      ((star z * z +
          star z * (rsOmegaAlg ^ (k : ℕ) * w) +
          star (rsOmegaAlg ^ (k : ℕ) * w) * z +
          star (rsOmegaAlg ^ (k : ℕ) * w) *
            (rsOmegaAlg ^ (k : ℕ) * w)) / 2)
      target := by
  subst target
  let tInt := OmegaIntCoord.add x (OmegaIntCoord.omegaPowMul (k : ℕ) y)
  have hresInt :
      OmegaResidue.sqrtTwoGDEEqPair n
        ((OmegaIntCoord.P tInt : ℤ) : ZMod 8)
        ((OmegaIntCoord.Q tInt : ℤ) : ZMod 8) = true := by
    rw [show OmegaResidue.transformed (k : ℕ)
        (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y) =
          OmegaResidue.ofIntCoord tInt by
            dsimp [tInt]
            exact (OmegaResidue.ofIntCoord_transformed (k : ℕ) x y).symm]
      at hres
    simpa [OmegaResidue.P_ofIntCoord, OmegaResidue.Q_ofIntCoord] using hres
  refine hasDenominatorExponent_of_selected_residue_ge_three
    (x := ((star z * z +
          star z * (rsOmegaAlg ^ (k : ℕ) * w) +
          star (rsOmegaAlg ^ (k : ℕ) * w) * z +
          star (rsOmegaAlg ^ (k : ℕ) * w) *
            (rsOmegaAlg ^ (k : ℕ) * w)) / 2))
    (k := 2 * r + 2) (n := n)
    (P := OmegaIntCoord.P tInt) (Q := OmegaIntCoord.Q tInt)
    hn hn4 hnlevel hresInt ?_
  rw [norm_candidate_eq_common_omega_numerator k x y hz hw, omega_norm_coord_as_legacy]

private theorem common_omega_presentations_of_legacy_coordinates
    {z w : ℂ}
    {nz nw : ℕ}
    {a b c d e f g h : ℤ}
    (hz : z = cyclotomicIntegerCoord a b c d / sqrtTwoComplex ^ nz)
    (hw : w = cyclotomicIntegerCoord e f g h / sqrtTwoComplex ^ nw) :
    ∃ x y : OmegaIntCoord,
      z = OmegaIntCoord.val x / sqrtTwoComplex ^ (max nz nw) ∧
      w = OmegaIntCoord.val y / sqrtTwoComplex ^ (max nz nw) := by
  have hzO : HasOmegaDenominatorExponent z nz := by
    refine ⟨omegaCoordOfLegacy a b c d, ?_⟩
    simpa [omegaCoordOfLegacy_val, cyclotomicIntegerCoord] using hz
  have hwO : HasOmegaDenominatorExponent w nw := by
    refine ⟨omegaCoordOfLegacy e f g h, ?_⟩
    simpa [omegaCoordOfLegacy_val, cyclotomicIntegerCoord] using hw
  rcases hasOmegaDenominatorExponent_mono hzO (Nat.le_max_left nz nw) with ⟨x, hx⟩
  rcases hasOmegaDenominatorExponent_mono hwO (Nat.le_max_right nz nw) with ⟨y, hy⟩
  exact ⟨x, y, hx, hy⟩

private theorem omegaSDE_presentation_of_legacy_coordinate
    {z : ℂ} {n : ℕ} {a b c d : ℤ}
    (hz : z = cyclotomicIntegerCoord a b c d / sqrtTwoComplex ^ n) :
    ∃ x : OmegaIntCoord,
      z = OmegaIntCoord.val x / sqrtTwoComplex ^ omegaSDE z := by
  have hzD : HasDenominatorExponent z n := by
    exact ⟨a, b, c, d, by simpa [cyclotomicIntegerCoord] using hz⟩
  have hzO : InOmegaDyadicCyclotomic z :=
    ⟨n, hasOmegaDenominatorExponent_of_hasDenominatorExponent hzD⟩
  exact hasOmegaDenominatorExponent_of_inOmegaDyadicCyclotomic hzO

private theorem not_norm_gde_ge_two_of_minimal_omega
    {z : ℂ} {r : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hr : omegaSDE z = r)
    (hpos : 0 < r) :
    OmegaResidue.sqrtTwoGDEGePair 2
      (OmegaResidue.P (OmegaResidue.ofIntCoord x))
      (OmegaResidue.Q (OmegaResidue.ofIntCoord x)) ≠ true := by
  intro hge
  have hg0 := sqrtTwoGDE_zero_of_minimal_omega_denominator_pos hz hr hpos
  have hnot := OmegaIntCoord.sqrtTwoGDE_zero_not_sqrtTwo_dvd hg0
  have hgePair : SqrtTwoNormPairGDEGe 2 (OmegaIntCoord.P x) (OmegaIntCoord.Q x) := by
    simpa [SqrtTwoNormPairGDEGe, OmegaResidue.P_ofIntCoord,
      OmegaResidue.Q_ofIntCoord] using hge
  exact hnot (norm_pair_gde_ge_two_sqrtTwo_dvd x hgePair)

private theorem exists_normGDEEq_zero_or_one_of_minimal_omega
    {z : ℂ} {r : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hr : omegaSDE z = r)
    (hpos : 0 < r) :
    ∃ j : ℕ,
      (j = 0 ∨ j = 1) ∧
        OmegaResidue.normGDEEq j (OmegaResidue.ofIntCoord x) = true := by
  have hnge2 := not_norm_gde_ge_two_of_minimal_omega hz hr hpos
  by_cases hge1 :
      OmegaResidue.sqrtTwoGDEGePair 1
        (OmegaResidue.P (OmegaResidue.ofIntCoord x))
        (OmegaResidue.Q (OmegaResidue.ofIntCoord x)) = true
  · refine ⟨1, Or.inr rfl, ?_⟩
    simp [OmegaResidue.normGDEEq, OmegaResidue.sqrtTwoGDEEqPair, hge1, hnge2]
  · refine ⟨0, Or.inl rfl, ?_⟩
    have hge1false :
        OmegaResidue.sqrtTwoGDEGePair 1
          (OmegaResidue.P (OmegaResidue.ofIntCoord x))
          (OmegaResidue.Q (OmegaResidue.ofIntCoord x)) = false := by
      cases h :
          OmegaResidue.sqrtTwoGDEGePair 1
            (OmegaResidue.P (OmegaResidue.ofIntCoord x))
            (OmegaResidue.Q (OmegaResidue.ofIntCoord x)) <;>
        simp [h] at hge1 ⊢
    have hge0 :
        OmegaResidue.sqrtTwoGDEGePair 0
          (OmegaResidue.P (OmegaResidue.ofIntCoord x))
          (OmegaResidue.Q (OmegaResidue.ofIntCoord x)) = true := rfl
    rw [OmegaResidue.normGDEEq, OmegaResidue.sqrtTwoGDEEqPair]
    simp [hge0, hge1false]

private theorem minimal_omega_denominator_pos_of_large_norm_sde
    {z : ℂ} {r : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hLarge : 4 ≤ DenNormSDE z) :
    0 < r := by
  by_contra hnot
  have hr0 : r = 0 := by omega
  subst r
  have hnorm :
      star z * z =
        cyclotomicIntegerCoord (OmegaIntCoord.P x) (OmegaIntCoord.Q x) 0 0 /
          sqrtTwoComplex ^ 0 := by
    rw [hz]
    simpa using omega_norm_coord_as_legacy x
  have hden :
      HasDenominatorExponent (star z * z) 0 :=
    ⟨OmegaIntCoord.P x, OmegaIntCoord.Q x, 0, 0,
      by simpa [cyclotomicIntegerCoord] using hnorm⟩
  have hsde := sde_le_of_hasDenominatorExponent hden
  unfold DenNormSDE at hLarge
  omega

private theorem int_add_int_mul_sqrtTwo_eq_int_early
    {A B R : ℤ}
    (h : ((A : ℂ) + (B : ℂ) * sqrtTwoComplex) = (R : ℂ)) :
    B = 0 ∧ A = R := by
  have hre : (A : ℝ) + (B : ℝ) * Real.sqrt 2 = (R : ℝ) := by
    have h' := congrArg Complex.re h
    simpa [sqrtTwoComplex] using h'
  have hB : B = 0 := by
    by_contra hB
    have hlin : (B : ℝ) * Real.sqrt 2 = ((R - A : ℤ) : ℝ) := by
      calc
        (B : ℝ) * Real.sqrt 2 =
            ((A : ℝ) + (B : ℝ) * Real.sqrt 2) - (A : ℝ) := by ring
        _ = (R : ℝ) - (A : ℝ) := by rw [hre]
        _ = ((R - A : ℤ) : ℝ) := by norm_num
    have hsqrt : Real.sqrt 2 = ((R - A : ℤ) : ℝ) / (B : ℝ) := by
      have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB
      rw [eq_div_iff hBreal]
      simpa [mul_comm] using hlin
    exact (irrational_sqrt_two.ne_rational (R - A) B) hsqrt
  subst B
  have hA : (A : ℝ) = (R : ℝ) := by simpa using hre
  constructor
  · rfl
  · exact_mod_cast hA

private theorem omega_norm_div_common_denominator
    {z : ℂ} {r : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r) :
    star z * z =
      (((OmegaIntCoord.P x : ℂ) + (OmegaIntCoord.Q x : ℂ) * sqrtTwoComplex) /
        sqrtTwoComplex ^ (2 * r)) := by
  have hsstar : star (sqrtTwoComplex ^ r) = sqrtTwoComplex ^ r := by
    simp [sqrtTwoComplex]
  have hpow : sqrtTwoComplex ^ (2 * r) =
      sqrtTwoComplex ^ r * sqrtTwoComplex ^ r := by
    rw [show 2 * r = r + r by omega, pow_add]
  rw [hz]
  calc
    star (OmegaIntCoord.val x / sqrtTwoComplex ^ r) *
        (OmegaIntCoord.val x / sqrtTwoComplex ^ r)
        =
      (star (OmegaIntCoord.val x) * OmegaIntCoord.val x) /
        sqrtTwoComplex ^ (2 * r) := by
        simp [star_div, hsstar, hpow]
        field_simp [pow_ne_zero r sqrtTwoComplex_ne_zero]
    _ = ((OmegaIntCoord.P x : ℂ) + (OmegaIntCoord.Q x : ℂ) * sqrtTwoComplex) /
        sqrtTwoComplex ^ (2 * r) := by
        rw [OmegaIntCoord.norm_val]

/-- Integer-level facts from the unit-state condition at a common omega
denominator level.  Independent of `r ≥ 3`; the mod-8 version of these facts
needs `r ≥ 3` for `2^r ≡ 0`. -/
private theorem unit_state_integer_facts_at_common_level
    {z w : ℂ} {R : ℕ} {x y : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ R)
    (hw : w = OmegaIntCoord.val y / sqrtTwoComplex ^ R)
    (hState : IsUnitState z w) :
    OmegaIntCoord.P x + OmegaIntCoord.P y = (2 : ℤ) ^ R ∧
    OmegaIntCoord.Q x + OmegaIntCoord.Q y = 0 := by
  have hzNorm := omega_norm_div_common_denominator hz
  have hwNorm := omega_norm_div_common_denominator hw
  have hpow_ne : sqrtTwoComplex ^ (2 * R) ≠ 0 :=
    pow_ne_zero (2 * R) sqrtTwoComplex_ne_zero
  have hclearC :
      ((OmegaIntCoord.P x + OmegaIntCoord.P y : ℤ) : ℂ) +
          ((OmegaIntCoord.Q x + OmegaIntCoord.Q y : ℤ) : ℂ) * sqrtTwoComplex =
        (2 : ℂ) ^ R := by
    have hmul := congrArg (fun t : ℂ => t * sqrtTwoComplex ^ (2 * R)) hState
    rw [hzNorm, hwNorm] at hmul
    have hden : sqrtTwoComplex ^ (2 * R) = (2 : ℂ) ^ R := by
      rw [pow_mul, sqrtTwoComplex_sq]
    field_simp [hpow_ne] at hmul
    rw [hden] at hmul
    calc
      ((OmegaIntCoord.P x + OmegaIntCoord.P y : ℤ) : ℂ) +
          ((OmegaIntCoord.Q x + OmegaIntCoord.Q y : ℤ) : ℂ) * sqrtTwoComplex
          =
        (OmegaIntCoord.P x : ℂ) + (OmegaIntCoord.Q x : ℂ) * sqrtTwoComplex +
          ((OmegaIntCoord.P y : ℂ) + sqrtTwoComplex * (OmegaIntCoord.Q y : ℂ)) := by
          norm_num [Int.cast_add]
          ring
      _ = (2 : ℂ) ^ R := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hsplit :=
    int_add_int_mul_sqrtTwo_eq_int_early
      (A := OmegaIntCoord.P x + OmegaIntCoord.P y)
      (B := OmegaIntCoord.Q x + OmegaIntCoord.Q y)
      (R := (2 : ℤ) ^ R)
      (by simpa using hclearC)
  exact ⟨hsplit.2, hsplit.1⟩

private theorem normalized_state_residue_compat_of_common_denominator
    {z w : ℂ} {r : ℕ} {x y : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hw : w = OmegaIntCoord.val y / sqrtTwoComplex ^ r)
    (hState : IsUnitState z w)
    (hr3 : 3 ≤ r) :
    OmegaResidue.P (OmegaResidue.ofIntCoord x) +
        OmegaResidue.P (OmegaResidue.ofIntCoord y) = 0 ∧
      OmegaResidue.Q (OmegaResidue.ofIntCoord x) +
        OmegaResidue.Q (OmegaResidue.ofIntCoord y) = 0 := by
  rcases unit_state_integer_facts_at_common_level hz hw hState with ⟨hPInt, hQInt⟩
  constructor
  · rw [OmegaResidue.P_ofIntCoord, OmegaResidue.P_ofIntCoord]
    rw [← Int.cast_add, hPInt]
    norm_num [Int.cast_pow]
    have hpow8 : ((2 : ZMod 8) ^ r) = 0 := by
      have h23 : ((2 : ZMod 8) ^ 3) = 0 := by native_decide
      rw [show r = 3 + (r - 3) by omega, pow_add]
      rw [h23, zero_mul]
    simpa using hpow8
  · rw [OmegaResidue.Q_ofIntCoord, OmegaResidue.Q_ofIntCoord]
    rw [← Int.cast_add, hQInt]
    norm_num

/-- Analog of `normalized_state_residue_compat_of_common_denominator` for the
special case `r = 2`: the unit-state equation gives `P x + P y = 4` (not 0)
and `Q x + Q y = 0` in `ZMod 8`. -/
private theorem normalized_state_residue_compat_at_two
    {z w : ℂ} {x y : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ 2)
    (hw : w = OmegaIntCoord.val y / sqrtTwoComplex ^ 2)
    (hState : IsUnitState z w) :
    OmegaResidue.P (OmegaResidue.ofIntCoord x) +
        OmegaResidue.P (OmegaResidue.ofIntCoord y) = 4 ∧
      OmegaResidue.Q (OmegaResidue.ofIntCoord x) +
        OmegaResidue.Q (OmegaResidue.ofIntCoord y) = 0 := by
  rcases unit_state_integer_facts_at_common_level hz hw hState with ⟨hPInt, hQInt⟩
  -- hPInt : P x + P y = 4 (integers); hQInt : Q x + Q y = 0 (integers)
  constructor
  · rw [OmegaResidue.P_ofIntCoord, OmegaResidue.P_ofIntCoord]
    rw [← Int.cast_add, hPInt]
    norm_num
  · rw [OmegaResidue.Q_ofIntCoord, OmegaResidue.Q_ofIntCoord]
    rw [← Int.cast_add, hQInt]
    norm_num

/-! ### Exact √2-valuation on real norm pairs

For `(P, Q) : ℤ × ℤ` representing `P + Q√2 ∈ ℤ[√2]`, we record explicit
divisibility by `(√2)^n` and the corresponding GDE.  This refines the residue
mod-8 check used by the four-choice descent: it gives the *exact* minimum
denominator equality `DenNormSDE z = 2*r - j`, which the residue test alone
cannot prove. -/

/-- `P + Q√2` is divisible by `(√2)^n` in `ℤ[√2]`. -/
def NormPairSqrtTwoPowDivides (P Q : ℤ) (n : ℕ) : Prop :=
  ∃ P' Q' : ℤ,
    ((P : ℂ) + (Q : ℂ) * sqrtTwoComplex) =
      sqrtTwoComplex ^ n * ((P' : ℂ) + (Q' : ℂ) * sqrtTwoComplex)

/-- Exact greatest dividing `√2`-exponent of `P + Q√2`. -/
def NormPairSqrtTwoGDE (P Q : ℤ) (g : ℕ) : Prop :=
  NormPairSqrtTwoPowDivides P Q g ∧ ¬ NormPairSqrtTwoPowDivides P Q (g + 1)

theorem normPairSqrtTwoPowDivides_zero (P Q : ℤ) :
    NormPairSqrtTwoPowDivides P Q 0 := ⟨P, Q, by simp⟩

/-- One-step `√2`-divisibility on the real pair: `(P + Q√2) = √2 · (P' + Q'√2)`
expands to `(P + Q√2) = 2Q' + P'√2`. -/
private theorem sqrtTwo_mul_intPair_eq (a b : ℤ) :
    sqrtTwoComplex * ((a : ℂ) + (b : ℂ) * sqrtTwoComplex) =
      2 * (b : ℂ) + (a : ℂ) * sqrtTwoComplex := by
  have hsq : sqrtTwoComplex * sqrtTwoComplex = 2 := sqrtTwoComplex_mul_self
  have : sqrtTwoComplex * ((a : ℂ) + (b : ℂ) * sqrtTwoComplex) =
      (a : ℂ) * sqrtTwoComplex + (b : ℂ) * (sqrtTwoComplex * sqrtTwoComplex) := by ring
  rw [this, hsq]
  ring

theorem normPairSqrtTwoPowDivides_one_iff (P Q : ℤ) :
    NormPairSqrtTwoPowDivides P Q 1 ↔ Even P := by
  constructor
  · rintro ⟨P', Q', h⟩
    rw [pow_one, sqrtTwo_mul_intPair_eq] at h
    have hzero :
        (((P - 2 * Q' : ℤ) : ℂ) +
          ((Q - P' : ℤ) : ℂ) * sqrtTwoComplex) = ((0 : ℤ) : ℂ) := by
      push_cast
      linear_combination h
    rcases int_add_int_mul_sqrtTwo_eq_int_early hzero with ⟨_, hP⟩
    exact ⟨Q', by omega⟩
  · rintro ⟨k, hP⟩
    refine ⟨Q, k, ?_⟩
    rw [pow_one, sqrtTwo_mul_intPair_eq]
    have hP' : P = 2 * k := by omega
    rw [show (P : ℂ) = 2 * (k : ℂ) by exact_mod_cast hP']

private theorem sqrtTwoSq_mul_intPair_eq (a b : ℤ) :
    sqrtTwoComplex ^ 2 * ((a : ℂ) + (b : ℂ) * sqrtTwoComplex) =
      2 * (a : ℂ) + 2 * (b : ℂ) * sqrtTwoComplex := by
  rw [sqrtTwoComplex_sq]
  ring

theorem normPairSqrtTwoPowDivides_two_iff (P Q : ℤ) :
    NormPairSqrtTwoPowDivides P Q 2 ↔ Even P ∧ Even Q := by
  constructor
  · rintro ⟨P', Q', h⟩
    rw [sqrtTwoSq_mul_intPair_eq] at h
    have hzero :
        (((P - 2 * P' : ℤ) : ℂ) +
          ((Q - 2 * Q' : ℤ) : ℂ) * sqrtTwoComplex) = ((0 : ℤ) : ℂ) := by
      push_cast
      linear_combination h
    rcases int_add_int_mul_sqrtTwo_eq_int_early hzero with ⟨hQ, hP⟩
    refine ⟨⟨P', ?_⟩, ⟨Q', ?_⟩⟩ <;> omega
  · rintro ⟨⟨a, hP⟩, ⟨b, hQ⟩⟩
    refine ⟨a, b, ?_⟩
    rw [sqrtTwoSq_mul_intPair_eq]
    have hP' : P = 2 * a := by omega
    have hQ' : Q = 2 * b := by omega
    rw [show (P : ℂ) = 2 * (a : ℂ) by exact_mod_cast hP',
        show (Q : ℂ) = 2 * (b : ℂ) by exact_mod_cast hQ']

/-- Downward closure: divisibility by `(√2)^(n+1)` implies divisibility by `(√2)^n`. -/
theorem normPairSqrtTwoPowDivides_step
    {P Q : ℤ} {n : ℕ}
    (h : NormPairSqrtTwoPowDivides P Q (n + 1)) :
    NormPairSqrtTwoPowDivides P Q n := by
  rcases h with ⟨P', Q', h⟩
  refine ⟨2 * Q', P', ?_⟩
  rw [h, pow_succ]
  rw [show sqrtTwoComplex ^ n * sqrtTwoComplex *
      ((P' : ℂ) + (Q' : ℂ) * sqrtTwoComplex) =
        sqrtTwoComplex ^ n *
          (sqrtTwoComplex * ((P' : ℂ) + (Q' : ℂ) * sqrtTwoComplex)) by ring]
  rw [sqrtTwo_mul_intPair_eq]
  push_cast
  ring

theorem normPairSqrtTwoPowDivides_mono
    {P Q : ℤ} {n m : ℕ}
    (h : NormPairSqrtTwoPowDivides P Q m)
    (hnm : n ≤ m) :
    NormPairSqrtTwoPowDivides P Q n := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact ih (normPairSqrtTwoPowDivides_step h)

private theorem zmod8_val_even_of_even_int (P : ℤ) (h : Even P) :
    (P : ZMod 8).val % 2 = 0 := by
  obtain ⟨k, rfl⟩ := h
  have h1 : ((k + k : ℤ) : ZMod 8) = 2 * (k : ZMod 8) := by push_cast; ring
  rw [h1]
  have h2 : ∀ q : ZMod 8, (2 * q).val % 2 = 0 := by decide
  exact h2 _

private theorem zmod8_val_odd_of_odd_int (P : ℤ) (h : ¬ Even P) :
    (P : ZMod 8).val % 2 = 1 := by
  have hOdd : Odd P := Int.not_even_iff_odd.mp h
  obtain ⟨k, rfl⟩ := hOdd
  have h1 : ((2 * k + 1 : ℤ) : ZMod 8) = 2 * (k : ZMod 8) + 1 := by push_cast; ring
  rw [h1]
  have h2 : ∀ q : ZMod 8, (2 * q + 1).val % 2 = 1 := by decide
  exact h2 _

/-- An `OmegaIntCoord` not divisible by `√2` has norm-pair GDE at most one. -/
theorem not_normPairSqrtTwoPowDivides_two_of_not_sqrtTwo_dvd
    (x : OmegaIntCoord)
    (hnot : ¬ ∃ q : OmegaIntCoord,
      OmegaIntCoord.val x = sqrtTwoComplex * OmegaIntCoord.val q) :
    ¬ NormPairSqrtTwoPowDivides
        (OmegaIntCoord.P x) (OmegaIntCoord.Q x) 2 := by
  intro h
  rcases (normPairSqrtTwoPowDivides_two_iff _ _).mp h with ⟨hP, hQ⟩
  exact hnot (OmegaIntCoord.val_dvd_sqrtTwo_of_norm_pair_even x hP hQ)

/-- `sqrtTwoComplex^m` equals the cast of `(√2)^m`. -/
private theorem sqrtTwoComplex_pow_eq_ofReal (m : ℕ) :
    sqrtTwoComplex ^ m = ((Real.sqrt 2 ^ m : ℝ) : ℂ) := by
  rw [sqrtTwoComplex, ← Complex.ofReal_pow]

private theorem sqrtTwoComplex_pow_im (m : ℕ) :
    (sqrtTwoComplex ^ m).im = 0 := by
  rw [sqrtTwoComplex_pow_eq_ofReal]
  exact Complex.ofReal_im _

private theorem sqrtTwoComplex_pow_re (m : ℕ) :
    (sqrtTwoComplex ^ m).re = (Real.sqrt 2 ^ m : ℝ) := by
  rw [sqrtTwoComplex_pow_eq_ofReal]
  exact Complex.ofReal_re _

/-- Imag part of the legacy numerator vanishes when it multiplies to a real
quantity. -/
private theorem imag_coords_zero_of_real_eq_legacy_pow
    {P Q a b c d : ℤ} {m : ℕ}
    (h : ((P : ℂ) + (Q : ℂ) * sqrtTwoComplex) =
          (((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
            ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) *
            sqrtTwoComplex ^ m) :
    c = 0 ∧ d = 0 := by
  have him := congrArg Complex.im h
  have hLHS_im : ((P : ℂ) + (Q : ℂ) * sqrtTwoComplex).im = 0 := by
    simp [sqrtTwoComplex]
  have hpowRe := sqrtTwoComplex_pow_re m
  have hpowIm := sqrtTwoComplex_pow_im m
  have hRHS_im :
      ((((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
          ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) *
          sqrtTwoComplex ^ m).im =
        ((c : ℝ) + (d : ℝ) * Real.sqrt 2) * (Real.sqrt 2 ^ m) := by
    rw [Complex.mul_im, hpowIm, hpowRe]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, sqrtTwoComplex]
  rw [hLHS_im, hRHS_im] at him
  have hpow_pos : (0 : ℝ) < Real.sqrt 2 ^ m :=
    pow_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)) m
  have h_cd_real : ((c : ℝ) + (d : ℝ) * Real.sqrt 2) = 0 := by
    have h0 : ((c : ℝ) + (d : ℝ) * Real.sqrt 2) * (Real.sqrt 2 ^ m) = 0 := him.symm
    rcases mul_eq_zero.mp h0 with hcd | hpow
    · exact hcd
    · exact absurd hpow (ne_of_gt hpow_pos)
  have h_cd_complex : ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) = ((0 : ℤ) : ℂ) := by
    apply Complex.ext
    · simp [sqrtTwoComplex]
      exact_mod_cast h_cd_real
    · simp [sqrtTwoComplex]
  rcases int_add_int_mul_sqrtTwo_eq_int_early h_cd_complex with ⟨hd, hc⟩
  exact ⟨hc, hd⟩

/-- The real-pair equation implied by a legacy denominator-exponent presentation
of the squared norm. -/
private theorem normPair_eq_real_legacy_of_denominatorExponent
    {z : ℂ} {r k : ℕ} {x : OmegaIntCoord}
    {a b c d : ℤ}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hk : k ≤ 2 * r)
    (hden : star z * z =
      (((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
          ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
        sqrtTwoComplex ^ k) :
    ((OmegaIntCoord.P x : ℂ) + (OmegaIntCoord.Q x : ℂ) * sqrtTwoComplex) =
      (((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
          ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) *
        sqrtTwoComplex ^ (2 * r - k) := by
  have hnorm := omega_norm_div_common_denominator hz
  rw [hnorm] at hden
  have hpow_ne_2r : sqrtTwoComplex ^ (2 * r) ≠ 0 :=
    pow_ne_zero (2 * r) sqrtTwoComplex_ne_zero
  have hpow_ne_k : sqrtTwoComplex ^ k ≠ 0 :=
    pow_ne_zero k sqrtTwoComplex_ne_zero
  have hpow_ne_diff : sqrtTwoComplex ^ (2 * r - k) ≠ 0 :=
    pow_ne_zero (2 * r - k) sqrtTwoComplex_ne_zero
  have hpow_eq : sqrtTwoComplex ^ (2 * r) =
      sqrtTwoComplex ^ k * sqrtTwoComplex ^ (2 * r - k) := by
    rw [← pow_add, show k + (2 * r - k) = 2 * r by omega]
  rw [div_eq_div_iff hpow_ne_2r hpow_ne_k] at hden
  rw [hpow_eq] at hden
  -- hden : (P + Q√2) * sqrt2^k = legacy * (sqrt2^k * sqrt2^(2r-k))
  -- Rearrange RHS as (legacy * sqrt2^(2r-k)) * sqrt2^k, then cancel.
  have hassoc :
      (((a : ℂ) + (b : ℂ) * sqrtTwoComplex +
            ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I)) *
        (sqrtTwoComplex ^ k * sqrtTwoComplex ^ (2 * r - k)) =
      ((((a : ℂ) + (b : ℂ) * sqrtTwoComplex +
            ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I)) *
        sqrtTwoComplex ^ (2 * r - k)) * sqrtTwoComplex ^ k := by ring
  rw [hassoc] at hden
  exact mul_right_cancel₀ hpow_ne_k hden

/-- Upper bound for `DenNormSDE z`: if `(P x, Q x)` is divisible by `sqrt2^j`
in `ℤ[√2]`, then `star z * z` has a presentation at denominator level
`2*r - j`. -/
private theorem hasDenominatorExponent_starzz_le_of_normPairDvd
    {z : ℂ} {r j : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hjr : j ≤ 2 * r)
    (hdvd : NormPairSqrtTwoPowDivides (OmegaIntCoord.P x) (OmegaIntCoord.Q x) j) :
    HasDenominatorExponent (star z * z) (2 * r - j) := by
  rcases hdvd with ⟨P', Q', hpair⟩
  refine ⟨P', Q', 0, 0, ?_⟩
  rw [omega_norm_div_common_denominator hz, hpair]
  have hpow_ne_j : sqrtTwoComplex ^ j ≠ 0 := pow_ne_zero j sqrtTwoComplex_ne_zero
  have hpow_ne_diff : sqrtTwoComplex ^ (2 * r - j) ≠ 0 :=
    pow_ne_zero (2 * r - j) sqrtTwoComplex_ne_zero
  have hpow_eq : sqrtTwoComplex ^ (2 * r) =
      sqrtTwoComplex ^ j * sqrtTwoComplex ^ (2 * r - j) := by
    rw [← pow_add, show j + (2 * r - j) = 2 * r by omega]
  rw [hpow_eq]
  push_cast
  field_simp
  ring

/-- Lower bound for `DenNormSDE z`: if `(P x, Q x)` has greatest `√2`-dividing
exponent exactly `j`, then any presentation of `star z * z` has denominator
exponent at least `2*r - j`. -/
private theorem sde_starzz_ge_of_normPairGDE
    {z : ℂ} {r j : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hzDyadic : InDyadicCyclotomic z)
    (hgde : NormPairSqrtTwoGDE (OmegaIntCoord.P x) (OmegaIntCoord.Q x) j) :
    2 * r - j ≤ sde (star z * z) := by
  by_contra hlt
  push_neg at hlt
  set k := sde (star z * z) with hk_def
  have hk_lt : k < 2 * r - j := hlt
  have hk_le : k ≤ 2 * r := by omega
  have hzz_dyadic : InDyadicCyclotomic (star z * z) :=
    InDyadicCyclotomic.mul (InDyadicCyclotomic.star hzDyadic) hzDyadic
  have hk_dvd : HasDenominatorExponent (star z * z) k :=
    hasDenominatorExponent_sde hzz_dyadic
  rcases hk_dvd with ⟨a, b, c, d, hk_pres⟩
  have heq := normPair_eq_real_legacy_of_denominatorExponent
    (z := z) (r := r) (k := k) (x := x) (a := a) (b := b) (c := c) (d := d)
    hz hk_le hk_pres
  rcases imag_coords_zero_of_real_eq_legacy_pow heq with ⟨hc, hd⟩
  subst hc; subst hd
  have hdvd_2r_k :
      NormPairSqrtTwoPowDivides (OmegaIntCoord.P x) (OmegaIntCoord.Q x)
        (2 * r - k) := by
    refine ⟨a, b, ?_⟩
    calc ((OmegaIntCoord.P x : ℂ) + (OmegaIntCoord.Q x : ℂ) * sqrtTwoComplex)
        = ((a : ℂ) + (b : ℂ) * sqrtTwoComplex +
            (((0 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * sqrtTwoComplex) * Complex.I) *
          sqrtTwoComplex ^ (2 * r - k) := heq
      _ = sqrtTwoComplex ^ (2 * r - k) * ((a : ℂ) + (b : ℂ) * sqrtTwoComplex) := by
          push_cast; ring
  have hge : j + 1 ≤ 2 * r - k := by omega
  exact hgde.2 (normPairSqrtTwoPowDivides_mono hdvd_2r_k hge)

/-- Exact `DenNormSDE` equality: when the omega presentation `z = val x / sqrt2^r`
is minimal, the squared-norm denominator exponent is `2*r - j` where `j` is
the exact `√2`-GDE of the integer pair `(P x, Q x)`. -/
private theorem denNormSDE_eq_two_r_sub_j_of_normPairGDE
    {z : ℂ} {r j : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hzDyadic : InDyadicCyclotomic z)
    (hgde : NormPairSqrtTwoGDE (OmegaIntCoord.P x) (OmegaIntCoord.Q x) j)
    (hjr : j ≤ 2 * r) :
    DenNormSDE z = 2 * r - j := by
  have hupper :=
    sde_le_of_hasDenominatorExponent
      (hasDenominatorExponent_starzz_le_of_normPairDvd hz hjr hgde.1)
  have hlower := sde_starzz_ge_of_normPairGDE hz hzDyadic hgde
  unfold DenNormSDE
  omega


/-- `r ≥ 3` whenever the squared-norm denominator exponent reaches 5. -/
private theorem minimal_omega_denominator_ge_three_of_large_norm_sde
    {z : ℂ} {r : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hLarge : 5 ≤ DenNormSDE z) :
    3 ≤ r := by
  have hpres : HasDenominatorExponent (star z * z) (2 * r) := by
    refine ⟨OmegaIntCoord.P x, OmegaIntCoord.Q x, 0, 0, ?_⟩
    rw [omega_norm_div_common_denominator hz]
    simp
  have hle : sde (star z * z) ≤ 2 * r :=
    sde_le_of_hasDenominatorExponent hpres
  unfold DenNormSDE at hLarge
  omega

/-- Square-norm scaling: `P(√2^n · x) = 2^n · P(x)`, `Q(√2^n · x) = 2^n · Q(x)`. -/
private theorem PQ_sqrtTwoPowMul (n : ℕ) (x : OmegaIntCoord) :
    OmegaIntCoord.P (OmegaIntCoord.sqrtTwoPowMul n x) =
      (2 : ℤ) ^ n * OmegaIntCoord.P x ∧
    OmegaIntCoord.Q (OmegaIntCoord.sqrtTwoPowMul n x) =
      (2 : ℤ) ^ n * OmegaIntCoord.Q x := by
  have hval := OmegaIntCoord.val_sqrtTwoPowMul n x
  have hnorm_lhs := OmegaIntCoord.norm_val (OmegaIntCoord.sqrtTwoPowMul n x)
  have hnorm_x := OmegaIntCoord.norm_val x
  have hsstar_pow : star (sqrtTwoComplex ^ n) = sqrtTwoComplex ^ n := by
    simp [sqrtTwoComplex]
  have heq :
      ((OmegaIntCoord.P (OmegaIntCoord.sqrtTwoPowMul n x) : ℂ) +
          (OmegaIntCoord.Q (OmegaIntCoord.sqrtTwoPowMul n x) : ℂ) *
            sqrtTwoComplex) =
        (sqrtTwoComplex ^ (2 * n)) *
          ((OmegaIntCoord.P x : ℂ) + (OmegaIntCoord.Q x : ℂ) * sqrtTwoComplex) := by
    rw [← hnorm_lhs, ← hnorm_x, hval, star_mul, hsstar_pow]
    rw [show sqrtTwoComplex ^ (2 * n) = sqrtTwoComplex ^ n * sqrtTwoComplex ^ n by
      rw [← pow_add, two_mul]]
    ring
  have hpow2 : sqrtTwoComplex ^ (2 * n) = ((2 : ℤ) ^ n : ℂ) := by
    rw [pow_mul, sqrtTwoComplex_sq]
    push_cast; ring
  rw [hpow2] at heq
  have hzero :
      ((OmegaIntCoord.P (OmegaIntCoord.sqrtTwoPowMul n x) -
          (2 : ℤ) ^ n * OmegaIntCoord.P x : ℤ) : ℂ) +
        ((OmegaIntCoord.Q (OmegaIntCoord.sqrtTwoPowMul n x) -
          (2 : ℤ) ^ n * OmegaIntCoord.Q x : ℤ) : ℂ) * sqrtTwoComplex =
      ((0 : ℤ) : ℂ) := by
    push_cast
    linear_combination heq
  rcases int_add_int_mul_sqrtTwo_eq_int_early hzero with ⟨hQ, hP⟩
  exact ⟨by omega, by omega⟩

/-- Helper: lift omega presentation up by `d` levels via the explicit scaling. -/
private theorem lift_omega_pres_up
    {w : ℂ} {s d : ℕ} {y : OmegaIntCoord}
    (hy : w = OmegaIntCoord.val y / sqrtTwoComplex ^ s) :
    w = OmegaIntCoord.val (OmegaIntCoord.sqrtTwoPowMul d y) /
        sqrtTwoComplex ^ (s + d) := by
  rw [hy, OmegaIntCoord.val_sqrtTwoPowMul, pow_add]
  field_simp [pow_ne_zero s sqrtTwoComplex_ne_zero,
    pow_ne_zero d sqrtTwoComplex_ne_zero]

/-- Even power of two ≥ 1 means the value is even. -/
private theorem even_two_pow_mul {n : ℕ} (hn : 1 ≤ n) (a : ℤ) :
    Even ((2 : ℤ) ^ n * a) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨(2 : ℤ) ^ m * a, ?_⟩
  rw [pow_succ]
  ring

/-- Even pow-of-two combined: if `a + 2^n · b = 2^r` with `n ≥ 1` and `r ≥ 1`,
then `a` is even.  -/
private theorem even_of_int_eq_two_pow_minus_two_pow_mul
    {a b : ℤ} {n r : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r)
    (h : a + (2 : ℤ) ^ n * b = (2 : ℤ) ^ r) :
    Even a := by
  have h1 : a = (2 : ℤ) ^ r - (2 : ℤ) ^ n * b := by linarith
  rw [h1]
  refine Even.sub ?_ (even_two_pow_mul hn b)
  refine ⟨(2 : ℤ) ^ (r - 1), ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  simp [pow_succ]; ring

/-- If `a + 2^n · b = 0` with `n ≥ 1`, then `a` is even. -/
private theorem even_of_int_eq_neg_two_pow_mul
    {a b : ℤ} {n : ℕ}
    (hn : 1 ≤ n)
    (h : a + (2 : ℤ) ^ n * b = 0) :
    Even a := by
  have h1 : a = -((2 : ℤ) ^ n * b) := by linarith
  rw [h1]
  exact Even.neg (even_two_pow_mul hn b)

/-- Under unit-state and minimal-z with sufficiently large squared-norm,
`omegaSDE w ≤ r`.  Used to lift `w` to the common denominator `r`. -/
private theorem omegaSDE_w_le_r_of_minimal_z
    {z w : ℂ} {r : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hr : omegaSDE z = r)
    (hr3 : 3 ≤ r)
    (hwDyadic : InOmegaDyadicCyclotomic w)
    (hState : IsUnitState z w) :
    omegaSDE w ≤ r := by
  by_contra hgt
  push_neg at hgt
  rcases hasOmegaDenominatorExponent_of_inOmegaDyadicCyclotomic hwDyadic with ⟨y_min, hy_min⟩
  have hy_NotDvd :
      ¬ ∃ q : OmegaIntCoord,
        OmegaIntCoord.val y_min = sqrtTwoComplex * OmegaIntCoord.val q := by
    have hs_pos : 0 < omegaSDE w := by omega
    have h := sqrtTwoGDE_zero_of_minimal_omega_denominator_pos hy_min rfl hs_pos
    exact OmegaIntCoord.sqrtTwoGDE_zero_not_sqrtTwo_dvd h
  -- Lift z to level omegaSDE w
  let d := omegaSDE w - r
  have hd_pos : 1 ≤ d := by omega
  let x' := OmegaIntCoord.sqrtTwoPowMul d x
  have hz_s : z = OmegaIntCoord.val x' / sqrtTwoComplex ^ omegaSDE w := by
    have := lift_omega_pres_up (d := d) hz
    rw [show r + d = omegaSDE w by omega] at this
    exact this
  rcases unit_state_integer_facts_at_common_level hz_s hy_min hState with ⟨hP, hQ⟩
  rcases PQ_sqrtTwoPowMul d x with ⟨hPx', hQx'⟩
  -- P y_min = 2^(omegaSDE w) - P x' = 2^(omegaSDE w) - 2^d * P x (even since d ≥ 1).
  have hPy_even : Even (OmegaIntCoord.P y_min) := by
    have hsum : OmegaIntCoord.P y_min + (2 : ℤ) ^ d * OmegaIntCoord.P x =
        (2 : ℤ) ^ omegaSDE w := by
      have := hP
      rw [hPx'] at this
      linarith
    exact even_of_int_eq_two_pow_minus_two_pow_mul hd_pos (by omega) hsum
  have hQy_even : Even (OmegaIntCoord.Q y_min) := by
    have hsum : OmegaIntCoord.Q y_min + (2 : ℤ) ^ d * OmegaIntCoord.Q x = 0 := by
      have := hQ
      rw [hQx'] at this
      linarith
    exact even_of_int_eq_neg_two_pow_mul hd_pos hsum
  exact hy_NotDvd
    (OmegaIntCoord.val_dvd_sqrtTwo_of_norm_pair_even y_min hPy_even hQy_even)

/-- Denominator synchronization for unit states.

If `z` is presented at omega-denominator level `r` and `(z,w)` is a unit
state with `w ∈ D[ω]`, then `w` also has an omega-denominator presentation at
level `r`.  This is the reusable denominator half of the Ross-Selinger
completion argument: no companion entry can require a larger denominator than
the displayed level of the first entry. -/
theorem omegaSDE_second_le_of_unit_state_common_denominator
    {z w : ℂ} {r : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hwDyadic : InOmegaDyadicCyclotomic w)
    (hState : IsUnitState z w) :
    omegaSDE w ≤ r := by
  by_contra hgt
  push_neg at hgt
  rcases hasOmegaDenominatorExponent_of_inOmegaDyadicCyclotomic hwDyadic with ⟨y_min, hy_min⟩
  have hy_NotDvd :
      ¬ ∃ q : OmegaIntCoord,
        OmegaIntCoord.val y_min = sqrtTwoComplex * OmegaIntCoord.val q := by
    have hs_pos : 0 < omegaSDE w := by omega
    have h := sqrtTwoGDE_zero_of_minimal_omega_denominator_pos hy_min rfl hs_pos
    exact OmegaIntCoord.sqrtTwoGDE_zero_not_sqrtTwo_dvd h
  let d := omegaSDE w - r
  have hd_pos : 1 ≤ d := by omega
  let x' := OmegaIntCoord.sqrtTwoPowMul d x
  have hz_s : z = OmegaIntCoord.val x' / sqrtTwoComplex ^ omegaSDE w := by
    have := lift_omega_pres_up (d := d) hz
    rw [show r + d = omegaSDE w by omega] at this
    exact this
  rcases unit_state_integer_facts_at_common_level hz_s hy_min hState with ⟨hP, hQ⟩
  rcases PQ_sqrtTwoPowMul d x with ⟨hPx', hQx'⟩
  have hPy_even : Even (OmegaIntCoord.P y_min) := by
    have hsum : OmegaIntCoord.P y_min + (2 : ℤ) ^ d * OmegaIntCoord.P x =
        (2 : ℤ) ^ omegaSDE w := by
      have := hP
      rw [hPx'] at this
      linarith
    exact even_of_int_eq_two_pow_minus_two_pow_mul hd_pos (by omega) hsum
  have hQy_even : Even (OmegaIntCoord.Q y_min) := by
    have hsum : OmegaIntCoord.Q y_min + (2 : ℤ) ^ d * OmegaIntCoord.Q x = 0 := by
      have := hQ
      rw [hQx'] at this
      linarith
    exact even_of_int_eq_neg_two_pow_mul hd_pos hsum
  exact hy_NotDvd
    (OmegaIntCoord.val_dvd_sqrtTwo_of_norm_pair_even y_min hPy_even hQy_even)

/-! ### Phase 1: structural coordinate bound for the canonical omega numerator

For any unit state `(z, w)` over `D[ω]` with `z = val(x)/sqrt2^r`, the
integer sum-of-squares `P x = x.x0² + x.x1² + x.x2² + x.x3²` is bounded by
`2^r`.  This is the entry point of the classifier that will eventually replace
the discarded ad-hoc state enumeration in the low-`DenNormSDE` base case.

The bound is obtained from the unit-state integer equation
`P x' + P y' = 2^R` at any common denominator level `R ≥ omegaSDE z, omegaSDE w`,
combined with non-negativity of both `P` values. -/

private theorem omegaIntCoord_P_nonneg (x : OmegaIntCoord) :
    0 ≤ OmegaIntCoord.P x := by
  unfold OmegaIntCoord.P
  positivity

private theorem omegaIntCoord_x0_sq_le_P (x : OmegaIntCoord) :
    x.x0 ^ 2 ≤ OmegaIntCoord.P x := by
  unfold OmegaIntCoord.P
  nlinarith [sq_nonneg x.x1, sq_nonneg x.x2, sq_nonneg x.x3]

private theorem omegaIntCoord_x1_sq_le_P (x : OmegaIntCoord) :
    x.x1 ^ 2 ≤ OmegaIntCoord.P x := by
  unfold OmegaIntCoord.P
  nlinarith [sq_nonneg x.x0, sq_nonneg x.x2, sq_nonneg x.x3]

private theorem omegaIntCoord_x2_sq_le_P (x : OmegaIntCoord) :
    x.x2 ^ 2 ≤ OmegaIntCoord.P x := by
  unfold OmegaIntCoord.P
  nlinarith [sq_nonneg x.x0, sq_nonneg x.x1, sq_nonneg x.x3]

private theorem omegaIntCoord_x3_sq_le_P (x : OmegaIntCoord) :
    x.x3 ^ 2 ≤ OmegaIntCoord.P x := by
  unfold OmegaIntCoord.P
  nlinarith [sq_nonneg x.x0, sq_nonneg x.x1, sq_nonneg x.x2]

/-- **Phase 1 / Main bound.** If `z = val(x)/sqrt2^r` lies in a unit state
`(z, w)` with `w ∈ D[ω]`, then the omega-coordinate sum-of-squares `P x` is
bounded by `2^r`. -/
theorem omegaIntCoord_P_le_two_pow_of_unit_state
    {z w : ℂ} {r : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hwDyadic : InOmegaDyadicCyclotomic w)
    (hState : IsUnitState z w) :
    OmegaIntCoord.P x ≤ (2 : ℤ) ^ r := by
  classical
  let s := omegaSDE w
  let R := max r s
  have hR_ge_r : r ≤ R := le_max_left r s
  have hR_ge_s : s ≤ R := le_max_right r s
  -- Lift z up to level R.
  let x' := OmegaIntCoord.sqrtTwoPowMul (R - r) x
  have hz_R : z = OmegaIntCoord.val x' / sqrtTwoComplex ^ R := by
    have hlift := lift_omega_pres_up (d := R - r) hz
    rw [show r + (R - r) = R by omega] at hlift
    exact hlift
  -- Lift w up to level R via its minimal omega presentation.
  let y_min := Classical.choose
    (hasOmegaDenominatorExponent_of_inOmegaDyadicCyclotomic hwDyadic)
  have hy_min : w = OmegaIntCoord.val y_min / sqrtTwoComplex ^ s :=
    Classical.choose_spec
      (hasOmegaDenominatorExponent_of_inOmegaDyadicCyclotomic hwDyadic)
  let y' := OmegaIntCoord.sqrtTwoPowMul (R - s) y_min
  have hw_R : w = OmegaIntCoord.val y' / sqrtTwoComplex ^ R := by
    have hlift := lift_omega_pres_up (d := R - s) hy_min
    rw [show s + (R - s) = R by omega] at hlift
    exact hlift
  -- Integer equation at the common level.
  rcases unit_state_integer_facts_at_common_level hz_R hw_R hState with ⟨hPint, _hQint⟩
  rcases PQ_sqrtTwoPowMul (R - r) x with ⟨hPx', _⟩
  -- 2^(R-r) * P x = P x', P y' ≥ 0, hence 2^(R-r) * P x ≤ 2^R.
  have hPy_nonneg : 0 ≤ OmegaIntCoord.P y' :=
    omegaIntCoord_P_nonneg y'
  have hPx'_le : OmegaIntCoord.P x' ≤ (2 : ℤ) ^ R := by linarith
  have hPow_split : (2 : ℤ) ^ R = 2 ^ (R - r) * 2 ^ r := by
    rw [← pow_add, show (R - r) + r = R by omega]
  have hineq : 2 ^ (R - r) * OmegaIntCoord.P x ≤ 2 ^ (R - r) * 2 ^ r := by
    rw [← hPx', ← hPow_split]; exact hPx'_le
  have hpow_pos : (0 : ℤ) < 2 ^ (R - r) := by positivity
  exact Int.le_of_mul_le_mul_left hineq hpow_pos

/-- Corollary: each individual omega coordinate `x.x_i` satisfies `x_i² ≤ 2^r`. -/
theorem omegaIntCoord_coords_sq_le_two_pow_of_unit_state
    {z w : ℂ} {r : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hwDyadic : InOmegaDyadicCyclotomic w)
    (hState : IsUnitState z w) :
    x.x0 ^ 2 ≤ (2 : ℤ) ^ r ∧
    x.x1 ^ 2 ≤ (2 : ℤ) ^ r ∧
    x.x2 ^ 2 ≤ (2 : ℤ) ^ r ∧
    x.x3 ^ 2 ≤ (2 : ℤ) ^ r := by
  have hP := omegaIntCoord_P_le_two_pow_of_unit_state hz hwDyadic hState
  exact ⟨(omegaIntCoord_x0_sq_le_P x).trans hP,
         (omegaIntCoord_x1_sq_le_P x).trans hP,
         (omegaIntCoord_x2_sq_le_P x).trans hP,
         (omegaIntCoord_x3_sq_le_P x).trans hP⟩

/-! ### Phase 1 warm-up: classification at `omegaSDE z = 0`

The base of the structural classifier. When `z ∈ ℤ[ω]` (no `√2` denominator)
sits in a unit state, the omega coordinate `x` lies in a 9-element finite set:
the zero vector and the eight `±ω^k` generators.  No external enumeration is
trusted — the list is derived from `P x ≤ 1` and integer parity. -/

/-- For a unit state at `omegaSDE z = 0`, the sum-of-squares of the omega
numerator is at most `1`. -/
theorem unit_state_omegaSDE_zero_P_le_one
    {z w : ℂ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x)
    (hwDyadic : InOmegaDyadicCyclotomic w)
    (hState : IsUnitState z w) :
    OmegaIntCoord.P x ≤ 1 := by
  have hzpres : z = OmegaIntCoord.val x / sqrtTwoComplex ^ 0 := by
    simp [hz]
  have hbound := omegaIntCoord_P_le_two_pow_of_unit_state hzpres hwDyadic hState
  simpa using hbound

/-- Classifier (warm-up): for a unit state at `omegaSDE z = 0`, the omega
coordinate `x` is one of nine explicit values — the zero vector or one of
the eight basis generators `±ω^k`. -/
theorem unit_state_omegaSDE_zero_classification
    {z w : ℂ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x)
    (hwDyadic : InOmegaDyadicCyclotomic w)
    (hState : IsUnitState z w) :
    x = ⟨0, 0, 0, 0⟩ ∨
    x = ⟨1, 0, 0, 0⟩ ∨ x = ⟨-1, 0, 0, 0⟩ ∨
    x = ⟨0, 1, 0, 0⟩ ∨ x = ⟨0, -1, 0, 0⟩ ∨
    x = ⟨0, 0, 1, 0⟩ ∨ x = ⟨0, 0, -1, 0⟩ ∨
    x = ⟨0, 0, 0, 1⟩ ∨ x = ⟨0, 0, 0, -1⟩ := by
  have hPle := unit_state_omegaSDE_zero_P_le_one hz hwDyadic hState
  cases x with
  | mk a b c d =>
    -- Each x_i² ≤ P x ≤ 1, so x_i ∈ {-1, 0, 1}.
    have ha : a ^ 2 ≤ 1 :=
      (omegaIntCoord_x0_sq_le_P ⟨a, b, c, d⟩).trans hPle
    have hb : b ^ 2 ≤ 1 :=
      (omegaIntCoord_x1_sq_le_P ⟨a, b, c, d⟩).trans hPle
    have hc : c ^ 2 ≤ 1 :=
      (omegaIntCoord_x2_sq_le_P ⟨a, b, c, d⟩).trans hPle
    have hd : d ^ 2 ≤ 1 :=
      (omegaIntCoord_x3_sq_le_P ⟨a, b, c, d⟩).trans hPle
    have halo : -1 ≤ a := by nlinarith [sq_nonneg (a + 1)]
    have hahi : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
    have hblo : -1 ≤ b := by nlinarith [sq_nonneg (b + 1)]
    have hbhi : b ≤ 1 := by nlinarith [sq_nonneg (b - 1)]
    have hclo : -1 ≤ c := by nlinarith [sq_nonneg (c + 1)]
    have hchi : c ≤ 1 := by nlinarith [sq_nonneg (c - 1)]
    have hdlo : -1 ≤ d := by nlinarith [sq_nonneg (d + 1)]
    have hdhi : d ≤ 1 := by nlinarith [sq_nonneg (d - 1)]
    unfold OmegaIntCoord.P at hPle
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
      first
      | (left; rfl)
      | (right; left; rfl)
      | (right; right; left; rfl)
      | (right; right; right; left; rfl)
      | (right; right; right; right; left; rfl)
      | (right; right; right; right; right; left; rfl)
      | (right; right; right; right; right; right; left; rfl)
      | (right; right; right; right; right; right; right; left; rfl)
      | (right; right; right; right; right; right; right; right; rfl)
      | (exfalso; norm_num at hPle)

/-! ### Step 1: classifier at `omegaSDE z = 1`

`P x ≤ 2` and each coordinate `x.x_i ∈ {-1, 0, 1}`.  We do not enforce the
minimality side condition (`x` not divisible by `√2`) in the bound; the
33-case enumeration is intentionally exposed only via the coordinate range,
keeping the disjunction tractable for downstream consumers. -/

/-- For a unit state at `omegaSDE z = 1`, `P x ≤ 2`. -/
theorem unit_state_omegaSDE_one_P_le_two
    {z w : ℂ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex)
    (hwDyadic : InOmegaDyadicCyclotomic w)
    (hState : IsUnitState z w) :
    OmegaIntCoord.P x ≤ 2 := by
  have hzpres : z = OmegaIntCoord.val x / sqrtTwoComplex ^ 1 := by
    simp [hz]
  have hbound := omegaIntCoord_P_le_two_pow_of_unit_state hzpres hwDyadic hState
  simpa using hbound

/-- Coordinate-range form of the `omegaSDE z = 1` bound: each `x.x_i ∈ {-1, 0, 1}`. -/
theorem unit_state_omegaSDE_one_coords_in_range
    {z w : ℂ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex)
    (hwDyadic : InOmegaDyadicCyclotomic w)
    (hState : IsUnitState z w) :
    (-1 ≤ x.x0 ∧ x.x0 ≤ 1) ∧
    (-1 ≤ x.x1 ∧ x.x1 ≤ 1) ∧
    (-1 ≤ x.x2 ∧ x.x2 ≤ 1) ∧
    (-1 ≤ x.x3 ∧ x.x3 ≤ 1) := by
  have hzpres : z = OmegaIntCoord.val x / sqrtTwoComplex ^ 1 := by simp [hz]
  rcases omegaIntCoord_coords_sq_le_two_pow_of_unit_state hzpres hwDyadic hState
    with ⟨h0, h1, h2, h3⟩
  have h0' : x.x0 ^ 2 ≤ 2 := by simpa using h0
  have h1' : x.x1 ^ 2 ≤ 2 := by simpa using h1
  have h2' : x.x2 ^ 2 ≤ 2 := by simpa using h2
  have h3' : x.x3 ^ 2 ≤ 2 := by simpa using h3
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    nlinarith [sq_nonneg (x.x0 + 1), sq_nonneg (x.x0 - 1),
               sq_nonneg (x.x1 + 1), sq_nonneg (x.x1 - 1),
               sq_nonneg (x.x2 + 1), sq_nonneg (x.x2 - 1),
               sq_nonneg (x.x3 + 1), sq_nonneg (x.x3 - 1)]

private structure KMMStateSDEGDEFacts
    (z w : ℂ) (r : ℕ) (x y : OmegaIntCoord) where
  hzMin : omegaSDE z = r
  hwMin : omegaSDE w ≤ r
  j : ℕ
  hj : j = 0 ∨ j = 1
  hlevel : DenNormSDE z = 2 * r - j
  hNormZ : OmegaResidue.normGDEEq j (OmegaResidue.ofIntCoord x) = true
  hNormW : OmegaResidue.normGDEEq j (OmegaResidue.ofIntCoord y) = true
  hP :
    OmegaResidue.P (OmegaResidue.ofIntCoord x) +
      OmegaResidue.P (OmegaResidue.ofIntCoord y) = 0
  hQ :
    OmegaResidue.Q (OmegaResidue.ofIntCoord x) +
      OmegaResidue.Q (OmegaResidue.ofIntCoord y) = 0

private structure KMMStateSDEGDEPackage
    (z w : ℂ) (r : ℕ) (x : OmegaIntCoord) where
  y : OmegaIntCoord
  hy : w = OmegaIntCoord.val y / sqrtTwoComplex ^ r
  facts : KMMStateSDEGDEFacts z w r x y

private noncomputable def kmm_state_sde_gde_facts_from_minimal_z
    {z w : ℂ}
    {nw : ℕ} {e f g h : ℤ}
    {r : ℕ} {x : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hr : omegaSDE z = r)
    (hwLegacy : w = cyclotomicIntegerCoord e f g h / sqrtTwoComplex ^ nw)
    (hState : IsUnitState z w)
    (hLarge : 5 ≤ DenNormSDE z) :
    KMMStateSDEGDEPackage z w r x := by
  -- r ≥ 3 from large norm.
  have hr3 : 3 ≤ r := minimal_omega_denominator_ge_three_of_large_norm_sde hz hLarge
  have hpos : 0 < r := by omega
  -- w is in InOmegaDyadicCyclotomic by the legacy presentation.
  have hwDyadic : InOmegaDyadicCyclotomic w := by
    refine ⟨nw, omegaCoordOfLegacy e f g h, ?_⟩
    simpa [omegaCoordOfLegacy_val, cyclotomicIntegerCoord] using hwLegacy
  -- Lift w to a presentation at level r.
  have hw_le_r : omegaSDE w ≤ r :=
    omegaSDE_w_le_r_of_minimal_z hz hr hr3 hwDyadic hState
  let y_min := Classical.choose
    (hasOmegaDenominatorExponent_of_inOmegaDyadicCyclotomic hwDyadic)
  have hy_min : w = OmegaIntCoord.val y_min / sqrtTwoComplex ^ omegaSDE w :=
    Classical.choose_spec
      (hasOmegaDenominatorExponent_of_inOmegaDyadicCyclotomic hwDyadic)
  let d := r - omegaSDE w
  let y := OmegaIntCoord.sqrtTwoPowMul d y_min
  have hy : w = OmegaIntCoord.val y / sqrtTwoComplex ^ r := by
    have hlift := lift_omega_pres_up (d := d) hy_min
    rw [show omegaSDE w + d = r by omega] at hlift
    exact hlift
  -- z is in D[ω].  We rebuild a legacy `(a, b, c, d)` presentation from the omega
  -- coords of x.  Using x = (a0,a1,a2,a3):
  -- val x = a0 + a1·ω + a2·ω² + a3·ω³ = a0 - a3/√2 + i(a2 + (a1+a3)/√2) + (a1/√2)
  --       = (2 a0 + (a1 - a3)√2 + (2 a2 + (a1 + a3)√2) i) / 2.
  -- So z = val x / √2^r = ((2 a0) + (a1 - a3)√2 + (2 a2 + (a1 + a3)√2)·i) / √2^(r+2).
  have hzDyadic : InDyadicCyclotomic z := by
    rcases x with ⟨a0, a1, a2, a3⟩
    refine ⟨r + 2, 2 * a0, a1 - a3, 2 * a2, a1 + a3, ?_⟩
    rw [hz]
    simp only [OmegaIntCoord.val]
    have hs : sqrtTwoComplex ≠ 0 := sqrtTwoComplex_ne_zero
    have hpow_r : sqrtTwoComplex ^ r ≠ 0 := pow_ne_zero r hs
    rw [show sqrtTwoComplex ^ (r + 2) = sqrtTwoComplex ^ r * sqrtTwoComplex ^ 2 by
      rw [pow_add]]
    rw [sqrtTwoComplex_sq]
    have hrwo : rsOmegaAlg ^ 2 = Complex.I := rsOmegaAlg_sq
    have hrwo3 : rsOmegaAlg ^ 3 = (-1 + Complex.I) / sqrtTwoComplex := rsOmegaAlg_cube
    have hrwo_def : rsOmegaAlg = (1 + Complex.I) / sqrtTwoComplex := rfl
    rw [hrwo, hrwo3, hrwo_def]
    field_simp [hs, hpow_r]
    push_cast
    linear_combination
      -((a1 : ℂ) - (a3 : ℂ) + ((a1 : ℂ) + (a3 : ℂ)) * Complex.I) * sqrtTwoComplex_mul_self
  -- Establish exact GDE j on (P x, Q x).
  have hxNotDvd :
      ¬ ∃ q : OmegaIntCoord,
        OmegaIntCoord.val x = sqrtTwoComplex * OmegaIntCoord.val q :=
    OmegaIntCoord.sqrtTwoGDE_zero_not_sqrtTwo_dvd
      (sqrtTwoGDE_zero_of_minimal_omega_denominator_pos hz hr hpos)
  have h_not_dvd2 :
      ¬ NormPairSqrtTwoPowDivides (OmegaIntCoord.P x) (OmegaIntCoord.Q x) 2 :=
    not_normPairSqrtTwoPowDivides_two_of_not_sqrtTwo_dvd x hxNotDvd
  -- Case on Even (P x) to determine j ∈ {0, 1}.
  by_cases hPxEven : Even (OmegaIntCoord.P x)
  · -- j = 1 case
    have hgde : NormPairSqrtTwoGDE (OmegaIntCoord.P x) (OmegaIntCoord.Q x) 1 :=
      ⟨(normPairSqrtTwoPowDivides_one_iff _ _).mpr hPxEven, h_not_dvd2⟩
    have hlevel : DenNormSDE z = 2 * r - 1 :=
      denNormSDE_eq_two_r_sub_j_of_normPairGDE hz hzDyadic hgde (by omega)
    rcases normalized_state_residue_compat_of_common_denominator hz hy hState hr3
      with ⟨hP, hQ⟩
    -- residue-level facts from Even (P x) and ¬(Even P x ∧ Even Q x)
    have hQxNotEven : ¬ Even (OmegaIntCoord.Q x) := by
      intro hQ
      exact h_not_dvd2 ((normPairSqrtTwoPowDivides_two_iff _ _).mpr ⟨hPxEven, hQ⟩)
    have hP_val : ((OmegaIntCoord.P x : ZMod 8)).val % 2 = 0 :=
      zmod8_val_even_of_even_int _ hPxEven
    have hQ_val : ((OmegaIntCoord.Q x : ZMod 8)).val % 2 = 1 :=
      zmod8_val_odd_of_odd_int _ hQxNotEven
    have hNormZ : OmegaResidue.normGDEEq 1 (OmegaResidue.ofIntCoord x) = true := by
      rw [OmegaResidue.normGDEEq, OmegaResidue.P_ofIntCoord,
        OmegaResidue.Q_ofIntCoord]
      have hclassify :
          ∀ A B : ZMod 8, A.val % 2 = 0 → B.val % 2 = 1 →
            OmegaResidue.sqrtTwoGDEEqPair 1 A B = true := by decide
      exact hclassify _ _ hP_val hQ_val
    have hNormW : OmegaResidue.normGDEEq 1 (OmegaResidue.ofIntCoord y) = true :=
      OmegaResidue.normGDEEq_of_neg_norm_pair hNormZ hP hQ
    exact ⟨y, hy, hr, hw_le_r, 1, Or.inr rfl, hlevel, hNormZ, hNormW, hP, hQ⟩
  · -- j = 0 case
    have hgde : NormPairSqrtTwoGDE (OmegaIntCoord.P x) (OmegaIntCoord.Q x) 0 :=
      ⟨normPairSqrtTwoPowDivides_zero _ _, fun h =>
        hPxEven ((normPairSqrtTwoPowDivides_one_iff _ _).mp h)⟩
    have hlevel : DenNormSDE z = 2 * r - 0 :=
      denNormSDE_eq_two_r_sub_j_of_normPairGDE hz hzDyadic hgde (by omega)
    rcases normalized_state_residue_compat_of_common_denominator hz hy hState hr3
      with ⟨hP, hQ⟩
    have hP_val : ((OmegaIntCoord.P x : ZMod 8)).val % 2 = 1 :=
      zmod8_val_odd_of_odd_int _ hPxEven
    have hNormZ : OmegaResidue.normGDEEq 0 (OmegaResidue.ofIntCoord x) = true := by
      rw [OmegaResidue.normGDEEq, OmegaResidue.P_ofIntCoord,
        OmegaResidue.Q_ofIntCoord]
      have hclassify :
          ∀ A B : ZMod 8, A.val % 2 = 1 →
            OmegaResidue.sqrtTwoGDEEqPair 0 A B = true := by decide
      exact hclassify _ _ hP_val
    have hNormW : OmegaResidue.normGDEEq 0 (OmegaResidue.ofIntCoord y) = true :=
      OmegaResidue.normGDEEq_of_neg_norm_pair hNormZ hP hQ
    exact ⟨y, hy, hr, hw_le_r, 0, Or.inl rfl, hlevel, hNormZ, hNormW, hP, hQ⟩

private structure KMMSDEGDEBridgeData (z w : ℂ) where
  r : ℕ
  j : ℕ
  x : OmegaIntCoord
  y : OmegaIntCoord
  hj : j = 0 ∨ j = 1
  hlevel : DenNormSDE z = 2 * r - j
  hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r
  hw : w = OmegaIntCoord.val y / sqrtTwoComplex ^ r
  hcompat :
    OmegaResidue.compatiblePair j
      (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y) = true

private def kmm_sde_gde_bridge_data_of_paper_coordinates
    {z w : ℂ}
    {r j : ℕ} {x y : OmegaIntCoord}
    (hj : j = 0 ∨ j = 1)
    (hlevel : DenNormSDE z = 2 * r - j)
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hw : w = OmegaIntCoord.val y / sqrtTwoComplex ^ r)
    (hNormZ :
      OmegaResidue.normGDEEq j (OmegaResidue.ofIntCoord x) = true)
    (hNormW :
      OmegaResidue.normGDEEq j (OmegaResidue.ofIntCoord y) = true)
    (hP :
      OmegaResidue.P (OmegaResidue.ofIntCoord x) +
        OmegaResidue.P (OmegaResidue.ofIntCoord y) = 0)
    (hQ :
      OmegaResidue.Q (OmegaResidue.ofIntCoord x) +
        OmegaResidue.Q (OmegaResidue.ofIntCoord y) = 0) :
    KMMSDEGDEBridgeData z w := by
  refine ⟨r, j, x, y, hj, hlevel, hz, hw, ?_⟩
  simp [OmegaResidue.compatiblePair, hNormZ, hNormW, hP, hQ]

private def kmm_sde_gde_bridge_data_of_common_minimal_facts
    {z w : ℂ} {r : ℕ} {x y : OmegaIntCoord}
    (hz : z = OmegaIntCoord.val x / sqrtTwoComplex ^ r)
    (hw : w = OmegaIntCoord.val y / sqrtTwoComplex ^ r)
    (hfacts : KMMStateSDEGDEFacts z w r x y) :
    KMMSDEGDEBridgeData z w := by
  rcases hfacts with ⟨_hzMin, _hwMin, j, hj, hlevel, hNormZ, hNormW, hP, hQ⟩
  exact kmm_sde_gde_bridge_data_of_paper_coordinates
    hj hlevel hz hw hNormZ hNormW hP hQ

private noncomputable def kmm_sde_gde_bridge_data_of_legacy_coordinates
    {z w : ℂ}
    {nz nw : ℕ}
    {a b c d e f g h : ℤ}
    (hz : z = cyclotomicIntegerCoord a b c d / sqrtTwoComplex ^ nz)
    (hw : w = cyclotomicIntegerCoord e f g h / sqrtTwoComplex ^ nw)
    (hState : IsUnitState z w)
    (hLarge : 5 ≤ DenNormSDE z) :
    KMMSDEGDEBridgeData z w := by
  let x := Classical.choose (omegaSDE_presentation_of_legacy_coordinate hz)
  have hx : z = OmegaIntCoord.val x / sqrtTwoComplex ^ omegaSDE z :=
    Classical.choose_spec (omegaSDE_presentation_of_legacy_coordinate hz)
  rcases kmm_state_sde_gde_facts_from_minimal_z
      (z := z) (w := w) (nw := nw) (e := e) (f := f) (g := g) (h := h)
      (r := omegaSDE z) (x := x) hx rfl hw hState hLarge with
    ⟨y, hy, hfacts⟩
  exact kmm_sde_gde_bridge_data_of_common_minimal_facts hx hy hfacts

private theorem kmm_choose_k_for_norm_descent_from_sde_gde_bridge
    {z w : ℂ}
    (D : KMMSDEGDEBridgeData z w)
    (hLarge : 5 ≤ DenNormSDE z) :
    ∃ k : Fin 4,
      HasDenominatorExponent
        (star ((applyHTPowToState k z w).1) *
          ((applyHTPowToState k z w).1))
        (DenNormSDE z - 1) := by
  rcases D with ⟨r, j, x, y, hj, hlevel, hz, hw, hcompat⟩
  have hd : (3 : ℕ) ∈ ([1, 2, 3] : List ℕ) := by simp
  rcases kmm_four_choice_parity (j := j) (d := 3) hj hcompat hd with ⟨k, hres⟩
  have hn : 3 ≤ 3 + j := by omega
  have hn4 : 3 + j ≤ 4 := by
    rcases hj with rfl | rfl <;> omega
  have hnlevel : 3 + j ≤ 2 * r + 2 := by
    rcases hj with rfl | rfl <;> omega
  have htarget : DenNormSDE z - 1 = 2 * r + 2 - (3 + j) := by
    rcases hj with rfl | rfl <;> omega
  have hcandidate :
      HasDenominatorExponent
        ((star z * z +
            star z * (rsOmegaAlg ^ (k : ℕ) * w) +
            star (rsOmegaAlg ^ (k : ℕ) * w) * z +
            star (rsOmegaAlg ^ (k : ℕ) * w) *
              (rsOmegaAlg ^ (k : ℕ) * w)) / 2)
        (DenNormSDE z - 1) :=
    hasDenominatorExponent_of_common_omega_choice_ge_three
      hn hn4 hnlevel k x y hz hw htarget hres
  refine ⟨k, ?_⟩
  rw [applyHTPowToState_norm_formula]
  exact hcandidate

/-- Paper-shaped coordinate descent: convert legacy entry witnesses only far
enough to obtain the KMM minimal-denominator/gde bridge, then use the residue
check with `d = 3` to lower the norm denominator by one. -/
theorem kmm_choose_k_coordinate_descent
    {z w : ℂ}
    {nz nw : ℕ}
    {a b c d e f g h : ℤ}
    (hz : z = cyclotomicIntegerCoord a b c d / sqrtTwoComplex ^ nz)
    (hw : w = cyclotomicIntegerCoord e f g h / sqrtTwoComplex ^ nw)
    (hState : IsUnitState z w)
    (hLarge : 5 ≤ DenNormSDE z) :
    ∃ k : Fin 4,
      HasDenominatorExponent
        (star ((applyHTPowToState k z w).1) *
          ((applyHTPowToState k z w).1))
        (DenNormSDE z - 1) := by
  exact kmm_choose_k_for_norm_descent_from_sde_gde_bridge
    (kmm_sde_gde_bridge_data_of_legacy_coordinates hz hw hState hLarge)
    hLarge

/-- Coordinate descent lifted from dyadic-state membership. -/
theorem kmm_choose_k_coordinate_descent_of_entries
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w)
    (hLarge : 5 ≤ DenNormSDE z) :
    ∃ k : Fin 4,
      HasDenominatorExponent
        (star ((applyHTPowToState k z w).1) *
          ((applyHTPowToState k z w).1))
        (DenNormSDE z - 1) := by
  rcases hEntries with ⟨hz, hw⟩
  rcases hz with ⟨nz, a, b, c, d, hz⟩
  rcases hw with ⟨nw, e, f, g, h, hw⟩
  exact kmm_choose_k_coordinate_descent
    (z := z) (w := w) (nz := nz) (nw := nw)
    (a := a) (b := b) (c := c) (d := d)
    (e := e) (f := f) (g := g) (h := h)
    (by simpa [cyclotomicIntegerCoord] using hz)
    (by simpa [cyclotomicIntegerCoord] using hw)
    hState hLarge

/-- KMM denominator-exponent descent for the transformed first-coordinate
norm, factored through the coordinate congruence lemma. -/
theorem kmm_choose_k_for_norm_descent
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w)
    (hLarge : 5 ≤ DenNormSDE z) :
    ∃ k : Fin 4,
      HasDenominatorExponent
        (star ((applyHTPowToState k z w).1) *
          ((applyHTPowToState k z w).1))
        (DenNormSDE z - 1) := by
  exact kmm_choose_k_coordinate_descent_of_entries hEntries hState hLarge

/-- Arithmetic core of the KMM denominator-descent step.

This isolates the only hard part of the induction engine: for a normalized
dyadic-cyclotomic state with sufficiently large denominator norm, one of the
four transforms `H T^k` strictly lowers `DenNormSDE` on the tracked entry. -/
theorem kmm_norm_denominator_reduction_arithmetic
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w)
    (hLarge : 5 ≤ DenNormSDE z) :
    ∃ k : Fin 4,
      DenNormSDE ((applyHTPowToState k z w).1) < DenNormSDE z := by
  rcases kmm_choose_k_for_norm_descent hEntries hState hLarge with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hsde := sde_le_of_hasDenominatorExponent hk
  change sde
      (star ((applyHTPowToState k z w).1) *
        ((applyHTPowToState k z w).1)) < DenNormSDE z
  omega

/-- KMM denominator descent: when the denominator norm is large, one of
`H T^k`, `k ∈ {0,1,2,3}`, preserves the state invariants and strictly lowers
the tracked denominator norm.  The arithmetic congruence proof is isolated
behind this statement. -/
theorem kmm_exists_reducing_k
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w)
    (hLarge : 5 ≤ DenNormSDE z) :
    ∃ k : Fin 4,
      let z' := (applyHTPowToState k z w).1
      let w' := (applyHTPowToState k z w).2
      StateEntriesInDyadicCyclotomic z' w' ∧
      IsUnitState z' w' ∧
      DenNormSDE z' < DenNormSDE z := by
  rcases kmm_norm_denominator_reduction_arithmetic hEntries hState hLarge with
    ⟨k, hk⟩
  refine ⟨k, ?_⟩
  dsimp
  refine ⟨applyHTPowToState_entries hEntries k, applyHTPowToState_unit hState k, hk⟩

/-- An omega-denominator level of 3 or more forces `DenNormSDE z ≥ 5`.
The contrapositive gives the upper bound `omegaSDE z ≤ 2` needed for the
low-denominator base table. -/
private theorem omegaSDE_le_two_of_denNormSDE_le_four
    {z : ℂ}
    (hz : InDyadicCyclotomic z)
    (hLow : DenNormSDE z ≤ 4) :
    omegaSDE z ≤ 2 := by
  by_contra h
  push_neg at h
  have hr3 : 3 ≤ omegaSDE z := h
  -- Get InOmegaDyadicCyclotomic z from the legacy presentation
  have hzO : InOmegaDyadicCyclotomic z := by
    rcases hz with ⟨n, a, b, c, d, hzleg⟩
    exact ⟨n, hasOmegaDenominatorExponent_of_hasDenominatorExponent
      ⟨a, b, c, d, by simpa [cyclotomicIntegerCoord] using hzleg⟩⟩
  -- Get minimal omega presentation at level r = omegaSDE z
  rcases hasOmegaDenominatorExponent_of_inOmegaDyadicCyclotomic hzO with ⟨x, hxpres⟩
  -- hxpres : z = val(x) / √2^(omegaSDE z)
  -- x is not √2-divisible at the minimal level
  have hpos : 0 < omegaSDE z := by omega
  have hxNotDvd := OmegaIntCoord.sqrtTwoGDE_zero_not_sqrtTwo_dvd
    (sqrtTwoGDE_zero_of_minimal_omega_denominator_pos hxpres rfl hpos)
  have h_not_dvd2 := not_normPairSqrtTwoPowDivides_two_of_not_sqrtTwo_dvd x hxNotDvd
  -- Lower bound on DenNormSDE z: ≥ 2 * omegaSDE z - j ≥ 5
  by_cases hPxEven : Even (OmegaIntCoord.P x)
  · -- j = 1 case: DenNormSDE z ≥ 2 * omegaSDE z - 1 ≥ 5
    have hgde : NormPairSqrtTwoGDE (OmegaIntCoord.P x) (OmegaIntCoord.Q x) 1 :=
      ⟨(normPairSqrtTwoPowDivides_one_iff _ _).mpr hPxEven, h_not_dvd2⟩
    have hlb := sde_starzz_ge_of_normPairGDE hxpres hz hgde
    unfold DenNormSDE at hLow
    omega
  · -- j = 0 case: DenNormSDE z ≥ 2 * omegaSDE z ≥ 6
    have hgde : NormPairSqrtTwoGDE (OmegaIntCoord.P x) (OmegaIntCoord.Q x) 0 :=
      ⟨normPairSqrtTwoPowDivides_zero _ _, fun h =>
        hPxEven ((normPairSqrtTwoPowDivides_one_iff _ _).mp h)⟩
    have hlb := sde_starzz_ge_of_normPairGDE hxpres hz hgde
    unfold DenNormSDE at hLow
    omega

/-- At `omegaSDE z = 1` with a minimal presentation where `P x = 2`, no valid
unit state exists in `D[ω] × D[ω]`.  The norm equation forces
`|w|² = −Qx·√2/2`, which combined with the unit-state identity over a common
omega level forces `P(yw) = 0`, hence `w = 0`, giving `Qx = 0` — contradicting
the odd-parity guarantee from the minimality check. -/
private theorem unit_state_omegaSDE_one_P_two_impossible
    {z w : ℂ} {x : OmegaIntCoord}
    (hzpres : z = OmegaIntCoord.val x / sqrtTwoComplex ^ 1)
    (hr : omegaSDE z = 1)
    (hP2 : OmegaIntCoord.P x = 2)
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w) :
    False := by
  -- Minimality: x is not √2-divisible at level r = 1
  have hxNotDvd := OmegaIntCoord.sqrtTwoGDE_zero_not_sqrtTwo_dvd
    (sqrtTwoGDE_zero_of_minimal_omega_denominator_pos hzpres hr Nat.one_pos)
  have h_not_dvd2 := not_normPairSqrtTwoPowDivides_two_of_not_sqrtTwo_dvd x hxNotDvd
  -- P x = 2 is even ⟹ Q x is odd
  have hPxEven : Even (OmegaIntCoord.P x) := ⟨1, by omega⟩
  have hQxOdd : ¬ Even (OmegaIntCoord.Q x) :=
    fun hQ => h_not_dvd2 ((normPairSqrtTwoPowDivides_two_iff _ _).mpr ⟨hPxEven, hQ⟩)
  -- Get omega presentation of w at its minimal level s = omegaSDE w
  have hwO : InOmegaDyadicCyclotomic w := by
    rcases hEntries.2 with ⟨nw, ew, fw, gw, hw, hwleg⟩
    exact ⟨nw, hasOmegaDenominatorExponent_of_hasDenominatorExponent
      ⟨ew, fw, gw, hw, by simpa [cyclotomicIntegerCoord] using hwleg⟩⟩
  rcases hasOmegaDenominatorExponent_of_inOmegaDyadicCyclotomic hwO with ⟨yw, hwpres⟩
  set s := omegaSDE w
  -- Lift z from level 1 to (1+s), lift w from level s to (s+1)
  have hz_lifted := lift_omega_pres_up (d := s) hzpres
  have hw_lifted := lift_omega_pres_up (d := 1) hwpres
  rw [show s + 1 = 1 + s from by ring] at hw_lifted
  -- Common-level integer identity at R = 1 + s
  rcases unit_state_integer_facts_at_common_level hz_lifted hw_lifted hState with ⟨hPsum, _⟩
  -- 2^s * P x + 2 * P yw = 2^(1+s) → P yw = 0
  have hPyw0 : OmegaIntCoord.P yw = 0 := by
    have hPs : OmegaIntCoord.P (OmegaIntCoord.sqrtTwoPowMul s x) = 2 ^ s * 2 :=
      ((PQ_sqrtTwoPowMul s x).1).trans (by rw [hP2])
    have hP1' : OmegaIntCoord.P (OmegaIntCoord.sqrtTwoPowMul 1 yw) = 2 * OmegaIntCoord.P yw :=
      ((PQ_sqrtTwoPowMul 1 yw).1).trans (by ring)
    have hge0 := omegaIntCoord_P_nonneg yw
    linarith [hPsum, show (2:ℤ)^(1+s) = 2^s * 2 from by ring]
  -- P yw = 0 → yw = 0 → w = 0
  have hyw_zero : yw = ⟨0, 0, 0, 0⟩ := by
    cases yw with
    | mk a b c d =>
      simp only [OmegaIntCoord.P] at hPyw0
      have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
      have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
      have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
      have hd : d = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
      subst ha; subst hb; subst hc; subst hd; rfl
  have hw0 : w = 0 := by rw [hwpres, hyw_zero]; simp [OmegaIntCoord.val]
  -- IsUnitState z 0 → star z * z = 1
  have hzUnit : star z * z = 1 := by
    have := hState; unfold IsUnitState at this
    rw [hw0, star_zero, mul_zero, add_zero] at this; exact this
  -- Norm formula: (2 + Q x * √2) / 2 = 1 → Q x = 0 → contradiction with Q x odd
  have hz_norm := omega_norm_div_common_denominator hzpres
  rw [hzUnit] at hz_norm
  have hsimp2 : sqrtTwoComplex ^ (2 * 1) = 2 := by norm_num [sqrtTwoComplex_sq]
  rw [hsimp2] at hz_norm
  -- hz_norm : 1 = ((P x : ℂ) + (Q x : ℂ) * sqrtTwoComplex) / 2
  have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
  rw [show (OmegaIntCoord.P x : ℂ) = 2 from by exact_mod_cast hP2] at hz_norm
  -- hz_norm : 1 = (2 + Q x * √2) / 2
  have hQeq : (OmegaIntCoord.Q x : ℂ) * sqrtTwoComplex = 0 := by
    rw [eq_div_iff h2ne] at hz_norm
    linear_combination -hz_norm
  have hQx0 : OmegaIntCoord.Q x = 0 := by
    rcases mul_eq_zero.mp hQeq with h | h
    · exact_mod_cast h
    · exact absurd h sqrtTwoComplex_ne_zero
  exact hQxOdd ⟨0, by omega⟩

/-- When `z = val(x)/√2²` is at the minimal omega level 2, every companion `w`
in a unit state with `w ∈ D[ω]` satisfies `omegaSDE w ≤ 2`.

Proof: if `omegaSDE w ≥ 3` (say `= s`), then at the common level `s` the
unit-state equation gives `P y_min = 2^(s-2)·(4 - P x)` and
`Q y_min = -2^(s-2)·Q x`.  Both are divisible by `2^(s-2) ≥ 2`, making
`val(y_min)` divisible by `√2`, contradicting the minimality of `y_min`. -/
private theorem omegaSDE_w_le_two_of_denNormSDE_z_le_four
    {z w : ℂ} {x : OmegaIntCoord}
    (hzpres : z = OmegaIntCoord.val x / sqrtTwoComplex ^ 2)
    (hzMin : omegaSDE z = 2)
    (hwO : InOmegaDyadicCyclotomic w)
    (hState : IsUnitState z w) :
    omegaSDE w ≤ 2 := by
  by_contra h
  push_neg at h
  -- s := omegaSDE w ≥ 3
  rcases hasOmegaDenominatorExponent_of_inOmegaDyadicCyclotomic hwO with ⟨y_min, hy_min⟩
  set s := omegaSDE w with hs_def
  -- after `set`, hy_min : w = val(y_min) / √2^s
  have hs3 : 3 ≤ s := by omega
  have hpos_s : 0 < s := by omega
  -- y_min is not √2-divisible (minimality of s)
  have hy_NotDvd :
      ¬ ∃ q : OmegaIntCoord,
        OmegaIntCoord.val y_min = sqrtTwoComplex * OmegaIntCoord.val q :=
    OmegaIntCoord.sqrtTwoGDE_zero_not_sqrtTwo_dvd
      (sqrtTwoGDE_zero_of_minimal_omega_denominator_pos hy_min hs_def.symm hpos_s)
  -- Lift z from level 2 to level s
  have hz_s : z = OmegaIntCoord.val (OmegaIntCoord.sqrtTwoPowMul (s - 2) x) /
      sqrtTwoComplex ^ s := by
    have := lift_omega_pres_up (d := s - 2) hzpres
    rwa [show 2 + (s - 2) = s from by omega] at this
  -- Integer identity at level s
  rcases unit_state_integer_facts_at_common_level hz_s hy_min hState with ⟨hPsum, hQsum⟩
  rcases PQ_sqrtTwoPowMul (s - 2) x with ⟨hPs, hQs⟩
  -- P y_min is even: P y_min = 2^s - 2^(s-2)·P x = 2^(s-2)·(4-P x), div by 2^(s-2) ≥ 2
  have hd_pos : 1 ≤ s - 2 := by omega
  have hPy_even : Even (OmegaIntCoord.P y_min) := by
    have hsum : OmegaIntCoord.P y_min + (2 : ℤ) ^ (s - 2) * OmegaIntCoord.P x =
        (2 : ℤ) ^ s := by
      have := hPsum; rw [hPs] at this; linarith
    exact even_of_int_eq_two_pow_minus_two_pow_mul hd_pos (by omega) hsum
  -- Q y_min is even: Q y_min = -2^(s-2)·Q x, div by 2^(s-2) ≥ 2
  have hQy_even : Even (OmegaIntCoord.Q y_min) := by
    have hsum : OmegaIntCoord.Q y_min + (2 : ℤ) ^ (s - 2) * OmegaIntCoord.Q x = 0 := by
      have := hQsum; rw [hQs] at this; linarith
    exact even_of_int_eq_neg_two_pow_mul hd_pos hsum
  -- Contradiction: val(y_min) is √2-divisible, but y_min is minimal
  exact hy_NotDvd
    (OmegaIntCoord.val_dvd_sqrtTwo_of_norm_pair_even y_min hPy_even hQy_even)

/-- The Ross-Selinger circuit word for `(H T^k)⁻¹ = T^(8-k) H`, for
`k ∈ {0,1,2,3}`.  Since circuit evaluation is by fold-right multiplication,
the list `[.t, ..., .t, .h]` evaluates as `T^m H`. -/
def inverseHTWord (k : Fin 4) : CliffordTCircuit :=
  match k.val with
  | 0 => [.h]
  | 1 => [.t, .t, .t, .t, .t, .t, .t, .h]
  | 2 => [.t, .t, .t, .t, .t, .t, .h]
  | 3 => [.t, .t, .t, .t, .t, .h]
  | _ => []

/-- T-count-optimized Ross-Selinger word for `(H T^k)⁻¹ = T^(8-k) H`.

This uses `S = T²`, so the inverse powers are represented as
`T⁷ = S³T`, `T⁶ = S³`, and `T⁵ = S²T`.  The matrix is the same as
`inverseHTWord`, but the `T`-count is at most one. -/
def optimizedInverseHTWord (k : Fin 4) : CliffordTCircuit :=
  match k.val with
  | 0 => [.h]
  | 1 => [.s, .s, .s, .t, .h]
  | 2 => [.s, .s, .s, .h]
  | 3 => [.s, .s, .t, .h]
  | _ => []

theorem TCount_optimizedInverseHTWord_le_one (k : Fin 4) :
    TCount (optimizedInverseHTWord k) ≤ 1 := by
  fin_cases k <;> decide

/-- Prepend the inverse `HT^k` step to a state-preparation circuit. -/
def prependInverseHT (k : Fin 4) (C : CliffordTCircuit) : CliffordTCircuit :=
  inverseHTWord k ++ C

/-- T-count-optimized version of `prependInverseHT`. -/
def prependOptimizedInverseHT (k : Fin 4) (C : CliffordTCircuit) : CliffordTCircuit :=
  optimizedInverseHTWord k ++ C

theorem eval_prependInverseHT
    (k : Fin 4) (C : CliffordTCircuit) :
    CliffordTCircuit.eval (prependInverseHT k C)
      =
    CliffordTCircuit.eval (inverseHTWord k) *
      CliffordTCircuit.eval C := by
  simp [prependInverseHT, CliffordTCircuit.eval_append]

theorem TCount_prependOptimizedInverseHT_le
    (k : Fin 4) (C : CliffordTCircuit) :
    TCount (prependOptimizedInverseHT k C) ≤ TCount C + 1 := by
  rw [prependOptimizedInverseHT, TCount_append]
  have h := TCount_optimizedInverseHTWord_le_one k
  omega

private lemma phaseT_scalar_eq_rsOmegaAlg :
    Complex.exp (Complex.I * (Real.pi / 4)) = rsOmegaAlg := by
  rw [show Complex.I * (Real.pi / 4) = ((Real.pi / 4 : ℂ) * Complex.I) by ring,
    Complex.exp_mul_I]
  have hcast : (Real.pi / 4 : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) := by norm_num
  have hcos : Complex.cos (Real.pi / 4 : ℂ) = (((Real.sqrt 2) / 2 : ℝ) : ℂ) := by
    rw [hcast, ← Complex.ofReal_cos, Real.cos_pi_div_four]
  have hsin : Complex.sin (Real.pi / 4 : ℂ) = (((Real.sqrt 2) / 2 : ℝ) : ℂ) := by
    rw [hcast, ← Complex.ofReal_sin, Real.sin_pi_div_four]
  rw [hcos, hsin]
  rw [rsOmegaAlg]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (Real.sqrt 2 : ℝ) ≠ 0 by positivity)
  have hI : (1 + Complex.I : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  simp [sqrtTwoComplex]
  field_simp [hs, hI]
  norm_num [sq, ← Complex.ofReal_mul, Real.sq_sqrt]

private lemma rsOmegaAlg_mul_self :
    rsOmegaAlg * rsOmegaAlg = Complex.I := by
  have hs : sqrtTwoComplex ≠ 0 := sqrtTwoComplex_ne_zero
  simp [rsOmegaAlg]
  field_simp [hs]
  ring_nf
  simp [sqrtTwoComplex_sq, Complex.I_sq]

private lemma rsOmegaAlg_pow_four :
    rsOmegaAlg ^ 4 = (-1 : ℂ) := by
  calc
    rsOmegaAlg ^ 4 = (rsOmegaAlg * rsOmegaAlg) * (rsOmegaAlg * rsOmegaAlg) := by ring
    _ = Complex.I * Complex.I := by rw [rsOmegaAlg_mul_self]
    _ = (-1 : ℂ) := by simp [Complex.I_mul_I]

private lemma rsOmegaAlg_pow_eight :
    rsOmegaAlg ^ 8 = (1 : ℂ) := by
  calc
    rsOmegaAlg ^ 8 = (rsOmegaAlg ^ 4) * (rsOmegaAlg ^ 4) := by ring
    _ = (1 : ℂ) := by simp [rsOmegaAlg_pow_four]

private lemma rsOmegaAlg_pow_eq_of_mod_eq {m n : ℕ}
    (h : m % 8 = n % 8) :
    rsOmegaAlg ^ m = rsOmegaAlg ^ n := by
  calc
    rsOmegaAlg ^ m
        = rsOmegaAlg ^ (m % 8 + 8 * (m / 8)) := by
            rw [Nat.mod_add_div]
    _ = rsOmegaAlg ^ (m % 8) * (rsOmegaAlg ^ 8) ^ (m / 8) := by
            rw [pow_add, pow_mul]
    _ = rsOmegaAlg ^ (m % 8) := by
            rw [rsOmegaAlg_pow_eight]
            simp
    _ = rsOmegaAlg ^ (n % 8) := by rw [h]
    _ = rsOmegaAlg ^ (n % 8) * (rsOmegaAlg ^ 8) ^ (n / 8) := by
            rw [rsOmegaAlg_pow_eight]
            simp
    _ = rsOmegaAlg ^ (n % 8 + 8 * (n / 8)) := by
            rw [pow_add, pow_mul]
    _ = rsOmegaAlg ^ n := by
            rw [Nat.mod_add_div]

private lemma rsOmegaAlg_pow_add_compl
    (a b : ℕ) (h : a + b = 8) :
    rsOmegaAlg ^ a * rsOmegaAlg ^ b = (1 : ℂ) := by
  rw [← pow_add, h, rsOmegaAlg_pow_eight]

private lemma hadamard2_stateColumn (a b : ℂ) :
    hadamard2 * stateColumn a b =
      stateColumn ((a + b) / sqrtTwoComplex) ((a - b) / sqrtTwoComplex) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stateColumn, hadamard2, Matrix.mul_apply, Fin.sum_univ_two, sqrtTwoComplex]
  all_goals ring

private lemma phaseT_stateColumn (a b : ℂ) :
    phaseT * stateColumn a b =
      stateColumn a (rsOmegaAlg * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stateColumn, phaseT, diag2, Matrix.mul_apply, Fin.sum_univ_two,
      phaseT_scalar_eq_rsOmegaAlg]

private lemma phaseS_stateColumn (a b : ℂ) :
    phaseS * stateColumn a b =
      stateColumn a (Complex.I * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stateColumn, phaseS, diag2, Matrix.mul_apply, Fin.sum_univ_two]

private lemma eval_replicate_t_stateColumn (n : ℕ) (a b : ℂ) :
    CliffordTCircuit.eval (List.replicate n RossSelingerPrimitive.t) *
      stateColumn a b =
    stateColumn a (rsOmegaAlg ^ n * b) := by
  induction n with
  | zero =>
      simp [CliffordTCircuit.eval]
  | succ n ih =>
      calc
        CliffordTCircuit.eval (List.replicate (n + 1) RossSelingerPrimitive.t) *
            stateColumn a b
            = phaseT *
              (CliffordTCircuit.eval (List.replicate n RossSelingerPrimitive.t) *
                stateColumn a b) := by
                rw [List.replicate_succ]
                simp only [CliffordTCircuit.eval_cons, RossSelingerPrimitive.eval]
                rw [Matrix.mul_assoc]
        _ = phaseT * stateColumn a (rsOmegaAlg ^ n * b) := by rw [ih]
        _ = stateColumn a (rsOmegaAlg ^ (n + 1) * b) := by
            rw [phaseT_stateColumn]
            simp [pow_succ', mul_assoc]

private lemma eval_replicate_t_matrix (n : ℕ) :
    CliffordTCircuit.eval (List.replicate n RossSelingerPrimitive.t) =
      Matrix.of ![![(1 : ℂ), 0], ![0, rsOmegaAlg ^ n]] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [CliffordTCircuit.eval]
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [CliffordTCircuit.eval_cons, RossSelingerPrimitive.eval]
      rw [ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [phaseT, diag2, Matrix.mul_apply, Fin.sum_univ_two,
          phaseT_scalar_eq_rsOmegaAlg, pow_succ']

/-! ### Step 2a: X gate identity via Clifford+T

`X = H · Z · H = H · S² · H`, so this word is Clifford-only in the
Ross-Selinger gate alphabet.  We expose this via its action on `|0⟩`:
`X · |0⟩ = |1⟩`. -/

/-- The Clifford+T word for the `X` (NOT) gate. -/
def cliffordT_X_word : CliffordTCircuit := [.h, .s, .s, .h]

theorem TCount_cliffordT_X_word :
    TCount cliffordT_X_word = 0 := by
  rfl

private lemma ket0Column_eq_stateColumn :
    ket0Column = stateColumn 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ket0Column, stateColumn]

/-- `H · S² · H · |0⟩ = |1⟩` — the Clifford+T `X` gate identity at `|0⟩`. -/
theorem cliffordT_X_word_eval_ket0 :
    CliffordTCircuit.eval cliffordT_X_word * ket0Column = stateColumn 0 1 := by
  rw [ket0Column_eq_stateColumn]
  simp only [cliffordT_X_word, CliffordTCircuit.eval_cons, RossSelingerPrimitive.eval,
    CliffordTCircuit.eval_nil]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [Matrix.mul_one]
  rw [hadamard2_stateColumn]
  rw [show ((1 : ℂ) + 0) / sqrtTwoComplex = 1 / sqrtTwoComplex by ring,
      show ((1 : ℂ) - 0) / sqrtTwoComplex = 1 / sqrtTwoComplex by ring]
  rw [phaseS_stateColumn, phaseS_stateColumn]
  rw [hadamard2_stateColumn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stateColumn]
  all_goals
    first | left | skip
    field_simp [sqrtTwoComplex_ne_zero]
    simp [Complex.I_sq, sqrtTwoComplex_sq]
    try norm_num

/-! ### Step 2a (cont.): ω^k circuit infrastructure -/

/-- `eval [.omega]^k * stateColumn a b = stateColumn (ω^k a) (ω^k b)`. -/
theorem eval_replicate_omega_stateColumn (n : ℕ) (a b : ℂ) :
    CliffordTCircuit.eval (List.replicate n RossSelingerPrimitive.omega) *
      stateColumn a b =
    stateColumn (rsOmegaAlg ^ n * a) (rsOmegaAlg ^ n * b) := by
  induction n with
  | zero => simp [CliffordTCircuit.eval, ket0Column_eq_stateColumn]
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [CliffordTCircuit.eval_cons]
    rw [Matrix.mul_assoc, ih]
    -- Now apply ω · I to stateColumn.
    have : RossSelingerPrimitive.eval RossSelingerPrimitive.omega =
        Complex.exp (Complex.I * (Real.pi / 4)) • (1 : Square 2) := rfl
    rw [this, phaseT_scalar_eq_rsOmegaAlg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [stateColumn, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
        pow_succ]
    all_goals ring

/-- Circuit witness for ω^k |0⟩: just k copies of the omega scalar. -/
theorem cliffordT_circuit_omegaPow_zero (m : ℕ) :
    CliffordTCircuit.eval (List.replicate m RossSelingerPrimitive.omega) *
      ket0Column = stateColumn (rsOmegaAlg ^ m) 0 := by
  rw [ket0Column_eq_stateColumn, eval_replicate_omega_stateColumn]
  simp

/-- Circuit witness for ω^k |1⟩: `X` followed by scalar `ω^k`. -/
theorem cliffordT_circuit_zero_omegaPow (k : ℕ) :
    CliffordTCircuit.eval
        (List.replicate k RossSelingerPrimitive.omega ++ cliffordT_X_word) *
      ket0Column = stateColumn 0 (rsOmegaAlg ^ k) := by
  rw [CliffordTCircuit.eval_append, Matrix.mul_assoc,
    cliffordT_X_word_eval_ket0, eval_replicate_omega_stateColumn]
  simp

private lemma hadamard2_apply_applyHTPowToState
    (k : Fin 4) (z w : ℂ) :
    hadamard2 *
      stateColumn
        (applyHTPowToState k z w).1
        (applyHTPowToState k z w).2 =
    stateColumn z (rsOmegaAlg ^ (k : ℕ) * w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stateColumn, applyHTPowToState, hadamard2, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    field_simp [sqrtTwoComplex_ne_zero]
    rw [sqrtTwoComplex]
    ring_nf
    rw [show ((↑(Real.sqrt 2) : ℂ) ^ 2) = (2 : ℂ) by
      norm_num [sq, ← Complex.ofReal_mul, Real.sq_sqrt]]

theorem inverseHT_apply_applyHTPowToState
    (k : Fin 4) (z w : ℂ) :
    CliffordTCircuit.eval (inverseHTWord k) *
      stateColumn
        (applyHTPowToState k z w).1
        (applyHTPowToState k z w).2
      =
    stateColumn z w := by
  fin_cases k
  · simpa [inverseHTWord, CliffordTCircuit.eval, RossSelingerPrimitive.eval]
      using hadamard2_apply_applyHTPowToState (0 : Fin 4) z w
  · calc
      CliffordTCircuit.eval (inverseHTWord 1) *
          stateColumn
            (applyHTPowToState 1 z w).1
            (applyHTPowToState 1 z w).2
          = CliffordTCircuit.eval (List.replicate 7 RossSelingerPrimitive.t) *
              (hadamard2 *
                stateColumn
                  (applyHTPowToState 1 z w).1
                  (applyHTPowToState 1 z w).2) := by
              simp [inverseHTWord, CliffordTCircuit.eval_append, CliffordTCircuit.eval,
                RossSelingerPrimitive.eval, Matrix.mul_assoc]
      _ = CliffordTCircuit.eval (List.replicate 7 RossSelingerPrimitive.t) *
              stateColumn z (rsOmegaAlg ^ (1 : ℕ) * w) := by
              rw [hadamard2_apply_applyHTPowToState]
              norm_num
      _ = stateColumn z (rsOmegaAlg ^ 7 * (rsOmegaAlg ^ (1 : ℕ) * w)) := by
              rw [eval_replicate_t_stateColumn]
      _ = stateColumn z w := by
              have hpow : rsOmegaAlg ^ 7 * rsOmegaAlg ^ (1 : ℕ) = (1 : ℂ) :=
                rsOmegaAlg_pow_add_compl 7 1 (by norm_num)
              simpa [pow_one, mul_assoc] using
                congrArg (fun q : ℂ => stateColumn z (q * w)) hpow
  · calc
      CliffordTCircuit.eval (inverseHTWord 2) *
          stateColumn
            (applyHTPowToState 2 z w).1
            (applyHTPowToState 2 z w).2
          = CliffordTCircuit.eval (List.replicate 6 RossSelingerPrimitive.t) *
              (hadamard2 *
                stateColumn
                  (applyHTPowToState 2 z w).1
                  (applyHTPowToState 2 z w).2) := by
              simp [inverseHTWord, CliffordTCircuit.eval_append, CliffordTCircuit.eval,
                RossSelingerPrimitive.eval, Matrix.mul_assoc]
      _ = CliffordTCircuit.eval (List.replicate 6 RossSelingerPrimitive.t) *
              stateColumn z (rsOmegaAlg ^ (2 : ℕ) * w) := by
              rw [hadamard2_apply_applyHTPowToState]
              norm_num
      _ = stateColumn z (rsOmegaAlg ^ 6 * (rsOmegaAlg ^ (2 : ℕ) * w)) := by
              rw [eval_replicate_t_stateColumn]
      _ = stateColumn z w := by
              have hpow : rsOmegaAlg ^ 6 * rsOmegaAlg ^ (2 : ℕ) = (1 : ℂ) :=
                rsOmegaAlg_pow_add_compl 6 2 (by norm_num)
              simpa [mul_assoc] using
                congrArg (fun q : ℂ => stateColumn z (q * w)) hpow

  · calc
      CliffordTCircuit.eval (inverseHTWord 3) *
          stateColumn
            (applyHTPowToState 3 z w).1
            (applyHTPowToState 3 z w).2
          = CliffordTCircuit.eval (List.replicate 5 RossSelingerPrimitive.t) *
              (hadamard2 *
                stateColumn
                  (applyHTPowToState 3 z w).1
                  (applyHTPowToState 3 z w).2) := by
              simp [inverseHTWord, CliffordTCircuit.eval_append, CliffordTCircuit.eval,
                RossSelingerPrimitive.eval, Matrix.mul_assoc]
      _ = CliffordTCircuit.eval (List.replicate 5 RossSelingerPrimitive.t) *
              stateColumn z (rsOmegaAlg ^ (3 : ℕ) * w) := by
              rw [hadamard2_apply_applyHTPowToState]
              norm_num
      _ = stateColumn z (rsOmegaAlg ^ 5 * (rsOmegaAlg ^ (3 : ℕ) * w)) := by
              rw [eval_replicate_t_stateColumn]
        _ = stateColumn z w := by
                have hpow : rsOmegaAlg ^ 5 * rsOmegaAlg ^ (3 : ℕ) = (1 : ℂ) :=
                  rsOmegaAlg_pow_add_compl 5 3 (by norm_num)
                simpa [mul_assoc] using
                  congrArg (fun q : ℂ => stateColumn z (q * w)) hpow

theorem optimizedInverseHT_apply_applyHTPowToState
    (k : Fin 4) (z w : ℂ) :
    CliffordTCircuit.eval (optimizedInverseHTWord k) *
      stateColumn
        (applyHTPowToState k z w).1
        (applyHTPowToState k z w).2
      =
    stateColumn z w := by
  fin_cases k
  · simpa [optimizedInverseHTWord, CliffordTCircuit.eval, RossSelingerPrimitive.eval]
      using hadamard2_apply_applyHTPowToState (0 : Fin 4) z w
  · calc
      CliffordTCircuit.eval (optimizedInverseHTWord 1) *
          stateColumn
            (applyHTPowToState 1 z w).1
            (applyHTPowToState 1 z w).2
          = phaseS * (phaseS * (phaseS *
              (phaseT *
                (hadamard2 *
                  stateColumn
                    (applyHTPowToState 1 z w).1
                    (applyHTPowToState 1 z w).2)))) := by
              simp [optimizedInverseHTWord, CliffordTCircuit.eval,
                RossSelingerPrimitive.eval, Matrix.mul_assoc]
      _ = phaseS * (phaseS * (phaseS *
              (phaseT * stateColumn z (rsOmegaAlg ^ (1 : ℕ) * w)))) := by
              rw [hadamard2_apply_applyHTPowToState]
              norm_num
      _ = stateColumn z w := by
              rw [phaseT_stateColumn, phaseS_stateColumn, phaseS_stateColumn,
                phaseS_stateColumn]
              have hω2 : rsOmegaAlg ^ 2 = Complex.I := by
                simpa [pow_two] using rsOmegaAlg_mul_self
              have hω8 : rsOmegaAlg ^ 8 = (1 : ℂ) := rsOmegaAlg_pow_eight
              have hscalar :
                  Complex.I * (Complex.I * (Complex.I *
                    (rsOmegaAlg * (rsOmegaAlg * w)))) = w := by
                calc
                  Complex.I * (Complex.I * (Complex.I *
                      (rsOmegaAlg * (rsOmegaAlg * w))))
                      = rsOmegaAlg ^ 8 * w := by
                          rw [← hω2]
                          ring
                  _ = w := by rw [hω8]; ring
              simpa [stateColumn, hscalar]
  · calc
      CliffordTCircuit.eval (optimizedInverseHTWord 2) *
          stateColumn
            (applyHTPowToState 2 z w).1
            (applyHTPowToState 2 z w).2
          = phaseS * (phaseS * (phaseS *
                (hadamard2 *
                  stateColumn
                    (applyHTPowToState 2 z w).1
                    (applyHTPowToState 2 z w).2))) := by
              simp [optimizedInverseHTWord, CliffordTCircuit.eval,
                RossSelingerPrimitive.eval, Matrix.mul_assoc]
      _ = phaseS * (phaseS * (phaseS *
              stateColumn z (rsOmegaAlg ^ (2 : ℕ) * w))) := by
              rw [hadamard2_apply_applyHTPowToState]
              norm_num
      _ = stateColumn z w := by
              rw [phaseS_stateColumn, phaseS_stateColumn, phaseS_stateColumn]
              have hω2 : rsOmegaAlg ^ 2 = Complex.I := by
                simpa [pow_two] using rsOmegaAlg_mul_self
              have hω8 : rsOmegaAlg ^ 8 = (1 : ℂ) := rsOmegaAlg_pow_eight
              have hscalar :
                  Complex.I * (Complex.I * (Complex.I *
                    (rsOmegaAlg ^ 2 * w))) = w := by
                calc
                  Complex.I * (Complex.I * (Complex.I *
                      (rsOmegaAlg ^ 2 * w)))
                      = rsOmegaAlg ^ 8 * w := by
                          rw [← hω2]
                          ring
                  _ = w := by rw [hω8]; ring
              simpa [stateColumn, hscalar]
  · calc
      CliffordTCircuit.eval (optimizedInverseHTWord 3) *
          stateColumn
            (applyHTPowToState 3 z w).1
            (applyHTPowToState 3 z w).2
          = phaseS * (phaseS *
              (phaseT *
                (hadamard2 *
                  stateColumn
                    (applyHTPowToState 3 z w).1
                    (applyHTPowToState 3 z w).2))) := by
              simp [optimizedInverseHTWord, CliffordTCircuit.eval,
                RossSelingerPrimitive.eval, Matrix.mul_assoc]
      _ = phaseS * (phaseS *
              (phaseT * stateColumn z (rsOmegaAlg ^ (3 : ℕ) * w))) := by
              rw [hadamard2_apply_applyHTPowToState]
              norm_num
      _ = stateColumn z w := by
              rw [phaseT_stateColumn, phaseS_stateColumn, phaseS_stateColumn]
              have hω2 : rsOmegaAlg ^ 2 = Complex.I := by
                simpa [pow_two] using rsOmegaAlg_mul_self
              have hω8 : rsOmegaAlg ^ 8 = (1 : ℂ) := rsOmegaAlg_pow_eight
              have hscalar :
                  Complex.I * (Complex.I *
                    (rsOmegaAlg * (rsOmegaAlg ^ 3 * w))) = w := by
                calc
                  Complex.I * (Complex.I *
                      (rsOmegaAlg * (rsOmegaAlg ^ 3 * w)))
                      = rsOmegaAlg ^ 8 * w := by
                          rw [← hω2]
                          ring
                  _ = w := by rw [hω8]; ring
              simpa [stateColumn, hscalar]

/-- If a reduced state has a circuit, then composing with the inverse
`H T^k` step prepares the original state.  This isolates the missing concrete
circuit-evaluation lemma for the KMM induction. -/
theorem kmm_state_preparation_step_from_reduced
    {z w z' w' : ℂ}
    (k : Fin 4)
    (hz' : z' = (applyHTPowToState k z w).1)
    (hw' : w' = (applyHTPowToState k z w).2)
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w)
    (hEntries' : StateEntriesInDyadicCyclotomic z' w')
    (hState' : IsUnitState z' w')
    (hPrep' : ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z' w') :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w := by
  rcases hPrep' with ⟨C', hC'⟩
  refine ⟨prependInverseHT k C', ?_⟩
  rw [eval_prependInverseHT]
  rw [Matrix.mul_assoc, hC']
  rw [hz', hw']
  exact inverseHT_apply_applyHTPowToState k z w

/-- T-count-tracking version of `kmm_state_preparation_step_from_reduced`,
using the optimized inverse `HT` word. -/
theorem kmm_state_preparation_optimized_step_from_reduced
    {z w z' w' : ℂ}
    (k : Fin 4)
    (hz' : z' = (applyHTPowToState k z w).1)
    (hw' : w' = (applyHTPowToState k z w).2)
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w)
    (hEntries' : StateEntriesInDyadicCyclotomic z' w')
    (hState' : IsUnitState z' w')
    {C' : CliffordTCircuit}
    (hPrep' : CliffordTCircuit.eval C' * ket0Column = stateColumn z' w') :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w ∧
        TCount C ≤ TCount C' + 1 := by
  refine ⟨prependOptimizedInverseHT k C', ?_, ?_⟩
  · simp [prependOptimizedInverseHT, CliffordTCircuit.eval_append]
    rw [Matrix.mul_assoc, hPrep']
    rw [hz', hw']
    exact optimizedInverseHT_apply_applyHTPowToState k z w
  · exact TCount_prependOptimizedInverseHT_le k C'

theorem first_column_is_unit_state
    {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    IsUnitState (U 0 0) (U 1 0) := by
  have hUU : U† * U = (1 : Square 2) := Matrix.mem_unitaryGroup_iff'.mp hU
  have h00 := congr_fun (congr_fun hUU 0) 0
  simpa [IsUnitState, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply] using h00

theorem first_column_entries_in_dyadic
    {U : Square 2}
    (hEntries : MatrixEntriesInDyadicCyclotomic U) :
    StateEntriesInDyadicCyclotomic (U 0 0) (U 1 0) :=
  ⟨hEntries 0 0, hEntries 1 0⟩

theorem unitary_fixing_ket0_is_diagonal_phase
    {W : Square 2}
    (hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hFix : W * ket0Column = ket0Column) :
    ∃ α : ℂ,
      star α * α = 1 ∧
      W = Matrix.of ![![(1 : ℂ), 0], ![0, α]] := by
  have h00 : W 0 0 = 1 := by
    have h := congr_fun (congr_fun hFix 0) 0
    simpa [ket0Column, Matrix.mul_apply, Fin.sum_univ_two] using h
  have h10 : W 1 0 = 0 := by
    have h := congr_fun (congr_fun hFix 1) 0
    simpa [ket0Column, Matrix.mul_apply, Fin.sum_univ_two] using h
  have hUU : W† * W = (1 : Square 2) := Matrix.mem_unitaryGroup_iff'.mp hW
  have h01 : W 0 1 = 0 := by
    have h := congr_fun (congr_fun hUU 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      h00, h10] at h
    simpa using h
  have hNorm : star (W 1 1) * (W 1 1) = 1 := by
    have h := congr_fun (congr_fun hUU 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      h01] using h
  refine ⟨W 1 1, hNorm, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h01]

/-- Split an equality in `ℤ + ℤ√2` using irrationality of `√2`. -/
theorem int_add_int_mul_sqrtTwo_eq_int
    {A B R : ℤ}
    (h : ((A : ℂ) + (B : ℂ) * sqrtTwoComplex) = (R : ℂ)) :
    B = 0 ∧ A = R := by
  have hre : (A : ℝ) + (B : ℝ) * Real.sqrt 2 = (R : ℝ) := by
    have h' := congrArg Complex.re h
    simpa [sqrtTwoComplex] using h'
  have hB : B = 0 := by
    by_contra hB
    have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB
    have hsqrt : Real.sqrt 2 = ((R - A : ℤ) : ℝ) / (B : ℝ) := by
      have hre' : (B : ℝ) * Real.sqrt 2 = ((R - A : ℤ) : ℝ) := by
        norm_num
        linarith
      exact (eq_div_iff hBreal).2 (by simpa [mul_comm] using hre')
    exact (irrational_sqrt_two.ne_rational (R - A) B) hsqrt
  have hA : A = R := by
    subst hB
    norm_num at hre
    exact_mod_cast hre
  exact ⟨hB, hA⟩

private theorem int_sq_nonneg (x : ℤ) : 0 ≤ x ^ 2 := by
  nlinarith [sq_nonneg x]

private theorem int_sq_eq_zero_of_nonpos {x : ℤ} (h : x ^ 2 ≤ 0) :
    x = 0 := by
  nlinarith [sq_nonneg x]

private theorem int_sq_le_one_cases {x : ℤ} (h : x ^ 2 ≤ 1) :
    x = -1 ∨ x = 0 ∨ x = 1 := by
  have hxlo : -2 < x := by nlinarith [sq_nonneg (x + 2)]
  have hxhi : x < 2 := by nlinarith [sq_nonneg (x - 2)]
  omega

private theorem rsOmegaAlg_pow_0 :
    rsOmegaAlg ^ 0 = (1 : ℂ) := by
  simp

private theorem rsOmegaAlg_pow_1 :
    rsOmegaAlg ^ 1 = rsOmegaAlg := by
  simp

private theorem rsOmegaAlg_pow_2 :
    rsOmegaAlg ^ 2 = Complex.I := by
  simpa [pow_two] using rsOmegaAlg_mul_self

private theorem rsOmegaAlg_pow_3 :
    rsOmegaAlg ^ 3 = ((-1 : ℂ) + Complex.I) / sqrtTwoComplex := by
  rw [show rsOmegaAlg ^ 3 = rsOmegaAlg ^ 2 * rsOmegaAlg by ring]
  rw [rsOmegaAlg_pow_2, rsOmegaAlg]
  field_simp [sqrtTwoComplex_ne_zero]
  rw [mul_add, Complex.I_mul_I]
  ring

private theorem rsOmegaAlg_pow_4 :
    rsOmegaAlg ^ 4 = (-1 : ℂ) :=
  rsOmegaAlg_pow_four

private theorem rsOmegaAlg_pow_5 :
    rsOmegaAlg ^ 5 = ((-1 : ℂ) - Complex.I) / sqrtTwoComplex := by
  calc
    rsOmegaAlg ^ 5 = rsOmegaAlg ^ 4 * rsOmegaAlg := by ring
    _ = (-1 : ℂ) * rsOmegaAlg := by rw [rsOmegaAlg_pow_4]
    _ = ((-1 : ℂ) - Complex.I) / sqrtTwoComplex := by
      rw [rsOmegaAlg]
      ring

private theorem rsOmegaAlg_pow_6 :
    rsOmegaAlg ^ 6 = -Complex.I := by
  calc
    rsOmegaAlg ^ 6 = rsOmegaAlg ^ 4 * rsOmegaAlg ^ 2 := by ring
    _ = -Complex.I := by rw [rsOmegaAlg_pow_4, rsOmegaAlg_pow_2]; ring

private theorem rsOmegaAlg_pow_7 :
    rsOmegaAlg ^ 7 = ((1 : ℂ) - Complex.I) / sqrtTwoComplex := by
  calc
    rsOmegaAlg ^ 7 = rsOmegaAlg ^ 4 * rsOmegaAlg ^ 3 := by ring
    _ = ((1 : ℂ) - Complex.I) / sqrtTwoComplex := by
      rw [rsOmegaAlg_pow_4, rsOmegaAlg_pow_3]
      ring

private theorem div_sqrtTwo_eq_one_of_eq_sqrtTwo {z : ℂ}
    (h : z = sqrtTwoComplex) :
    z / sqrtTwoComplex = 1 := by
  rw [h]
  field_simp [sqrtTwoComplex_ne_zero]

private theorem div_sqrtTwo_eq_neg_one_of_eq_neg_sqrtTwo {z : ℂ}
    (h : z = -sqrtTwoComplex) :
    z / sqrtTwoComplex = -1 := by
  rw [h]
  field_simp [sqrtTwoComplex_ne_zero]

private theorem div_sqrtTwo_eq_I_of_eq_sqrtTwo_mul_I {z : ℂ}
    (h : z = sqrtTwoComplex * Complex.I) :
    z / sqrtTwoComplex = Complex.I := by
  rw [h]
  field_simp [sqrtTwoComplex_ne_zero]

private theorem div_sqrtTwo_eq_neg_I_of_eq_neg_sqrtTwo_mul_I {z : ℂ}
    (h : z = -(sqrtTwoComplex * Complex.I)) :
    z / sqrtTwoComplex = -Complex.I := by
  rw [h]
  field_simp [sqrtTwoComplex_ne_zero]

private theorem dyadic_unit_phase_integer_norm_classification_n0
    {a b c d : ℤ}
    (hCross : a * b + c * d = 0)
    (hNorm : a ^ 2 + c ^ 2 + 2 * b ^ 2 + 2 * d ^ 2 = 1) :
    ∃ m : Fin 8,
      ((((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
          ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
        (sqrtTwoComplex ^ 0)) = rsOmegaAlg ^ (m : ℕ) := by
  have hb_le : 2 * b ^ 2 ≤ 1 := by
    nlinarith [int_sq_nonneg a, int_sq_nonneg c, int_sq_nonneg d, hNorm]
  have hd_le : 2 * d ^ 2 ≤ 1 := by
    nlinarith [int_sq_nonneg a, int_sq_nonneg b, int_sq_nonneg c, hNorm]
  have hb0 : b = 0 := by
    nlinarith [int_sq_nonneg b, hb_le]
  have hd0 : d = 0 := by
    nlinarith [int_sq_nonneg d, hd_le]
  subst hb0
  subst hd0
  norm_num at hNorm
  have hac : a ^ 2 + c ^ 2 = 1 := by simpa using hNorm
  have ha_bound : a ^ 2 ≤ 1 := by nlinarith [int_sq_nonneg c, hac]
  have hc_bound : c ^ 2 ≤ 1 := by nlinarith [int_sq_nonneg a, hac]
  have ha_lo : -1 ≤ a := by nlinarith [int_sq_nonneg a, ha_bound]
  have ha_hi : a ≤ 1 := by nlinarith [int_sq_nonneg a, ha_bound]
  have hc_lo : -1 ≤ c := by nlinarith [int_sq_nonneg c, hc_bound]
  have hc_hi : c ≤ 1 := by nlinarith [int_sq_nonneg c, hc_bound]
  interval_cases a <;> interval_cases c <;> try omega
  · refine ⟨4, ?_⟩
    simp [rsOmegaAlg_pow_4]
  · refine ⟨6, ?_⟩
    simp [rsOmegaAlg_pow_6]
  · refine ⟨2, ?_⟩
    simp [rsOmegaAlg_pow_2]
  · refine ⟨0, ?_⟩
    simp [rsOmegaAlg_pow_0]

private theorem dyadic_unit_phase_integer_norm_classification_n1
    {a b c d : ℤ}
    (hCross : a * b + c * d = 0)
    (hNorm : a ^ 2 + c ^ 2 + 2 * b ^ 2 + 2 * d ^ 2 = 2) :
    ∃ m : Fin 8,
      ((((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
          ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
        (sqrtTwoComplex ^ 1)) = rsOmegaAlg ^ (m : ℕ) := by
  have ha_sq_le : a ^ 2 ≤ 2 := by
    nlinarith [int_sq_nonneg b, int_sq_nonneg c, int_sq_nonneg d, hNorm]
  have hb_sq_le : b ^ 2 ≤ 1 := by
    nlinarith [int_sq_nonneg a, int_sq_nonneg c, int_sq_nonneg d, hNorm]
  have hc_sq_le : c ^ 2 ≤ 2 := by
    nlinarith [int_sq_nonneg a, int_sq_nonneg b, int_sq_nonneg d, hNorm]
  have hd_sq_le : d ^ 2 ≤ 1 := by
    nlinarith [int_sq_nonneg a, int_sq_nonneg b, int_sq_nonneg c, hNorm]
  have ha_lo : -1 ≤ a := by nlinarith [int_sq_nonneg a, ha_sq_le]
  have ha_hi : a ≤ 1 := by nlinarith [int_sq_nonneg a, ha_sq_le]
  have hb_lo : -1 ≤ b := by nlinarith [int_sq_nonneg b, hb_sq_le]
  have hb_hi : b ≤ 1 := by nlinarith [int_sq_nonneg b, hb_sq_le]
  have hc_lo : -1 ≤ c := by nlinarith [int_sq_nonneg c, hc_sq_le]
  have hc_hi : c ≤ 1 := by nlinarith [int_sq_nonneg c, hc_sq_le]
  have hd_lo : -1 ≤ d := by nlinarith [int_sq_nonneg d, hd_sq_le]
  have hd_hi : d ≤ 1 := by nlinarith [int_sq_nonneg d, hd_sq_le]
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    interval_cases d <;> try omega
  · refine ⟨5, ?_⟩
    simp [rsOmegaAlg_pow_5]
    ring
  · refine ⟨3, ?_⟩
    simp [rsOmegaAlg_pow_3]
  · refine ⟨4, ?_⟩
    field_simp [sqrtTwoComplex_ne_zero]
    simp [rsOmegaAlg_pow_4]
  · refine ⟨6, ?_⟩
    field_simp [sqrtTwoComplex_ne_zero]
    simp [rsOmegaAlg_pow_6]
  · refine ⟨2, ?_⟩
    field_simp [sqrtTwoComplex_ne_zero]
    simp [rsOmegaAlg_pow_2]
  · refine ⟨0, ?_⟩
    field_simp [sqrtTwoComplex_ne_zero]
    simp [rsOmegaAlg_pow_0]
  · refine ⟨7, ?_⟩
    simp [rsOmegaAlg_pow_7]
    ring
  · refine ⟨1, ?_⟩
    simp [rsOmegaAlg_pow_1, rsOmegaAlg]

private theorem two_pow_add_two_int (n : ℕ) :
    (2 : ℤ) ^ (n + 2) = 4 * (2 : ℤ) ^ n := by
  rw [show n + 2 = n + 1 + 1 by omega]
  simp [pow_succ]
  ring

private theorem even_a_c_of_norm_ge_two
    {n : ℕ} {a b c d : ℤ}
    (hn : 2 ≤ n)
    (hCross : a * b + c * d = 0)
    (hNorm : a ^ 2 + c ^ 2 + 2 * b ^ 2 + 2 * d ^ 2 = 2 ^ n) :
    Even a ∧ Even c := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  obtain ⟨A, rfl⟩ | ⟨A, rfl⟩ := Int.even_or_odd a
  · obtain ⟨C, rfl⟩ | ⟨C, rfl⟩ := Int.even_or_odd c
    · exact ⟨⟨A, rfl⟩, ⟨C, rfl⟩⟩
    · exfalso
      rw [two_pow_add_two_int] at hNorm
      ring_nf at hNorm
      omega
  · obtain ⟨C, rfl⟩ | ⟨C, rfl⟩ := Int.even_or_odd c
    · exfalso
      rw [two_pow_add_two_int] at hNorm
      ring_nf at hNorm
      omega
    · obtain ⟨B, rfl⟩ | ⟨B, rfl⟩ := Int.even_or_odd b
      · obtain ⟨D, rfl⟩ | ⟨D, rfl⟩ := Int.even_or_odd d
        · exfalso
          rw [two_pow_add_two_int] at hNorm
          ring_nf at hNorm
          omega
        · exfalso
          ring_nf at hCross
          omega
      · obtain ⟨D, rfl⟩ | ⟨D, rfl⟩ := Int.even_or_odd d
        · exfalso
          ring_nf at hCross
          omega
        · exfalso
          rw [two_pow_add_two_int] at hNorm
          ring_nf at hNorm
          omega

private theorem dyadic_unit_phase_integer_norm_descent
    {n : ℕ} {a b c d : ℤ}
    (hn : 2 ≤ n)
    (hCross : a * b + c * d = 0)
    (hNorm : a ^ 2 + c ^ 2 + 2 * b ^ 2 + 2 * d ^ 2 = 2 ^ n) :
    ∃ A C : ℤ,
      a = 2 * A ∧
      c = 2 * C ∧
      b * A + d * C = 0 ∧
      b ^ 2 + d ^ 2 + 2 * A ^ 2 + 2 * C ^ 2 = 2 ^ (n - 1) ∧
      ((((a : ℂ) + (b : ℂ) * sqrtTwoComplex) +
          ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
        (sqrtTwoComplex ^ n))
      =
      ((((b : ℂ) + (A : ℂ) * sqrtTwoComplex) +
          ((d : ℂ) + (C : ℂ) * sqrtTwoComplex) * Complex.I) /
        (sqrtTwoComplex ^ (n - 1))) := by
  rcases even_a_c_of_norm_ge_two hn hCross hNorm with ⟨haEven, hcEven⟩
  rcases haEven with ⟨A, ha⟩
  rcases hcEven with ⟨C, hc⟩
  have ha2 : a = 2 * A := by omega
  have hc2 : c = 2 * C := by omega
  refine ⟨A, C, ha2, hc2, ?_, ?_, ?_⟩
  · rw [ha2, hc2] at hCross
    ring_nf at hCross
    nlinarith
  · have hpow : (2 : ℤ) ^ n = 2 * (2 : ℤ) ^ (n - 1) := by
      nth_rewrite 1 [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
      ring
    rw [ha2, hc2] at hNorm
    rw [hpow] at hNorm
    ring_nf at hNorm
    nlinarith
  · rw [ha2, hc2]
    have hn_eq : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn_eq]
    rw [pow_succ]
    field_simp [sqrtTwoComplex_ne_zero, pow_ne_zero (n - 1) sqrtTwoComplex_ne_zero]
    ring_nf
    rw [sqrtTwoComplex_sq]
    norm_num
    ring_nf

/-- Arithmetic kernel for phase units in `D[ω]`, after all complex
star/division algebra has been expanded away.

The hypothesis says the numerator norm is
`(a^2 + c^2 + 2*b^2 + 2*d^2) + 2*(a*b + c*d)*sqrt2 = 2^n`.
The remaining proof should split the rational and `sqrt2` parts, then use the
KMM parity/descent argument plus the `n = 0, 1` finite classifications. -/
theorem dyadic_unit_phase_integer_norm_classification
    {n : ℕ} {a b c d : ℤ}
    (hCross : a * b + c * d = 0)
    (hNorm : a ^ 2 + c ^ 2 + 2 * b ^ 2 + 2 * d ^ 2 = 2 ^ n) :
    ∃ m : Fin 8,
  (((a : ℂ) + (b : ℂ) * sqrtTwoComplex +
          ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
        sqrtTwoComplex ^ n) = rsOmegaAlg ^ (m : ℕ) := by
  induction n using Nat.strong_induction_on generalizing a b c d with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        have hNorm0 : a ^ 2 + c ^ 2 + 2 * b ^ 2 + 2 * d ^ 2 = 1 := by
          simpa using hNorm
        simpa [add_assoc] using
          dyadic_unit_phase_integer_norm_classification_n0 hCross hNorm0
      by_cases hn1 : n = 1
      · subst n
        have hNorm1 : a ^ 2 + c ^ 2 + 2 * b ^ 2 + 2 * d ^ 2 = 2 := by
          simpa using hNorm
        simpa [add_assoc] using
          dyadic_unit_phase_integer_norm_classification_n1 hCross hNorm1
      have hn2 : 2 ≤ n := by omega
      rcases dyadic_unit_phase_integer_norm_descent hn2 hCross hNorm with
        ⟨A, C, ha, hc, hCross', hNorm', hVal⟩
      have hlt : n - 1 < n := by omega
      rcases ih (n - 1) hlt hCross' hNorm' with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [hVal]
      simpa [add_assoc] using hm

theorem dyadic_unit_phase_classification_from_norm_equation
    {n : ℕ} {a b c d : ℤ}
    (hEq :
      ((a ^ 2 + c ^ 2 + 2 * b ^ 2 + 2 * d ^ 2 : ℤ) : ℂ) +
          ((2 * (a * b + c * d) : ℤ) : ℂ) * sqrtTwoComplex =
        (2 : ℂ) ^ n) :
    ∃ m : Fin 8,
      (((a : ℂ) + (b : ℂ) * sqrtTwoComplex +
          ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
        sqrtTwoComplex ^ n) = rsOmegaAlg ^ (m : ℕ) := by
  have hEq' :
      ((a ^ 2 + c ^ 2 + 2 * b ^ 2 + 2 * d ^ 2 : ℤ) : ℂ) +
          ((2 * (a * b + c * d) : ℤ) : ℂ) * sqrtTwoComplex =
        ((2 ^ n : ℤ) : ℂ) := by
    simpa using hEq
  rcases int_add_int_mul_sqrtTwo_eq_int hEq' with ⟨hB, hA⟩
  have hCross : a * b + c * d = 0 := by
    omega
  have hNorm : a ^ 2 + c ^ 2 + 2 * b ^ 2 + 2 * d ^ 2 = 2 ^ n := hA
  exact dyadic_unit_phase_integer_norm_classification hCross hNorm

/-- Expand the norm-one condition for a dyadic cyclotomic coordinate into the
single numerator norm equation used by the arithmetic classification lemma. -/
theorem dyadic_unit_phase_classification_from_coordinates
    {n : ℕ} {a b c d : ℤ}
    (hNorm :
      star
          (((a : ℂ) + (b : ℂ) * sqrtTwoComplex +
              ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
            sqrtTwoComplex ^ n) *
            (((a : ℂ) + (b : ℂ) * sqrtTwoComplex +
                ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
              sqrtTwoComplex ^ n) =
        1) :
    ∃ m : Fin 8,
      (((a : ℂ) + (b : ℂ) * sqrtTwoComplex +
          ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
        sqrtTwoComplex ^ n) = rsOmegaAlg ^ (m : ℕ) := by
  let N : ℂ :=
    (a : ℂ) + (b : ℂ) * sqrtTwoComplex +
      ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I
  have hsstar : star sqrtTwoComplex = sqrtTwoComplex := by simp [sqrtTwoComplex]
  have hpow_ne : sqrtTwoComplex ^ n ≠ 0 := pow_ne_zero n sqrtTwoComplex_ne_zero
  have hNnorm :
      star N * N = sqrtTwoComplex ^ (2 * n) := by
    have hfrac :
        (star N * N) / (sqrtTwoComplex ^ n * sqrtTwoComplex ^ n) = 1 := by
      simpa [N, div_eq_mul_inv, star_mul, star_inv, hsstar, mul_assoc,
        mul_left_comm, mul_comm] using hNorm
    have hden_ne : sqrtTwoComplex ^ n * sqrtTwoComplex ^ n ≠ 0 :=
      mul_ne_zero hpow_ne hpow_ne
    have hmul := congrArg (fun x : ℂ => x * (sqrtTwoComplex ^ n * sqrtTwoComplex ^ n)) hfrac
    have hprod : star N * N = sqrtTwoComplex ^ n * sqrtTwoComplex ^ n := by
      simpa [hden_ne] using hmul
    calc
      star N * N = sqrtTwoComplex ^ n * sqrtTwoComplex ^ n := hprod
      _ = sqrtTwoComplex ^ (2 * n) := by
          rw [← pow_add]
          congr 1
          omega
  have hExpanded :
      ((a ^ 2 + c ^ 2 + 2 * b ^ 2 + 2 * d ^ 2 : ℤ) : ℂ) +
          ((2 * (a * b + c * d) : ℤ) : ℂ) * sqrtTwoComplex =
        (2 : ℂ) ^ n := by
    have hleft :
        star N * N =
          ((a ^ 2 + c ^ 2 + 2 * b ^ 2 + 2 * d ^ 2 : ℤ) : ℂ) +
            ((2 * (a * b + c * d) : ℤ) : ℂ) * sqrtTwoComplex := by
      simp [N, sqrtTwoComplex]
      ring_nf
      rw [show ((↑(Real.sqrt 2) : ℂ) ^ 2) = (2 : ℂ) by
        exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))]
      simp [Complex.I_sq]
      ring
    have hright : sqrtTwoComplex ^ (2 * n) = (2 : ℂ) ^ n := by
      calc
        sqrtTwoComplex ^ (2 * n) = (sqrtTwoComplex ^ 2) ^ n := by
          rw [pow_mul]
        _ = (2 : ℂ) ^ n := by rw [sqrtTwoComplex_sq]
    rw [← hleft, hNnorm, hright]
  exact dyadic_unit_phase_classification_from_norm_equation hExpanded

theorem dyadic_unit_phase_is_omega_pow
    {α : ℂ}
    (hα : InDyadicCyclotomic α)
    (hNorm : star α * α = 1) :
    ∃ m : Fin 8, α = rsOmegaAlg ^ (m : ℕ) := by
  rcases hα with ⟨n, a, b, c, d, hα⟩
  have hNorm' :
      star
          (((a : ℂ) + (b : ℂ) * sqrtTwoComplex +
              ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
            sqrtTwoComplex ^ n) *
            (((a : ℂ) + (b : ℂ) * sqrtTwoComplex +
                ((c : ℂ) + (d : ℂ) * sqrtTwoComplex) * Complex.I) /
              sqrtTwoComplex ^ n) =
        1 := by
    simpa [hα] using hNorm
  rcases dyadic_unit_phase_classification_from_coordinates hNorm' with ⟨m, hm⟩
  exact ⟨m, by simpa [hα] using hm⟩

theorem diagonal_omega_pow_exact
    (m : Fin 8) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C =
        Matrix.of ![![(1 : ℂ), 0], ![0, rsOmegaAlg ^ (m : ℕ)]] := by
  refine ⟨List.replicate (m : ℕ) RossSelingerPrimitive.t, ?_⟩
  exact eval_replicate_t_matrix (m : ℕ)

/-- The diagonal `ω^m` phase correction costs at most seven `T` gates. -/
theorem diagonal_omega_pow_exact_tcount
    (m : Fin 8) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C =
        Matrix.of ![![(1 : ℂ), 0], ![0, rsOmegaAlg ^ (m : ℕ)]] ∧
        TCount C ≤ 7 := by
  refine ⟨List.replicate (m : ℕ) RossSelingerPrimitive.t, ?_, ?_⟩
  · exact eval_replicate_t_matrix (m : ℕ)
  · rw [TCount_replicate_t]
    exact Nat.le_of_lt_succ m.2

/-! ### Step 2b: circuit witnesses for the `omegaSDE z = 0` classification -/

private lemma eq_zero_of_star_self_eq_zero {w : ℂ} (h : star w * w = 0) : w = 0 := by
  have h' : (Complex.normSq w : ℂ) = 0 := by
    rw [Complex.normSq_eq_conj_mul_self]
    simpa using h
  have hnormSq : Complex.normSq w = 0 := by exact_mod_cast h'
  exact Complex.normSq_eq_zero.mp hnormSq

/-- For a unit state at `omegaSDE z = 0`, an explicit Clifford+T circuit
prepares `(z, w)` from `|0⟩`.  Each of the 9 classifier cases dispatches to one
of the `replicate _ .omega` or `replicate _ .t ++ X` witness lemmas. -/
theorem unit_state_omegaSDE_zero_has_circuit
    {z w : ℂ} {x : OmegaIntCoord}
    (hzpres : z = OmegaIntCoord.val x)
    (hwDyadic : InDyadicCyclotomic w)
    (hwOmegaDyadic : InOmegaDyadicCyclotomic w)
    (hState : IsUnitState z w) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w := by
  rcases unit_state_omegaSDE_zero_classification hzpres hwOmegaDyadic hState with
    h | h | h | h | h | h | h | h | h
  -- Case 0: x = ⟨0, 0, 0, 0⟩.  z = 0, |w|² = 1, w = ω^k.
  · subst h
    have hzZero : z = 0 := by rw [hzpres]; simp [OmegaIntCoord.val]
    have hwNorm : star w * w = 1 := by
      have hSt := hState; unfold IsUnitState at hSt
      rw [hzZero] at hSt
      linear_combination hSt
    rcases dyadic_unit_phase_is_omega_pow hwDyadic hwNorm with ⟨m, hwval⟩
    refine ⟨List.replicate (m : ℕ) RossSelingerPrimitive.omega ++ cliffordT_X_word, ?_⟩
    rw [cliffordT_circuit_zero_omegaPow, hzZero, hwval]
  all_goals subst h
  -- Cases 1–8: z = ω^k for explicit k; w = 0.
  -- Case ⟨1, 0, 0, 0⟩: z = 1 = ω^0.
  · refine ⟨List.replicate 0 RossSelingerPrimitive.omega, ?_⟩
    rw [cliffordT_circuit_omegaPow_zero]
    have hzval : z = 1 := by rw [hzpres]; simp [OmegaIntCoord.val]
    have hzNorm : star z * z = 1 := by rw [hzval]; simp
    have hwZero : w = 0 :=
      eq_zero_of_star_self_eq_zero (by
        have hSt := hState; unfold IsUnitState at hSt
        linear_combination hSt - hzNorm)
    rw [hwZero, hzval]; simp
  -- Case ⟨-1, 0, 0, 0⟩: z = -1 = ω^4.
  · refine ⟨List.replicate 4 RossSelingerPrimitive.omega, ?_⟩
    rw [cliffordT_circuit_omegaPow_zero, rsOmegaAlg_pow_four]
    have hzval : z = -1 := by rw [hzpres]; simp [OmegaIntCoord.val]
    have hzNorm : star z * z = 1 := by rw [hzval]; simp
    have hwZero : w = 0 :=
      eq_zero_of_star_self_eq_zero (by
        have hSt := hState; unfold IsUnitState at hSt
        linear_combination hSt - hzNorm)
    rw [hwZero, hzval]
  -- Case ⟨0, 1, 0, 0⟩: z = ω.
  · refine ⟨List.replicate 1 RossSelingerPrimitive.omega, ?_⟩
    rw [cliffordT_circuit_omegaPow_zero]
    have hzval : z = rsOmegaAlg ^ 1 := by
      rw [hzpres]; simp [OmegaIntCoord.val]
    have hzNorm : star z * z = 1 := by
      rw [hzval]; exact rsOmegaAlg_pow_unit 1
    have hwZero : w = 0 :=
      eq_zero_of_star_self_eq_zero (by
        have hSt := hState; unfold IsUnitState at hSt
        linear_combination hSt - hzNorm)
    rw [hwZero, hzval]
  -- Case ⟨0, -1, 0, 0⟩: z = -ω = ω^5.
  · refine ⟨List.replicate 5 RossSelingerPrimitive.omega, ?_⟩
    rw [cliffordT_circuit_omegaPow_zero, rsOmegaAlg_five]
    have hzval : z = -rsOmegaAlg := by
      rw [hzpres]; simp [OmegaIntCoord.val]
    have hzNorm : star z * z = 1 := by
      have hu := rsOmegaAlg_pow_unit 1
      rw [hzval]
      have : star (-rsOmegaAlg) * (-rsOmegaAlg) = star rsOmegaAlg * rsOmegaAlg := by
        rw [star_neg]; ring
      rw [this]; simpa using hu
    have hwZero : w = 0 :=
      eq_zero_of_star_self_eq_zero (by
        have hSt := hState; unfold IsUnitState at hSt
        linear_combination hSt - hzNorm)
    rw [hwZero, hzval]
  -- Case ⟨0, 0, 1, 0⟩: z = ω².
  · refine ⟨List.replicate 2 RossSelingerPrimitive.omega, ?_⟩
    rw [cliffordT_circuit_omegaPow_zero]
    have hzval : z = rsOmegaAlg ^ 2 := by
      rw [hzpres]; simp [OmegaIntCoord.val]
    have hzNorm : star z * z = 1 := by
      rw [hzval]; exact rsOmegaAlg_pow_unit 2
    have hwZero : w = 0 :=
      eq_zero_of_star_self_eq_zero (by
        have hSt := hState; unfold IsUnitState at hSt
        linear_combination hSt - hzNorm)
    rw [hwZero, hzval]
  -- Case ⟨0, 0, -1, 0⟩: z = -ω² = ω^6.
  · refine ⟨List.replicate 6 RossSelingerPrimitive.omega, ?_⟩
    rw [cliffordT_circuit_omegaPow_zero, rsOmegaAlg_six]
    have hzval : z = -rsOmegaAlg ^ 2 := by
      rw [hzpres]; simp [OmegaIntCoord.val]
    have hzNorm : star z * z = 1 := by
      have hu := rsOmegaAlg_pow_unit 2
      rw [hzval]
      have : star (-rsOmegaAlg ^ 2) * (-rsOmegaAlg ^ 2) =
          star (rsOmegaAlg ^ 2) * rsOmegaAlg ^ 2 := by
        rw [star_neg]; ring
      rw [this]; exact hu
    have hwZero : w = 0 :=
      eq_zero_of_star_self_eq_zero (by
        have hSt := hState; unfold IsUnitState at hSt
        linear_combination hSt - hzNorm)
    rw [hwZero, hzval]
  -- Case ⟨0, 0, 0, 1⟩: z = ω³.
  · refine ⟨List.replicate 3 RossSelingerPrimitive.omega, ?_⟩
    rw [cliffordT_circuit_omegaPow_zero]
    have hzval : z = rsOmegaAlg ^ 3 := by
      rw [hzpres]; simp [OmegaIntCoord.val]
    have hzNorm : star z * z = 1 := by
      rw [hzval]; exact rsOmegaAlg_pow_unit 3
    have hwZero : w = 0 :=
      eq_zero_of_star_self_eq_zero (by
        have hSt := hState; unfold IsUnitState at hSt
        linear_combination hSt - hzNorm)
    rw [hwZero, hzval]
  -- Case ⟨0, 0, 0, -1⟩: z = -ω³ = ω^7.
  · refine ⟨List.replicate 7 RossSelingerPrimitive.omega, ?_⟩
    rw [cliffordT_circuit_omegaPow_zero, rsOmegaAlg_seven]
    have hzval : z = -rsOmegaAlg ^ 3 := by
      rw [hzpres]; simp [OmegaIntCoord.val]
    have hzNorm : star z * z = 1 := by
      have hu := rsOmegaAlg_pow_unit 3
      rw [hzval]
      have : star (-rsOmegaAlg ^ 3) * (-rsOmegaAlg ^ 3) =
          star (rsOmegaAlg ^ 3) * rsOmegaAlg ^ 3 := by
        rw [star_neg]; ring
      rw [this]; exact hu
    have hwZero : w = 0 :=
      eq_zero_of_star_self_eq_zero (by
        have hSt := hState; unfold IsUnitState at hSt
        linear_combination hSt - hzNorm)
    rw [hwZero, hzval]

/-- T-count bounded variant of `unit_state_omegaSDE_zero_has_circuit`. -/
theorem unit_state_omegaSDE_zero_has_circuit_tcount
    {z w : ℂ} {x : OmegaIntCoord}
    (hzpres : z = OmegaIntCoord.val x)
    (hwDyadic : InDyadicCyclotomic w)
    (hwOmegaDyadic : InOmegaDyadicCyclotomic w)
    (hState : IsUnitState z w) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w ∧
        TCount C ≤ 0 := by
  rcases unit_state_omegaSDE_zero_classification hzpres hwOmegaDyadic hState with
    h | h | h | h | h | h | h | h | h
  · subst h
    have hzZero : z = 0 := by rw [hzpres]; simp [OmegaIntCoord.val]
    have hwNorm : star w * w = 1 := by
      have hSt := hState; unfold IsUnitState at hSt
      rw [hzZero] at hSt
      linear_combination hSt
    rcases dyadic_unit_phase_is_omega_pow hwDyadic hwNorm with ⟨m, hwval⟩
    refine ⟨List.replicate (m : ℕ) RossSelingerPrimitive.omega ++ cliffordT_X_word,
      ?_, ?_⟩
    · rw [cliffordT_circuit_zero_omegaPow, hzZero, hwval]
    · rw [TCount_append, TCount_replicate_omega, TCount_cliffordT_X_word]
  all_goals subst h
  · refine ⟨List.replicate 0 RossSelingerPrimitive.omega, ?_, ?_⟩
    · rw [cliffordT_circuit_omegaPow_zero]
      have hzval : z = 1 := by rw [hzpres]; simp [OmegaIntCoord.val]
      have hzNorm : star z * z = 1 := by rw [hzval]; simp
      have hwZero : w = 0 :=
        eq_zero_of_star_self_eq_zero (by
          have hSt := hState; unfold IsUnitState at hSt
          linear_combination hSt - hzNorm)
      rw [hwZero, hzval]; simp
    · simp [TCount_replicate_omega]
  · refine ⟨List.replicate 4 RossSelingerPrimitive.omega, ?_, ?_⟩
    · rw [cliffordT_circuit_omegaPow_zero, rsOmegaAlg_pow_four]
      have hzval : z = -1 := by rw [hzpres]; simp [OmegaIntCoord.val]
      have hzNorm : star z * z = 1 := by rw [hzval]; simp
      have hwZero : w = 0 :=
        eq_zero_of_star_self_eq_zero (by
          have hSt := hState; unfold IsUnitState at hSt
          linear_combination hSt - hzNorm)
      rw [hwZero, hzval]
    · simp [TCount_replicate_omega]
  · refine ⟨List.replicate 1 RossSelingerPrimitive.omega, ?_, ?_⟩
    · rw [cliffordT_circuit_omegaPow_zero]
      have hzval : z = rsOmegaAlg ^ 1 := by
        rw [hzpres]; simp [OmegaIntCoord.val]
      have hzNorm : star z * z = 1 := by
        rw [hzval]; exact rsOmegaAlg_pow_unit 1
      have hwZero : w = 0 :=
        eq_zero_of_star_self_eq_zero (by
          have hSt := hState; unfold IsUnitState at hSt
          linear_combination hSt - hzNorm)
      rw [hwZero, hzval]
    · simp [TCount_replicate_omega]
  · refine ⟨List.replicate 5 RossSelingerPrimitive.omega, ?_, ?_⟩
    · rw [cliffordT_circuit_omegaPow_zero, rsOmegaAlg_five]
      have hzval : z = -rsOmegaAlg := by
        rw [hzpres]; simp [OmegaIntCoord.val]
      have hzNorm : star z * z = 1 := by
        have hu := rsOmegaAlg_pow_unit 1
        rw [hzval]
        have : star (-rsOmegaAlg) * (-rsOmegaAlg) = star rsOmegaAlg * rsOmegaAlg := by
          rw [star_neg]; ring
        rw [this]; simpa using hu
      have hwZero : w = 0 :=
        eq_zero_of_star_self_eq_zero (by
          have hSt := hState; unfold IsUnitState at hSt
          linear_combination hSt - hzNorm)
      rw [hwZero, hzval]
    · simp [TCount_replicate_omega]
  · refine ⟨List.replicate 2 RossSelingerPrimitive.omega, ?_, ?_⟩
    · rw [cliffordT_circuit_omegaPow_zero]
      have hzval : z = rsOmegaAlg ^ 2 := by
        rw [hzpres]; simp [OmegaIntCoord.val]
      have hzNorm : star z * z = 1 := by
        rw [hzval]; exact rsOmegaAlg_pow_unit 2
      have hwZero : w = 0 :=
        eq_zero_of_star_self_eq_zero (by
          have hSt := hState; unfold IsUnitState at hSt
          linear_combination hSt - hzNorm)
      rw [hwZero, hzval]
    · simp [TCount_replicate_omega]
  · refine ⟨List.replicate 6 RossSelingerPrimitive.omega, ?_, ?_⟩
    · rw [cliffordT_circuit_omegaPow_zero, rsOmegaAlg_six]
      have hzval : z = -rsOmegaAlg ^ 2 := by
        rw [hzpres]; simp [OmegaIntCoord.val]
      have hzNorm : star z * z = 1 := by
        have hu := rsOmegaAlg_pow_unit 2
        rw [hzval]
        have : star (-rsOmegaAlg ^ 2) * (-rsOmegaAlg ^ 2) =
            star (rsOmegaAlg ^ 2) * rsOmegaAlg ^ 2 := by
          rw [star_neg]; ring
        rw [this]; exact hu
      have hwZero : w = 0 :=
        eq_zero_of_star_self_eq_zero (by
          have hSt := hState; unfold IsUnitState at hSt
          linear_combination hSt - hzNorm)
      rw [hwZero, hzval]
    · simp [TCount_replicate_omega]
  · refine ⟨List.replicate 3 RossSelingerPrimitive.omega, ?_, ?_⟩
    · rw [cliffordT_circuit_omegaPow_zero]
      have hzval : z = rsOmegaAlg ^ 3 := by
        rw [hzpres]; simp [OmegaIntCoord.val]
      have hzNorm : star z * z = 1 := by
        rw [hzval]; exact rsOmegaAlg_pow_unit 3
      have hwZero : w = 0 :=
        eq_zero_of_star_self_eq_zero (by
          have hSt := hState; unfold IsUnitState at hSt
          linear_combination hSt - hzNorm)
      rw [hwZero, hzval]
    · simp [TCount_replicate_omega]
  · refine ⟨List.replicate 7 RossSelingerPrimitive.omega, ?_, ?_⟩
    · rw [cliffordT_circuit_omegaPow_zero, rsOmegaAlg_seven]
      have hzval : z = -rsOmegaAlg ^ 3 := by
        rw [hzpres]; simp [OmegaIntCoord.val]
      have hzNorm : star z * z = 1 := by
        have hu := rsOmegaAlg_pow_unit 3
        rw [hzval]
        have : star (-rsOmegaAlg ^ 3) * (-rsOmegaAlg ^ 3) =
            star (rsOmegaAlg ^ 3) * rsOmegaAlg ^ 3 := by
          rw [star_neg]; ring
        rw [this]; exact hu
      have hwZero : w = 0 :=
        eq_zero_of_star_self_eq_zero (by
          have hSt := hState; unfold IsUnitState at hSt
          linear_combination hSt - hzNorm)
      rw [hwZero, hzval]
    · simp [TCount_replicate_omega]

/-! ### Step 2c: `D[ω]` closure under `√2`-multiplication and phase-pair circuit

For the `omegaSDE z = 1` dispatcher we need: `z ∈ D[ω]` ⇒ `z · √2 ∈ D[ω]`, which
turns a half-norm coordinate into a unit phase amenable to
`dyadic_unit_phase_is_omega_pow`. -/

theorem InDyadicCyclotomic.sqrtTwo : InDyadicCyclotomic sqrtTwoComplex := by
  refine ⟨0, 0, 1, 0, 0, ?_⟩
  simp

/-- Circuit witness for the canonical phase-pair state `(ω^a/√2, ω^(a+m)/√2)`. -/
theorem cliffordT_circuit_phase_pair (a m : ℕ) :
    CliffordTCircuit.eval
        (List.replicate a RossSelingerPrimitive.omega ++
         List.replicate m RossSelingerPrimitive.t ++
         [RossSelingerPrimitive.h]) *
      ket0Column =
        stateColumn (rsOmegaAlg ^ a / sqrtTwoComplex)
          (rsOmegaAlg ^ (a + m) / sqrtTwoComplex) := by
  rw [CliffordTCircuit.eval_append, CliffordTCircuit.eval_append]
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  have hH :
      CliffordTCircuit.eval [RossSelingerPrimitive.h] * ket0Column =
        stateColumn (1 / sqrtTwoComplex) (1 / sqrtTwoComplex) := by
    rw [ket0Column_eq_stateColumn]
    simp [CliffordTCircuit.eval, RossSelingerPrimitive.eval, hadamard2_stateColumn]
  rw [hH, eval_replicate_t_stateColumn, eval_replicate_omega_stateColumn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stateColumn, pow_add] <;> ring

/-- Generic phase-pair dispatch: any unit state `(z, w)` with `z = ω^a/√2`
admits a Clifford+T preparation circuit, with `w` automatically also of the form
`ω^b/√2` by the unit-state equation. -/
theorem unit_state_phase_over_sqrtTwo_has_circuit
    {z w : ℂ} {a : ℕ}
    (hz : z = rsOmegaAlg ^ a / sqrtTwoComplex)
    (hwDyadic : InDyadicCyclotomic w)
    (hState : IsUnitState z w) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w := by
  -- |z|² = 1/2; hence |w|² = 1/2; hence (w · √2) is a unit phase.
  have hsstar : star sqrtTwoComplex = sqrtTwoComplex := by simp [sqrtTwoComplex]
  have hsq : sqrtTwoComplex * sqrtTwoComplex = 2 := sqrtTwoComplex_mul_self
  have hs_ne : sqrtTwoComplex ≠ 0 := sqrtTwoComplex_ne_zero
  have hu : star (rsOmegaAlg ^ a) * (rsOmegaAlg ^ a) = 1 := rsOmegaAlg_pow_unit a
  have hzNorm : star z * z = 1 / 2 := by
    rw [hz]
    rw [star_div₀, hsstar, div_mul_div_comm, hu, hsq]
  have hwsqrt2_norm : star (w * sqrtTwoComplex) * (w * sqrtTwoComplex) = 1 := by
    have hSt := hState; unfold IsUnitState at hSt
    have hwNorm : star w * w = 1 / 2 := by linear_combination hSt - hzNorm
    have h0 : star (w * sqrtTwoComplex) * (w * sqrtTwoComplex) =
        (star w * w) * (sqrtTwoComplex * sqrtTwoComplex) := by
      rw [star_mul, hsstar]; ring
    rw [h0, hwNorm, hsq]
    norm_num
  have hwsqrt2_dyadic : InDyadicCyclotomic (w * sqrtTwoComplex) :=
    InDyadicCyclotomic.mul hwDyadic InDyadicCyclotomic.sqrtTwo
  rcases dyadic_unit_phase_is_omega_pow hwsqrt2_dyadic hwsqrt2_norm with ⟨b, hb⟩
  have hw : w = rsOmegaAlg ^ (b : ℕ) / sqrtTwoComplex := by
    have hs : sqrtTwoComplex ≠ 0 := sqrtTwoComplex_ne_zero
    field_simp [hs]
    linear_combination hb
  -- Pick m := b + 7a + 8.  Then a + m = 8(a+1) + b, so ω^(a + m) = ω^b
  -- (using ω^8 = 1).  This formula is positive for all a ∈ ℕ.
  refine ⟨List.replicate a RossSelingerPrimitive.omega ++
          List.replicate ((b : ℕ) + 7 * a + 8) RossSelingerPrimitive.t ++
          [RossSelingerPrimitive.h], ?_⟩
  rw [cliffordT_circuit_phase_pair]
  rw [hz, hw]
  congr 1
  have heq : a + ((b : ℕ) + 7 * a + 8) = 8 * (a + 1) + (b : ℕ) := by ring
  rw [heq, pow_add, pow_mul, rsOmegaAlg_eight, one_pow, one_mul]

/-- T-count bounded variant of `unit_state_phase_over_sqrtTwo_has_circuit`
for the eight phase-pair cases used by the low-SDE table.  The old
implementation spent a full residue cycle of `T`s; this version chooses the
phase difference modulo `8`, so the `T` cost is at most seven. -/
theorem unit_state_phase_over_sqrtTwo_has_circuit_tcount
    {z w : ℂ} {a : ℕ}
    (ha : a ≤ 7)
    (hz : z = rsOmegaAlg ^ a / sqrtTwoComplex)
    (hwDyadic : InDyadicCyclotomic w)
  (hState : IsUnitState z w) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w ∧
        TCount C ≤ 7 := by
  have hsstar : star sqrtTwoComplex = sqrtTwoComplex := by simp [sqrtTwoComplex]
  have hsq : sqrtTwoComplex * sqrtTwoComplex = 2 := sqrtTwoComplex_mul_self
  have hu : star (rsOmegaAlg ^ a) * (rsOmegaAlg ^ a) = 1 := rsOmegaAlg_pow_unit a
  have hzNorm : star z * z = 1 / 2 := by
    rw [hz]
    rw [star_div₀, hsstar, div_mul_div_comm, hu, hsq]
  have hwsqrt2_norm : star (w * sqrtTwoComplex) * (w * sqrtTwoComplex) = 1 := by
    have hSt := hState; unfold IsUnitState at hSt
    have hwNorm : star w * w = 1 / 2 := by linear_combination hSt - hzNorm
    have h0 : star (w * sqrtTwoComplex) * (w * sqrtTwoComplex) =
        (star w * w) * (sqrtTwoComplex * sqrtTwoComplex) := by
      rw [star_mul, hsstar]; ring
    rw [h0, hwNorm, hsq]
    norm_num
  have hwsqrt2_dyadic : InDyadicCyclotomic (w * sqrtTwoComplex) :=
    InDyadicCyclotomic.mul hwDyadic InDyadicCyclotomic.sqrtTwo
  rcases dyadic_unit_phase_is_omega_pow hwsqrt2_dyadic hwsqrt2_norm with ⟨b, hb⟩
  have hw : w = rsOmegaAlg ^ (b : ℕ) / sqrtTwoComplex := by
    have hs : sqrtTwoComplex ≠ 0 := sqrtTwoComplex_ne_zero
    field_simp [hs]
    linear_combination hb
  let m : ℕ := ((b : ℕ) + 8 - a) % 8
  let C : CliffordTCircuit :=
    List.replicate a RossSelingerPrimitive.omega ++
      List.replicate m RossSelingerPrimitive.t ++
      [RossSelingerPrimitive.h]
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    rw [cliffordT_circuit_phase_pair]
    rw [hz, hw]
    congr 1
    have hmod : (a + m) % 8 = (b : ℕ) % 8 := by
      dsimp [m]
      have hb : (b : ℕ) ≤ 7 := Nat.le_of_lt_succ b.2
      omega
    exact congrArg (fun q : ℂ => q / sqrtTwoComplex)
      (rsOmegaAlg_pow_eq_of_mod_eq hmod)
  · dsimp [C]
    rw [TCount_append, TCount_append, TCount_replicate_omega,
      TCount_replicate_t]
    simp
    have hm : m < 8 := by
      dsimp [m]
      exact Nat.mod_lt _ (by norm_num)
    omega

/-! ### Step 4: `omegaSDE z = 1, P x = 1` dispatcher

When the omega-coordinate sum of squares equals 1, `z = val(x)/√2` is one of
eight `ω^k/√2` values.  Each dispatches to a phase-pair circuit. -/

theorem unit_state_omegaSDE_one_P_one_has_circuit
    {z w : ℂ} {x : OmegaIntCoord}
    (hzpres : z = OmegaIntCoord.val x / sqrtTwoComplex)
    (hwDyadic : InDyadicCyclotomic w)
    (hwOmegaDyadic : InOmegaDyadicCyclotomic w)
    (hState : IsUnitState z w)
    (hP_one : OmegaIntCoord.P x = 1) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w := by
  have hcoord_range :=
    unit_state_omegaSDE_one_coords_in_range hzpres hwOmegaDyadic hState
  rcases hcoord_range with ⟨⟨h0lo, h0hi⟩, ⟨h1lo, h1hi⟩, ⟨h2lo, h2hi⟩, ⟨h3lo, h3hi⟩⟩
  cases x with
  | mk a b c d =>
    unfold OmegaIntCoord.P at hP_one
    -- Each x_i ∈ {-1, 0, 1} and the sum of squares = 1; exactly one is ±1.
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
      first
      | -- Contradiction branch: P ≠ 1 (73 of 81 tuples).
        (exfalso
         simp only [show (-1 : ℤ) ^ 2 = 1 from by norm_num,
                    show (0 : ℤ) ^ 2 = 0 from by norm_num,
                    show (1 : ℤ) ^ 2 = 1 from by norm_num] at hP_one
         omega)
      | -- ⟨1, 0, 0, 0⟩ : z = 1 = ω^0 / √2.
        (exact unit_state_phase_over_sqrtTwo_has_circuit (a := 0)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨1, 0, 0, 0⟩) = 1 by
              unfold OmegaIntCoord.val; ring]; ring) hwDyadic hState)
      | -- ⟨-1, 0, 0, 0⟩ : z = -1/√2 = ω^4/√2.
        (exact unit_state_phase_over_sqrtTwo_has_circuit (a := 4)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨-1, 0, 0, 0⟩) = -1 by
              unfold OmegaIntCoord.val; ring];
              rw [show (rsOmegaAlg : ℂ) ^ 4 = (-1 : ℂ) from rsOmegaAlg_pow_four]) hwDyadic hState)
      | -- ⟨0, 1, 0, 0⟩ : z = ω/√2 = ω^1/√2.
        (exact unit_state_phase_over_sqrtTwo_has_circuit (a := 1)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨0, 1, 0, 0⟩) = rsOmegaAlg by
              unfold OmegaIntCoord.val; ring]; rw [pow_one]) hwDyadic hState)
      | -- ⟨0, -1, 0, 0⟩ : z = -ω/√2 = ω^5/√2.
        (exact unit_state_phase_over_sqrtTwo_has_circuit (a := 5)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨0, -1, 0, 0⟩) = -rsOmegaAlg by
              unfold OmegaIntCoord.val; ring];
              rw [show rsOmegaAlg ^ 5 = -rsOmegaAlg from rsOmegaAlg_five]) hwDyadic hState)
      | -- ⟨0, 0, 1, 0⟩ : z = ω²/√2.
        (exact unit_state_phase_over_sqrtTwo_has_circuit (a := 2)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨0, 0, 1, 0⟩) = rsOmegaAlg ^ 2 by
              unfold OmegaIntCoord.val; ring]) hwDyadic hState)
      | -- ⟨0, 0, -1, 0⟩ : z = -ω²/√2 = ω^6/√2.
        (exact unit_state_phase_over_sqrtTwo_has_circuit (a := 6)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨0, 0, -1, 0⟩) = -rsOmegaAlg ^ 2 by
              unfold OmegaIntCoord.val; ring];
              rw [show rsOmegaAlg ^ 6 = -rsOmegaAlg ^ 2 from rsOmegaAlg_six]) hwDyadic hState)
      | -- ⟨0, 0, 0, 1⟩ : z = ω³/√2.
        (exact unit_state_phase_over_sqrtTwo_has_circuit (a := 3)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨0, 0, 0, 1⟩) = rsOmegaAlg ^ 3 by
              unfold OmegaIntCoord.val; ring]) hwDyadic hState)
      | -- ⟨0, 0, 0, -1⟩ : z = -ω³/√2 = ω^7/√2.
        (exact unit_state_phase_over_sqrtTwo_has_circuit (a := 7)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨0, 0, 0, -1⟩) = -rsOmegaAlg ^ 3 by
              unfold OmegaIntCoord.val; ring];
              rw [show rsOmegaAlg ^ 7 = -rsOmegaAlg ^ 3 from rsOmegaAlg_seven]) hwDyadic hState)

/-- T-count bounded variant of `unit_state_omegaSDE_one_P_one_has_circuit`. -/
theorem unit_state_omegaSDE_one_P_one_has_circuit_tcount
    {z w : ℂ} {x : OmegaIntCoord}
    (hzpres : z = OmegaIntCoord.val x / sqrtTwoComplex)
    (hwDyadic : InDyadicCyclotomic w)
    (hwOmegaDyadic : InOmegaDyadicCyclotomic w)
    (hState : IsUnitState z w)
  (hP_one : OmegaIntCoord.P x = 1) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w ∧
        TCount C ≤ 7 := by
  have hcoord_range :=
    unit_state_omegaSDE_one_coords_in_range hzpres hwOmegaDyadic hState
  rcases hcoord_range with ⟨⟨h0lo, h0hi⟩, ⟨h1lo, h1hi⟩, ⟨h2lo, h2hi⟩, ⟨h3lo, h3hi⟩⟩
  cases x with
  | mk a b c d =>
    unfold OmegaIntCoord.P at hP_one
    interval_cases a <;> interval_cases b <;> interval_cases c <;>
      interval_cases d <;>
      first
      | (exfalso
         simp only [show (-1 : ℤ) ^ 2 = 1 from by norm_num,
                    show (0 : ℤ) ^ 2 = 0 from by norm_num,
                    show (1 : ℤ) ^ 2 = 1 from by norm_num] at hP_one
         omega)
      | (exact unit_state_phase_over_sqrtTwo_has_circuit_tcount (a := 0) (by omega)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨1, 0, 0, 0⟩) = 1 by
              unfold OmegaIntCoord.val; ring]; ring) hwDyadic hState)
      | (exact unit_state_phase_over_sqrtTwo_has_circuit_tcount (a := 4) (by omega)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨-1, 0, 0, 0⟩) = -1 by
              unfold OmegaIntCoord.val; ring];
              rw [show (rsOmegaAlg : ℂ) ^ 4 = (-1 : ℂ) from rsOmegaAlg_pow_four]) hwDyadic hState)
      | (exact unit_state_phase_over_sqrtTwo_has_circuit_tcount (a := 1) (by omega)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨0, 1, 0, 0⟩) = rsOmegaAlg by
              unfold OmegaIntCoord.val; ring]; rw [pow_one]) hwDyadic hState)
      | (exact unit_state_phase_over_sqrtTwo_has_circuit_tcount (a := 5) (by omega)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨0, -1, 0, 0⟩) = -rsOmegaAlg by
              unfold OmegaIntCoord.val; ring];
              rw [show rsOmegaAlg ^ 5 = -rsOmegaAlg from rsOmegaAlg_five]) hwDyadic hState)
      | (exact unit_state_phase_over_sqrtTwo_has_circuit_tcount (a := 2) (by omega)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨0, 0, 1, 0⟩) = rsOmegaAlg ^ 2 by
              unfold OmegaIntCoord.val; ring]) hwDyadic hState)
      | (exact unit_state_phase_over_sqrtTwo_has_circuit_tcount (a := 6) (by omega)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨0, 0, -1, 0⟩) = -rsOmegaAlg ^ 2 by
              unfold OmegaIntCoord.val; ring];
              rw [show rsOmegaAlg ^ 6 = -rsOmegaAlg ^ 2 from rsOmegaAlg_six]) hwDyadic hState)
      | (exact unit_state_phase_over_sqrtTwo_has_circuit_tcount (a := 3) (by omega)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨0, 0, 0, 1⟩) = rsOmegaAlg ^ 3 by
              unfold OmegaIntCoord.val; ring]) hwDyadic hState)
      | (exact unit_state_phase_over_sqrtTwo_has_circuit_tcount (a := 7) (by omega)
          (by rw [hzpres, show (OmegaIntCoord.val ⟨0, 0, 0, -1⟩) = -rsOmegaAlg ^ 3 by
              unfold OmegaIntCoord.val; ring];
              rw [show rsOmegaAlg ^ 7 = -rsOmegaAlg ^ 3 from rsOmegaAlg_seven]) hwDyadic hState)

private theorem rossSelingerPrimitive_eval_mem_unitaryGroup
    (gate : RossSelingerPrimitive) :
    RossSelingerPrimitive.eval gate ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  cases gate
  · exact TwoControl.Clifford.Universal.hadamard2_mem_unitaryGroup
  · exact TwoControl.Clifford.Universal.phaseS_mem_unitaryGroup
  · exact TwoControl.Clifford.Universal.phaseT_mem_unitaryGroup
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [RossSelingerPrimitive.eval, Matrix.mul_apply, Fin.sum_univ_two,
        phaseT_scalar_eq_rsOmegaAlg]
    all_goals exact rsOmegaAlg_unit

private theorem cliffordTCircuit_eval_mem_unitaryGroup
    (C : CliffordTCircuit) :
    CliffordTCircuit.eval C ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  induction C with
  | nil =>
      exact Submonoid.one_mem (Matrix.unitaryGroup (Fin 2) ℂ)
  | cons gate gates ih =>
      simpa [CliffordTCircuit.eval] using
        (Submonoid.mul_mem (Matrix.unitaryGroup (Fin 2) ℂ)
          (rossSelingerPrimitive_eval_mem_unitaryGroup gate) ih)

private theorem MatrixEntriesInDyadicCyclotomic.mul
    {A B : Square 2}
    (hA : MatrixEntriesInDyadicCyclotomic A)
    (hB : MatrixEntriesInDyadicCyclotomic B) :
    MatrixEntriesInDyadicCyclotomic (A * B) := by
  intro i j
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  exact InDyadicCyclotomic.add
    (InDyadicCyclotomic.mul (hA i 0) (hB 0 j))
    (InDyadicCyclotomic.mul (hA i 1) (hB 1 j))

private theorem MatrixEntriesInDyadicCyclotomic.conjTranspose
    {A : Square 2}
    (hA : MatrixEntriesInDyadicCyclotomic A) :
    MatrixEntriesInDyadicCyclotomic A† := by
  intro i j
  simpa [Matrix.conjTranspose_apply] using InDyadicCyclotomic.star (hA j i)

private theorem rossSelingerPrimitive_eval_entries
    (gate : RossSelingerPrimitive) :
    MatrixEntriesInDyadicCyclotomic (RossSelingerPrimitive.eval gate) := by
  intro i j
  cases gate <;> fin_cases i <;> fin_cases j
  · simpa [RossSelingerPrimitive.eval, hadamard2, sqrtTwoComplex, div_eq_mul_inv]
      using InDyadicCyclotomic.div_sqrtTwo InDyadicCyclotomic.one
  · simpa [RossSelingerPrimitive.eval, hadamard2, sqrtTwoComplex, div_eq_mul_inv]
      using InDyadicCyclotomic.div_sqrtTwo InDyadicCyclotomic.one
  · simpa [RossSelingerPrimitive.eval, hadamard2, sqrtTwoComplex, div_eq_mul_inv]
      using InDyadicCyclotomic.div_sqrtTwo InDyadicCyclotomic.one
  · simpa [RossSelingerPrimitive.eval, hadamard2, sqrtTwoComplex, div_eq_mul_inv]
      using InDyadicCyclotomic.neg
        (InDyadicCyclotomic.div_sqrtTwo InDyadicCyclotomic.one)
  · simpa [RossSelingerPrimitive.eval, phaseS, diag2] using InDyadicCyclotomic.one
  · simpa [RossSelingerPrimitive.eval, phaseS, diag2] using InDyadicCyclotomic.zero
  · simpa [RossSelingerPrimitive.eval, phaseS, diag2] using InDyadicCyclotomic.zero
  · refine ⟨0, 0, 0, 1, 0, ?_⟩
    simp [RossSelingerPrimitive.eval, phaseS, diag2, sqrtTwoComplex]
  · simpa [RossSelingerPrimitive.eval, phaseT, diag2] using InDyadicCyclotomic.one
  · simpa [RossSelingerPrimitive.eval, phaseT, diag2] using InDyadicCyclotomic.zero
  · simpa [RossSelingerPrimitive.eval, phaseT, diag2] using InDyadicCyclotomic.zero
  · simpa [RossSelingerPrimitive.eval, phaseT, diag2, phaseT_scalar_eq_rsOmegaAlg]
      using rsOmegaAlg_in_dyadic
  · simpa [RossSelingerPrimitive.eval, phaseT_scalar_eq_rsOmegaAlg]
      using rsOmegaAlg_in_dyadic
  · simpa [RossSelingerPrimitive.eval] using InDyadicCyclotomic.zero
  · simpa [RossSelingerPrimitive.eval] using InDyadicCyclotomic.zero
  · simpa [RossSelingerPrimitive.eval, phaseT_scalar_eq_rsOmegaAlg]
      using rsOmegaAlg_in_dyadic

private theorem cliffordTCircuit_eval_entries
    (C : CliffordTCircuit) :
    MatrixEntriesInDyadicCyclotomic (CliffordTCircuit.eval C) := by
  induction C with
  | nil =>
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [CliffordTCircuit.eval, InDyadicCyclotomic.zero, InDyadicCyclotomic.one]
  | cons gate gates ih =>
      simpa [CliffordTCircuit.eval] using
        MatrixEntriesInDyadicCyclotomic.mul
          (rossSelingerPrimitive_eval_entries gate) ih

private theorem residual_phase_in_dyadic
    {U : Square 2}
    (hEntries : MatrixEntriesInDyadicCyclotomic U)
    (C₀ : CliffordTCircuit) :
    InDyadicCyclotomic (((CliffordTCircuit.eval C₀)† * U) 1 1) :=
  MatrixEntriesInDyadicCyclotomic.mul
    (MatrixEntriesInDyadicCyclotomic.conjTranspose
      (cliffordTCircuit_eval_entries C₀))
    hEntries 1 1

private theorem matrix_eq_mul_conjTranspose_mul_of_unitary
    {A U : Square 2}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    A * (A† * U) = U := by
  have hAA : A * A† = (1 : Square 2) := Matrix.mem_unitaryGroup_iff.mp hA
  calc
    A * (A† * U) = (A * A†) * U := by rw [Matrix.mul_assoc]
    _ = U := by rw [hAA, Matrix.one_mul]

/-- Remaining structural phase-correction bridge for KMM unitary synthesis.

After preparing the first column of `U`, the residual unitary fixes `|0⟩`;
`unitary_fixing_ket0_is_diagonal_phase` reduces it to a diagonal phase, and
`dyadic_unit_phase_is_omega_pow` plus `diagonal_omega_pow_exact` should supply
the final exact circuit. The missing work here is packaging those ingredients
through the concrete circuit composition/evaluation API. -/
theorem kmm_unitary_implementation_phase_correction
    {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hEntries : MatrixEntriesInDyadicCyclotomic U)
    (C₀ : CliffordTCircuit)
    (hC₀ : CliffordTCircuit.eval C₀ * ket0Column =
      stateColumn (U 0 0) (U 1 0)) :
    ∃ C : CliffordTCircuit, CliffordTCircuit.eval C = U := by
  let A : Square 2 := CliffordTCircuit.eval C₀
  let W : Square 2 := A† * U
  have hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    simpa [A] using cliffordTCircuit_eval_mem_unitaryGroup C₀
  have hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    exact Submonoid.mul_mem (Matrix.unitaryGroup (Fin 2) ℂ)
      (TwoControl.conjTranspose_mem_unitaryGroup hA) hU
  have hUket : U * ket0Column = stateColumn (U 0 0) (U 1 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ket0Column, stateColumn, Matrix.mul_apply, Fin.sum_univ_two]
  have hFix : W * ket0Column = ket0Column := by
    calc
      W * ket0Column = A† * (U * ket0Column) := by
        simp [W, A, Matrix.mul_assoc]
      _ = A† * (A * ket0Column) := by
        rw [hUket, ← hC₀]
      _ = (A† * A) * ket0Column := by rw [Matrix.mul_assoc]
      _ = ket0Column := by
        have hAA : A† * A = (1 : Square 2) := Matrix.mem_unitaryGroup_iff'.mp hA
        rw [hAA, Matrix.one_mul]
  rcases unitary_fixing_ket0_is_diagonal_phase hW hFix with ⟨α, hαNorm, hWdiag⟩
  have hαDyadic : InDyadicCyclotomic α := by
    have hres : InDyadicCyclotomic (W 1 1) := by
      simpa [W, A] using residual_phase_in_dyadic hEntries C₀
    have hα : α = W 1 1 := by
      have h := congr_fun (congr_fun hWdiag 1) 1
      simpa using h.symm
    simpa [hα]
  rcases dyadic_unit_phase_is_omega_pow hαDyadic hαNorm with ⟨m, hm⟩
  rcases diagonal_omega_pow_exact m with ⟨Cphase, hCphase⟩
  refine ⟨C₀ ++ Cphase, ?_⟩
  rw [CliffordTCircuit.eval_append, hCphase]
  calc
    A * Matrix.of ![![(1 : ℂ), 0], ![0, rsOmegaAlg ^ (m : ℕ)]]
        = A * W := by
            rw [hWdiag, hm]
    _ = U := by
        simpa [W] using matrix_eq_mul_conjTranspose_mul_of_unitary (A := A) (U := U) hA

/-- T-count-carrying version of KMM's final phase correction.

Once a circuit prepares the first column of `U`, the remaining diagonal dyadic
unit phase is some `ω^m`, hence costs at most seven `T` gates. -/
theorem kmm_unitary_implementation_phase_correction_tcount
    {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hEntries : MatrixEntriesInDyadicCyclotomic U)
    (C₀ : CliffordTCircuit)
    (hC₀ : CliffordTCircuit.eval C₀ * ket0Column =
      stateColumn (U 0 0) (U 1 0)) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C = U ∧
        TCount C ≤ TCount C₀ + 7 := by
  let A : Square 2 := CliffordTCircuit.eval C₀
  let W : Square 2 := A† * U
  have hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    simpa [A] using cliffordTCircuit_eval_mem_unitaryGroup C₀
  have hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    exact Submonoid.mul_mem (Matrix.unitaryGroup (Fin 2) ℂ)
      (TwoControl.conjTranspose_mem_unitaryGroup hA) hU
  have hUket : U * ket0Column = stateColumn (U 0 0) (U 1 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ket0Column, stateColumn, Matrix.mul_apply, Fin.sum_univ_two]
  have hFix : W * ket0Column = ket0Column := by
    calc
      W * ket0Column = A† * (U * ket0Column) := by
        simp [W, A, Matrix.mul_assoc]
      _ = A† * (A * ket0Column) := by
        rw [hUket, ← hC₀]
      _ = (A† * A) * ket0Column := by rw [Matrix.mul_assoc]
      _ = ket0Column := by
        have hAA : A† * A = (1 : Square 2) := Matrix.mem_unitaryGroup_iff'.mp hA
        rw [hAA, Matrix.one_mul]
  rcases unitary_fixing_ket0_is_diagonal_phase hW hFix with ⟨α, hαNorm, hWdiag⟩
  have hαDyadic : InDyadicCyclotomic α := by
    have hres : InDyadicCyclotomic (W 1 1) := by
      simpa [W, A] using residual_phase_in_dyadic hEntries C₀
    have hα : α = W 1 1 := by
      have h := congr_fun (congr_fun hWdiag 1) 1
      simpa using h.symm
    simpa [hα]
  rcases dyadic_unit_phase_is_omega_pow hαDyadic hαNorm with ⟨m, hm⟩
  rcases diagonal_omega_pow_exact_tcount m with ⟨Cphase, hCphase, hTphase⟩
  refine ⟨C₀ ++ Cphase, ?_, ?_⟩
  · rw [CliffordTCircuit.eval_append, hCphase]
    calc
      A * Matrix.of ![![(1 : ℂ), 0], ![0, rsOmegaAlg ^ (m : ℕ)]]
          = A * W := by
              rw [hWdiag, hm]
      _ = U := by
          simpa [W] using matrix_eq_mul_conjTranspose_mul_of_unitary (A := A) (U := U) hA
  · rw [TCount_append]
    exact Nat.add_le_add_left hTphase (TCount C₀)

set_option maxHeartbeats 800000 in
/-- For `DenNormSDE z ∈ {3, 4}` (i.e. `omegaSDE z = 2`), there exists a gate
`H T^k` that strictly lowers `DenNormSDE z`.  This is the analogue of
`kmm_exists_reducing_k` for the low-SDE range that falls outside the standard
`r ≥ 3` hypothesis of the descent machinery. -/
private theorem kmm_exists_reducing_k_sde34
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w)
    (hLow : DenNormSDE z ≤ 4)
    (hHigh : 3 ≤ DenNormSDE z) :
    ∃ k : Fin 4,
      StateEntriesInDyadicCyclotomic (applyHTPowToState k z w).1 (applyHTPowToState k z w).2 ∧
      IsUnitState (applyHTPowToState k z w).1 (applyHTPowToState k z w).2 ∧
      DenNormSDE (applyHTPowToState k z w).1 < DenNormSDE z := by
  -- Step 1: Get minimal omega presentation of z
  rcases hEntries.1 with ⟨nz, a, b, c, d, hzleg⟩
  rcases omegaSDE_presentation_of_legacy_coordinate
    (by simpa [cyclotomicIntegerCoord] using hzleg) with ⟨x, hxpres⟩
  -- Step 2: r := omegaSDE z ≤ 2; interval_cases shows only r=2 is consistent with hHigh
  have hrle2 : omegaSDE z ≤ 2 := omegaSDE_le_two_of_denNormSDE_le_four hEntries.1 hLow
  set r := omegaSDE z with hr_def
  -- After `set`, hxpres : z = val(x) / √2^r
  interval_cases r
  · -- r = 0: DenNormSDE z ≤ 0, contradicts hHigh
    have hden0 : HasDenominatorExponent (star z * z) 0 :=
      hasDenominatorExponent_starzz_le_of_normPairDvd (j := 0) hxpres (Nat.zero_le _)
        (normPairSqrtTwoPowDivides_zero _ _)
    have hle0 : DenNormSDE z ≤ 0 := by unfold DenNormSDE; exact sde_le_of_hasDenominatorExponent hden0
    omega
  · -- r = 1: DenNormSDE z ≤ 2, contradicts hHigh
    have hden2 : HasDenominatorExponent (star z * z) 2 :=
      hasDenominatorExponent_starzz_le_of_normPairDvd (j := 0) hxpres (Nat.zero_le _)
        (normPairSqrtTwoPowDivides_zero _ _)
    have hle2 : DenNormSDE z ≤ 2 := by unfold DenNormSDE; exact sde_le_of_hasDenominatorExponent hden2
    omega
  · -- r = 2: the interesting case; hxpres : z = val(x) / √2^2
    have hxpres2 : z = OmegaIntCoord.val x / sqrtTwoComplex ^ 2 := hxpres
    -- Step 3: Get w at omega level ≤ 2
    have hwO : InOmegaDyadicCyclotomic w := by
      rcases hEntries.2 with ⟨nw, ew, fw, gw, hw, hwleg⟩
      exact ⟨nw, hasOmegaDenominatorExponent_of_hasDenominatorExponent
        ⟨ew, fw, gw, hw, by simpa [cyclotomicIntegerCoord] using hwleg⟩⟩
    have hwle2 : omegaSDE w ≤ 2 :=
      omegaSDE_w_le_two_of_denNormSDE_z_le_four hxpres2 hr_def.symm hwO hState
    -- Step 4: Lift w to level 2
    rcases hasOmegaDenominatorExponent_of_inOmegaDyadicCyclotomic hwO with ⟨y_min, hy_min⟩
    let y := OmegaIntCoord.sqrtTwoPowMul (2 - omegaSDE w) y_min
    have hypres : w = OmegaIntCoord.val y / sqrtTwoComplex ^ 2 := by
      have := lift_omega_pres_up (d := 2 - omegaSDE w) hy_min
      rwa [show omegaSDE w + (2 - omegaSDE w) = 2 from by omega] at this
    -- Step 5: Residue facts at level 2  (P + P' = 4, Q + Q' = 0 in ZMod 8)
    rcases normalized_state_residue_compat_at_two hxpres2 hypres hState with ⟨hP4, hQ0⟩
    -- Step 6: Minimality of x: not √2-divisible
    have hxNotDvd := OmegaIntCoord.sqrtTwoGDE_zero_not_sqrtTwo_dvd
      (sqrtTwoGDE_zero_of_minimal_omega_denominator_pos hxpres hr_def.symm (by omega))
    have h_not_dvd2 := not_normPairSqrtTwoPowDivides_two_of_not_sqrtTwo_dvd x hxNotDvd
    -- Step 7: Case split on j = 0 (P x odd) vs j = 1 (P x even)
    by_cases hPxEven : Even (OmegaIntCoord.P x)
    · -- j = 1 case: DenNormSDE z = 3
      have hQxNotEven : ¬ Even (OmegaIntCoord.Q x) := fun hQ =>
        h_not_dvd2 ((normPairSqrtTwoPowDivides_two_iff _ _).mpr ⟨hPxEven, hQ⟩)
      have hj1 : OmegaResidue.normGDEEq 1 (OmegaResidue.ofIntCoord x) = true := by
        rw [OmegaResidue.normGDEEq, OmegaResidue.P_ofIntCoord, OmegaResidue.Q_ofIntCoord]
        have : ∀ A B : ZMod 8, A.val % 2 = 0 → B.val % 2 = 1 →
            OmegaResidue.sqrtTwoGDEEqPair 1 A B = true := by decide
        exact this _ _ (zmod8_val_even_of_even_int _ hPxEven) (zmod8_val_odd_of_odd_int _ hQxNotEven)
      have hj1w : OmegaResidue.normGDEEq 1 (OmegaResidue.ofIntCoord y) = true :=
        OmegaResidue.normGDEEq_of_four_minus_pair (Or.inr rfl) hj1 hP4 hQ0
      have hDenNormZ3 : DenNormSDE z = 3 := by
        have hgde : NormPairSqrtTwoGDE (OmegaIntCoord.P x) (OmegaIntCoord.Q x) 1 :=
          ⟨(normPairSqrtTwoPowDivides_one_iff _ _).mpr hPxEven, h_not_dvd2⟩
        exact denNormSDE_eq_two_r_sub_j_of_normPairGDE hxpres2 hEntries.1 hgde (by omega)
      -- sde3_descent_choice gives k with GDE ≥ 4 = GDEEq 4
      rcases sde3_descent_choice hj1 hj1w hP4 hQ0 with ⟨k, hk⟩
      -- GDEGePair 4 = GDEEqPair 4 by definition of sqrtTwoGDEEqPair
      have hkEq : OmegaResidue.sqrtTwoGDEEqPair 4
          (OmegaResidue.P (OmegaResidue.transformed (k : ℕ)
            (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y)))
          (OmegaResidue.Q (OmegaResidue.transformed (k : ℕ)
            (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y)))
          = true := by simp [OmegaResidue.sqrtTwoGDEEqPair, hk]
      have hDen := hasDenominatorExponent_of_common_omega_choice_ge_three
        (n := 4) (r := 2) (target := 2) (by omega) (by omega) (by omega)
        k x y hxpres2 hypres rfl hkEq
      refine ⟨k, applyHTPowToState_entries hEntries k, applyHTPowToState_unit hState k, ?_⟩
      unfold DenNormSDE
      rw [applyHTPowToState_norm_formula]
      have hlt : sde _ ≤ 2 := sde_le_of_hasDenominatorExponent hDen
      unfold DenNormSDE at hDenNormZ3; omega
    · -- j = 0 case: DenNormSDE z = 4
      have hj0 : OmegaResidue.normGDEEq 0 (OmegaResidue.ofIntCoord x) = true := by
        rw [OmegaResidue.normGDEEq, OmegaResidue.P_ofIntCoord, OmegaResidue.Q_ofIntCoord]
        have : ∀ A B : ZMod 8, A.val % 2 = 1 →
            OmegaResidue.sqrtTwoGDEEqPair 0 A B = true := by decide
        exact this _ _ (zmod8_val_odd_of_odd_int _ hPxEven)
      have hj0w : OmegaResidue.normGDEEq 0 (OmegaResidue.ofIntCoord y) = true :=
        OmegaResidue.normGDEEq_of_four_minus_pair (Or.inl rfl) hj0 hP4 hQ0
      have hDenNormZ4 : DenNormSDE z = 4 := by
        have hgde : NormPairSqrtTwoGDE (OmegaIntCoord.P x) (OmegaIntCoord.Q x) 0 :=
          ⟨normPairSqrtTwoPowDivides_zero _ _,
            fun h => hPxEven ((normPairSqrtTwoPowDivides_one_iff _ _).mp h)⟩
        exact denNormSDE_eq_two_r_sub_j_of_normPairGDE hxpres2 hEntries.1 hgde (by omega)
      -- sde4_descent_choice gives k with GDE ≥ 3
      rcases sde4_descent_choice hj0 hj0w hP4 hQ0 with ⟨k, hk⟩
      -- Split GDEGePair 3 into GDEEqPair 4 or GDEEqPair 3
      have hkSplit :
          OmegaResidue.sqrtTwoGDEEqPair 4
            (OmegaResidue.P (OmegaResidue.transformed (k : ℕ)
              (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y)))
            (OmegaResidue.Q (OmegaResidue.transformed (k : ℕ)
              (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y)))
            = true ∨
          OmegaResidue.sqrtTwoGDEEqPair 3
            (OmegaResidue.P (OmegaResidue.transformed (k : ℕ)
              (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y)))
            (OmegaResidue.Q (OmegaResidue.transformed (k : ℕ)
              (OmegaResidue.ofIntCoord x) (OmegaResidue.ofIntCoord y)))
            = true := by
        have aux : ∀ A B : ZMod 8,
            OmegaResidue.sqrtTwoGDEGePair 3 A B = true →
            OmegaResidue.sqrtTwoGDEEqPair 4 A B = true ∨
            OmegaResidue.sqrtTwoGDEEqPair 3 A B = true := by decide
        exact aux _ _ hk
      rcases hkSplit with h4 | h3
      · -- Use n=4, target=2 < 4 = DenNormSDE z
        have hDen := hasDenominatorExponent_of_common_omega_choice_ge_three
          (n := 4) (r := 2) (target := 2) (by omega) (by omega) (by omega)
          k x y hxpres2 hypres rfl h4
        refine ⟨k, applyHTPowToState_entries hEntries k, applyHTPowToState_unit hState k, ?_⟩
        unfold DenNormSDE
        rw [applyHTPowToState_norm_formula]
        have hlt : sde _ ≤ 2 := sde_le_of_hasDenominatorExponent hDen
        unfold DenNormSDE at hDenNormZ4; omega
      · -- Use n=3, target=3 < 4 = DenNormSDE z
        have hDen := hasDenominatorExponent_of_common_omega_choice_ge_three
          (n := 3) (r := 2) (target := 3) (by omega) (by omega) (by omega)
          k x y hxpres2 hypres rfl h3
        refine ⟨k, applyHTPowToState_entries hEntries k, applyHTPowToState_unit hState k, ?_⟩
        unfold DenNormSDE
        rw [applyHTPowToState_norm_formula]
        have hlt : sde _ ≤ 3 := sde_le_of_hasDenominatorExponent hDen
        unfold DenNormSDE at hDenNormZ4; omega

/-- Full proof of the low-SDE base table, placed after the building-block
theorems it needs.  The bound is now `DenNormSDE z ≤ 2` (cases 3 and 4 are
handled by `kmm_exists_reducing_k_sde34` inside `kmm_state_preparation`). -/
private theorem kmm_low_sde_state_table_complete_impl
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w)
    (hLow : DenNormSDE z ≤ 2) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w := by
  -- Step 1: omega presentation of z at minimal level r = omegaSDE z
  rcases hEntries.1 with ⟨nz, a, b, c, d, hzleg⟩
  rcases omegaSDE_presentation_of_legacy_coordinate
    (by simpa [cyclotomicIntegerCoord] using hzleg) with ⟨x, hxpres⟩
  -- Step 2: omegaSDE z ≤ 2 from DenNormSDE z ≤ 2 (≤ 4 via transitivity)
  have hrle2 : omegaSDE z ≤ 2 :=
    omegaSDE_le_two_of_denNormSDE_le_four hEntries.1 (le_trans hLow (by omega))
  -- Step 3: membership lemmas for w
  have hwDyadic : InDyadicCyclotomic w := hEntries.2
  have hwOmegaDyadic : InOmegaDyadicCyclotomic w := by
    rcases hwDyadic with ⟨nw, ew, fw, gw, hw, hwleg⟩
    exact ⟨nw, hasOmegaDenominatorExponent_of_hasDenominatorExponent
      ⟨ew, fw, gw, hw, by simpa [cyclotomicIntegerCoord] using hwleg⟩⟩
  -- Step 4: case split on r = omegaSDE z ∈ {0, 1, 2}
  set r := omegaSDE z with hr_def
  interval_cases r
  · -- r = 0: z ∈ ℤ[ω]
    have hzpres0 : z = OmegaIntCoord.val x := by simpa using hxpres
    exact unit_state_omegaSDE_zero_has_circuit hzpres0 hwDyadic hwOmegaDyadic hState
  · -- r = 1: z = val(x)/√2
    have hzpres1 : z = OmegaIntCoord.val x / sqrtTwoComplex := by simpa using hxpres
    have hzpres1' : z = OmegaIntCoord.val x / sqrtTwoComplex ^ 1 := by rw [pow_one]; exact hzpres1
    have hPle2 := unit_state_omegaSDE_one_P_le_two hzpres1 hwOmegaDyadic hState
    have hPge0 := omegaIntCoord_P_nonneg x
    -- Case split with explicit named hypotheses (avoids interval_cases substitution issues)
    rcases (show OmegaIntCoord.P x = 0 ∨ OmegaIntCoord.P x = 1 ∨ OmegaIntCoord.P x = 2
              from by omega) with hP0 | hP1 | hP2
    · -- P x = 0: z = 0, contradicts omegaSDE z = 1
      exfalso
      have hval0 : OmegaIntCoord.val x = 0 := by
        cases x with
        | mk a b c d =>
          unfold OmegaIntCoord.P at hP0
          have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
          have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
          have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
          have hd : d = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
          subst ha; subst hb; subst hc; subst hd
          simp [OmegaIntCoord.val]
      rw [hval0] at hzpres1; simp at hzpres1
      have hom0 : omegaSDE z = 0 := by
        have h0 : HasOmegaDenominatorExponent z 0 :=
          ⟨⟨0, 0, 0, 0⟩, by simp [OmegaIntCoord.val, hzpres1]⟩
        exact Nat.le_zero.mp (omegaSDE_le_of_hasOmegaDenominatorExponent h0)
      omega
    · -- P x = 1: circuit via unit_state_omegaSDE_one_P_one_has_circuit
      exact unit_state_omegaSDE_one_P_one_has_circuit
        hzpres1 hwDyadic hwOmegaDyadic hState hP1
    · -- P x = 2: vacuous — no valid unit state in D[ω] × D[ω]
      exfalso
      exact unit_state_omegaSDE_one_P_two_impossible hzpres1' hr_def.symm hP2 hEntries hState
  · -- r = 2: impossible since DenNormSDE z ≤ 2 but at r=2, DenNormSDE z ≥ 3
    exfalso
    have hxpres2 : z = OmegaIntCoord.val x / sqrtTwoComplex ^ 2 := by simpa using hxpres
    have hxNotDvd := OmegaIntCoord.sqrtTwoGDE_zero_not_sqrtTwo_dvd
      (sqrtTwoGDE_zero_of_minimal_omega_denominator_pos hxpres (by omega) (by omega))
    have h_not_dvd2 := not_normPairSqrtTwoPowDivides_two_of_not_sqrtTwo_dvd x hxNotDvd
    by_cases hPxEven : Even (OmegaIntCoord.P x)
    · -- j = 1: DenNormSDE z = 3 > 2
      have hlb := sde_starzz_ge_of_normPairGDE hxpres2 hEntries.1
        ⟨(normPairSqrtTwoPowDivides_one_iff _ _).mpr hPxEven, h_not_dvd2⟩
      unfold DenNormSDE at hLow; omega
    · -- j = 0: DenNormSDE z = 4 > 2
      have hlb := sde_starzz_ge_of_normPairGDE hxpres2 hEntries.1
        ⟨normPairSqrtTwoPowDivides_zero _ _,
          fun h => hPxEven ((normPairSqrtTwoPowDivides_one_iff _ _).mp h)⟩
      unfold DenNormSDE at hLow; omega

/-- T-count bounded version of the low-SDE base table. -/
private theorem kmm_low_sde_state_table_complete_tcount_impl
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w)
    (hLow : DenNormSDE z ≤ 2) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w ∧
        TCount C ≤ 64 := by
  rcases hEntries.1 with ⟨nz, a, b, c, d, hzleg⟩
  rcases omegaSDE_presentation_of_legacy_coordinate
    (by simpa [cyclotomicIntegerCoord] using hzleg) with ⟨x, hxpres⟩
  have hrle2 : omegaSDE z ≤ 2 :=
    omegaSDE_le_two_of_denNormSDE_le_four hEntries.1 (le_trans hLow (by omega))
  have hwDyadic : InDyadicCyclotomic w := hEntries.2
  have hwOmegaDyadic : InOmegaDyadicCyclotomic w := by
    rcases hwDyadic with ⟨nw, ew, fw, gw, hw, hwleg⟩
    exact ⟨nw, hasOmegaDenominatorExponent_of_hasDenominatorExponent
      ⟨ew, fw, gw, hw, by simpa [cyclotomicIntegerCoord] using hwleg⟩⟩
  set r := omegaSDE z with hr_def
  interval_cases r
  · have hzpres0 : z = OmegaIntCoord.val x := by simpa using hxpres
    rcases unit_state_omegaSDE_zero_has_circuit_tcount
        hzpres0 hwDyadic hwOmegaDyadic hState with ⟨C, hC, hT⟩
    exact ⟨C, hC, hT.trans (by omega)⟩
  · have hzpres1 : z = OmegaIntCoord.val x / sqrtTwoComplex := by simpa using hxpres
    have hzpres1' : z = OmegaIntCoord.val x / sqrtTwoComplex ^ 1 := by
      rw [pow_one]
      exact hzpres1
    have hPle2 := unit_state_omegaSDE_one_P_le_two hzpres1 hwOmegaDyadic hState
    have hPge0 := omegaIntCoord_P_nonneg x
    rcases (show OmegaIntCoord.P x = 0 ∨ OmegaIntCoord.P x = 1 ∨ OmegaIntCoord.P x = 2
              from by omega) with hP0 | hP1 | hP2
    · exfalso
      have hval0 : OmegaIntCoord.val x = 0 := by
        cases x with
        | mk a b c d =>
          unfold OmegaIntCoord.P at hP0
          have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
          have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
          have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
          have hd : d = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
          subst ha; subst hb; subst hc; subst hd
          simp [OmegaIntCoord.val]
      rw [hval0] at hzpres1
      simp at hzpres1
      have hom0 : omegaSDE z = 0 := by
        have h0 : HasOmegaDenominatorExponent z 0 :=
          ⟨⟨0, 0, 0, 0⟩, by simp [OmegaIntCoord.val, hzpres1]⟩
        exact Nat.le_zero.mp (omegaSDE_le_of_hasOmegaDenominatorExponent h0)
      omega
    · rcases unit_state_omegaSDE_one_P_one_has_circuit_tcount
        hzpres1 hwDyadic hwOmegaDyadic hState hP1 with ⟨C, hC, hT⟩
      exact ⟨C, hC, by omega⟩
    · exfalso
      exact unit_state_omegaSDE_one_P_two_impossible hzpres1' hr_def.symm hP2 hEntries hState
  · exfalso
    have hxpres2 : z = OmegaIntCoord.val x / sqrtTwoComplex ^ 2 := by simpa using hxpres
    have hxNotDvd := OmegaIntCoord.sqrtTwoGDE_zero_not_sqrtTwo_dvd
      (sqrtTwoGDE_zero_of_minimal_omega_denominator_pos hxpres (by omega) (by omega))
    have h_not_dvd2 := not_normPairSqrtTwoPowDivides_two_of_not_sqrtTwo_dvd x hxNotDvd
    by_cases hPxEven : Even (OmegaIntCoord.P x)
    · have hlb := sde_starzz_ge_of_normPairGDE hxpres2 hEntries.1
        ⟨(normPairSqrtTwoPowDivides_one_iff _ _).mpr hPxEven, h_not_dvd2⟩
      unfold DenNormSDE at hLow
      omega
    · have hlb := sde_starzz_ge_of_normPairGDE hxpres2 hEntries.1
        ⟨normPairSqrtTwoPowDivides_zero _ _,
          fun h => hPxEven ((normPairSqrtTwoPowDivides_one_iff _ _).mp h)⟩
      unfold DenNormSDE at hLow
      omega

/-- KMM state preparation: every normalized state over `D[ω]` can be prepared
from `|0⟩`. -/
theorem kmm_state_preparation
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w := by
  classical
  have hmain :
      ∀ n : ℕ, ∀ z w : ℂ,
        DenNormSDE z = n →
        StateEntriesInDyadicCyclotomic z w →
        IsUnitState z w →
        ∃ C : CliffordTCircuit,
          CliffordTCircuit.eval C * ket0Column = stateColumn z w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro z w hdn hEntries hState
        by_cases hLowN : n ≤ 2
        · exact kmm_low_sde_state_table_complete_impl hEntries hState (by simpa [hdn])
        · by_cases hMedN : n ≤ 4
          · -- n ∈ {3, 4}: use the r=2 descent
            have h3 : 3 ≤ DenNormSDE z := by simpa [hdn] using (by omega : 3 ≤ n)
            have h4 : DenNormSDE z ≤ 4 := by simpa [hdn]
            rcases kmm_exists_reducing_k_sde34 hEntries hState h4 h3 with ⟨k, hEntries', hState', hDec⟩
            have hlt : DenNormSDE (applyHTPowToState k z w).1 < n := by simpa [hdn] using hDec
            rcases ih (DenNormSDE (applyHTPowToState k z w).1) hlt
                (applyHTPowToState k z w).1 (applyHTPowToState k z w).2 rfl hEntries' hState'
              with ⟨C', hC'⟩
            exact kmm_state_preparation_step_from_reduced k rfl rfl hEntries hState hEntries' hState' ⟨C', hC'⟩
          · have hLargeN : 5 ≤ n := by omega
            have hLarge : 5 ≤ DenNormSDE z := by simpa [hdn] using hLargeN
            rcases kmm_exists_reducing_k hEntries hState hLarge with ⟨k, hred⟩
            let z' := (applyHTPowToState k z w).1
            let w' := (applyHTPowToState k z w).2
            have hred' :
                StateEntriesInDyadicCyclotomic z' w' ∧
                IsUnitState z' w' ∧
                DenNormSDE z' < DenNormSDE z := by
              simpa [z', w'] using hred
            rcases hred' with ⟨hEntries', hState', hDec⟩
            have hlt : DenNormSDE z' < n := by simpa [hdn] using hDec
            rcases ih (DenNormSDE z') hlt z' w' rfl hEntries' hState' with ⟨C', hC'⟩
            exact kmm_state_preparation_step_from_reduced
              (z := z) (w := w) (z' := z') (w' := w') k rfl rfl
              hEntries hState hEntries' hState' ⟨C', hC'⟩
  exact hmain (DenNormSDE z) z w rfl hEntries hState

/-- Coarse but fully constructive T-count bound for KMM state preparation.

The low-SDE table is bounded by 64 `T` gates, and every recursive KMM descent
uses the optimized inverse `HT` step, adding at most one `T`.  This is not the
Ross-Selinger sharp `2k - 2` theorem; it is the full KMM recursion with
T-count accounting threaded through it. -/
theorem kmm_state_preparation_tcount
    {z w : ℂ}
    (hEntries : StateEntriesInDyadicCyclotomic z w)
    (hState : IsUnitState z w) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C * ket0Column = stateColumn z w ∧
        TCount C ≤ DenNormSDE z + 64 := by
  classical
  have hmain :
      ∀ n : ℕ, ∀ z w : ℂ,
        DenNormSDE z = n →
        StateEntriesInDyadicCyclotomic z w →
        IsUnitState z w →
        ∃ C : CliffordTCircuit,
          CliffordTCircuit.eval C * ket0Column = stateColumn z w ∧
            TCount C ≤ n + 64 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro z w hdn hEntries hState
        by_cases hLowN : n ≤ 2
        · rcases kmm_low_sde_state_table_complete_tcount_impl hEntries hState
              (by simpa [hdn]) with ⟨C, hC, hT⟩
          exact ⟨C, hC, by omega⟩
        · by_cases hMedN : n ≤ 4
          · have h3 : 3 ≤ DenNormSDE z := by simpa [hdn] using (by omega : 3 ≤ n)
            have h4 : DenNormSDE z ≤ 4 := by simpa [hdn]
            rcases kmm_exists_reducing_k_sde34 hEntries hState h4 h3 with
              ⟨k, hEntries', hState', hDec⟩
            have hlt : DenNormSDE (applyHTPowToState k z w).1 < n := by
              simpa [hdn] using hDec
            rcases ih (DenNormSDE (applyHTPowToState k z w).1) hlt
                (applyHTPowToState k z w).1 (applyHTPowToState k z w).2
                rfl hEntries' hState' with ⟨C', hC', hT'⟩
            rcases kmm_state_preparation_optimized_step_from_reduced
                k rfl rfl hEntries hState hEntries' hState' hC' with
              ⟨C, hC, hTstep⟩
            refine ⟨C, hC, ?_⟩
            have hT : TCount C ≤ TCount C' + 1 := hTstep
            omega
          · have hLargeN : 5 ≤ n := by omega
            have hLarge : 5 ≤ DenNormSDE z := by simpa [hdn] using hLargeN
            rcases kmm_exists_reducing_k hEntries hState hLarge with ⟨k, hred⟩
            let z' := (applyHTPowToState k z w).1
            let w' := (applyHTPowToState k z w).2
            have hred' :
                StateEntriesInDyadicCyclotomic z' w' ∧
                IsUnitState z' w' ∧
                DenNormSDE z' < DenNormSDE z := by
              simpa [z', w'] using hred
            rcases hred' with ⟨hEntries', hState', hDec⟩
            have hlt : DenNormSDE z' < n := by simpa [hdn] using hDec
            rcases ih (DenNormSDE z') hlt z' w' rfl hEntries' hState' with
              ⟨C', hC', hT'⟩
            rcases kmm_state_preparation_optimized_step_from_reduced
                (z := z) (w := w) (z' := z') (w' := w') k rfl rfl
                hEntries hState hEntries' hState' hC' with
              ⟨C, hC, hTstep⟩
            refine ⟨C, hC, ?_⟩
            have hT : TCount C ≤ TCount C' + 1 := hTstep
            omega
  simpa using hmain (DenNormSDE z) z w rfl hEntries hState

/-- The determinant/global-phase step reducing unitary synthesis to first-column
state preparation. -/
theorem kmm_unitary_implementation_from_state_preparation
    {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hEntries : MatrixEntriesInDyadicCyclotomic U)
    (hStatePrep :
      ∀ {z w : ℂ},
        StateEntriesInDyadicCyclotomic z w →
        IsUnitState z w →
        ∃ C : CliffordTCircuit,
          CliffordTCircuit.eval C * ket0Column = stateColumn z w) :
    ∃ C : CliffordTCircuit, CliffordTCircuit.eval C = U := by
  have hFirstEntries : StateEntriesInDyadicCyclotomic (U 0 0) (U 1 0) :=
    first_column_entries_in_dyadic hEntries
  have hFirstState : IsUnitState (U 0 0) (U 1 0) :=
    first_column_is_unit_state hU
  rcases hStatePrep hFirstEntries hFirstState with ⟨C₀, hC₀⟩
  exact kmm_unitary_implementation_phase_correction hU hEntries C₀ hC₀

/-- T-count-carrying unitary synthesis from a T-count-carrying state-preparation
procedure. -/
theorem kmm_unitary_implementation_from_state_preparation_tcount
    {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hEntries : MatrixEntriesInDyadicCyclotomic U)
    (hStatePrep :
      ∀ {z w : ℂ},
        StateEntriesInDyadicCyclotomic z w →
        IsUnitState z w →
        ∃ C : CliffordTCircuit,
          CliffordTCircuit.eval C * ket0Column = stateColumn z w ∧
            TCount C ≤ DenNormSDE z + 64) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C = U ∧
        TCount C ≤ DenNormSDE (U 0 0) + 71 := by
  have hFirstEntries : StateEntriesInDyadicCyclotomic (U 0 0) (U 1 0) :=
    first_column_entries_in_dyadic hEntries
  have hFirstState : IsUnitState (U 0 0) (U 1 0) :=
    first_column_is_unit_state hU
  rcases hStatePrep hFirstEntries hFirstState with ⟨C₀, hC₀, hT₀⟩
  rcases kmm_unitary_implementation_phase_correction_tcount hU hEntries C₀ hC₀ with
    ⟨C, hC, hTphase⟩
  refine ⟨C, hC, ?_⟩
  omega

/-- Non-optimal exact synthesis consequence of KMM. -/
theorem kmm_exact_synthesis
    {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hEntries : MatrixEntriesInDyadicCyclotomic U) :
    ∃ C : CliffordTCircuit, CliffordTCircuit.eval C = U := by
  exact kmm_unitary_implementation_from_state_preparation hU hEntries
    (fun hEntries hState => kmm_state_preparation hEntries hState)

/-- Stable name used by the earlier Ross-Selinger plan. -/
theorem exact_synthesis_of_unitary_dyadic_entries
    {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hEntries : MatrixEntriesInDyadicCyclotomic U) :
    ∃ C : CliffordTCircuit, CliffordTCircuit.eval C = U :=
  kmm_exact_synthesis hU hEntries

/-- Coarse, fully constructive KMM exact synthesis with T-count accounting. -/
theorem kmm_exact_synthesis_tcount
    {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hEntries : MatrixEntriesInDyadicCyclotomic U) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C = U ∧
        TCount C ≤ DenNormSDE (U 0 0) + 71 := by
  exact kmm_unitary_implementation_from_state_preparation_tcount hU hEntries
    (fun hEntries hState => kmm_state_preparation_tcount hEntries hState)

/-- Stable T-count-carrying exact-synthesis name for unitary dyadic matrices. -/
theorem exact_synthesis_of_unitary_dyadic_entries_tcount
    {U : Square 2}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hEntries : MatrixEntriesInDyadicCyclotomic U) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C = U ∧
        TCount C ≤ DenNormSDE (U 0 0) + 71 :=
  kmm_exact_synthesis_tcount hU hEntries

/-- Exact synthesis specialized to Ross-Selinger completion matrices. -/
theorem exact_synthesis_completion {u t : ℂ}
    (hu : InDyadicCyclotomic u)
    (ht : InDyadicCyclotomic t)
    (hNorm : NormEquation u t) :
    ∃ C : CliffordTCircuit, CliffordTCircuit.eval C = completionMatrix u t := by
  exact exact_synthesis_of_unitary_dyadic_entries
    (completionMatrix_mem_unitaryGroup hNorm)
    (completionMatrix_entries_in_dyadic hu ht)

/-- The Ross-Selinger returned-branch move `U ↦ T U T†` keeps the same
top-left entry `u` and replaces the completion entry by `ω t`. -/
theorem phaseT_completionMatrix_phaseT_conjTranspose
    (u t : ℂ) :
    phaseT * completionMatrix u t * phaseT† =
      completionMatrix u (rsOmegaAlg * t) := by
  have hstarOmega : star rsOmegaAlg = rsOmegaAlg⁻¹ := by
    have hunit := rsOmegaAlg_unit
    exact eq_inv_of_mul_eq_one_left hunit
  have homega_ne : rsOmegaAlg ≠ 0 := by
    intro h
    have hunit := rsOmegaAlg_unit
    rw [h] at hunit
    norm_num at hunit
  have hmulOmegaInv : ∀ z : ℂ, rsOmegaAlg * (z * rsOmegaAlg⁻¹) = z := by
    intro z
    field_simp [homega_ne]
    try ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [completionMatrix, phaseT, diag2, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, phaseT_scalar_eq_rsOmegaAlg, hstarOmega,
      star_mul, mul_assoc, hmulOmegaInv]

/-- T-count-carrying exact synthesis specialized to Ross-Selinger completion
matrices. -/
theorem exact_synthesis_completion_tcount {u t : ℂ}
    (hu : InDyadicCyclotomic u)
    (ht : InDyadicCyclotomic t)
    (hNorm : NormEquation u t) :
    ∃ C : CliffordTCircuit,
      CliffordTCircuit.eval C = completionMatrix u t ∧
        TCount C ≤ DenNormSDE u + 71 := by
  rcases exact_synthesis_of_unitary_dyadic_entries_tcount
      (completionMatrix_mem_unitaryGroup hNorm)
      (completionMatrix_entries_in_dyadic hu ht) with ⟨C, hC, hT⟩
  refine ⟨C, hC, ?_⟩
  simpa [completionMatrix] using hT

end TwoControl.KMM

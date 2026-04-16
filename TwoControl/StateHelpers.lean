import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import TwoControl.BlockHelpers

open scoped Matrix ComplexOrder
open Matrix

namespace TwoControl

/-! ### State-space helper lemmas -/

namespace StateHelpers

noncomputable def ketPlus : Vec 2 :=
  ![(1 / Real.sqrt 2 : ℂ), (1 / Real.sqrt 2 : ℂ)]

@[simp] lemma kronVec_vec2_apply_0 (a b : Vec 2) :
    kronVec a b 0 = a 0 * b 0 := by
  have hdiv : (((0 : Fin (2 * 2))).divNat : Fin 2) = 0 := by native_decide
  have hmod : (((0 : Fin (2 * 2))).modNat : Fin 2) = 0 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec2_apply_1 (a b : Vec 2) :
    kronVec a b 1 = a 0 * b 1 := by
  have hdiv : (((1 : Fin (2 * 2))).divNat : Fin 2) = 0 := by native_decide
  have hmod : (((1 : Fin (2 * 2))).modNat : Fin 2) = 1 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec2_apply_2 (a b : Vec 2) :
    kronVec a b 2 = a 1 * b 0 := by
  have hdiv : (((2 : Fin (2 * 2))).divNat : Fin 2) = 1 := by native_decide
  have hmod : (((2 : Fin (2 * 2))).modNat : Fin 2) = 0 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec2_apply_3 (a b : Vec 2) :
    kronVec a b 3 = a 1 * b 1 := by
  have hdiv : (((3 : Fin (2 * 2))).divNat : Fin 2) = 1 := by native_decide
  have hmod : (((3 : Fin (2 * 2))).modNat : Fin 2) = 1 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec4_2_apply_0 (v : Vec 4) (w : Vec 2) :
    kronVec v w 0 = v 0 * w 0 := by
  have hdiv : (((0 : Fin (4 * 2))).divNat : Fin 4) = 0 := by native_decide
  have hmod : (((0 : Fin (4 * 2))).modNat : Fin 2) = 0 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec4_2_apply_1 (v : Vec 4) (w : Vec 2) :
    kronVec v w 1 = v 0 * w 1 := by
  have hdiv : (((1 : Fin (4 * 2))).divNat : Fin 4) = 0 := by native_decide
  have hmod : (((1 : Fin (4 * 2))).modNat : Fin 2) = 1 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec4_2_apply_2 (v : Vec 4) (w : Vec 2) :
    kronVec v w 2 = v 1 * w 0 := by
  have hdiv : (((2 : Fin (4 * 2))).divNat : Fin 4) = 1 := by native_decide
  have hmod : (((2 : Fin (4 * 2))).modNat : Fin 2) = 0 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec4_2_apply_3 (v : Vec 4) (w : Vec 2) :
    kronVec v w 3 = v 1 * w 1 := by
  have hdiv : (((3 : Fin (4 * 2))).divNat : Fin 4) = 1 := by native_decide
  have hmod : (((3 : Fin (4 * 2))).modNat : Fin 2) = 1 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec4_2_apply_4 (v : Vec 4) (w : Vec 2) :
    kronVec v w 4 = v 2 * w 0 := by
  have hdiv : (((4 : Fin (4 * 2))).divNat : Fin 4) = 2 := by native_decide
  have hmod : (((4 : Fin (4 * 2))).modNat : Fin 2) = 0 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec4_2_apply_5 (v : Vec 4) (w : Vec 2) :
    kronVec v w 5 = v 2 * w 1 := by
  have hdiv : (((5 : Fin (4 * 2))).divNat : Fin 4) = 2 := by native_decide
  have hmod : (((5 : Fin (4 * 2))).modNat : Fin 2) = 1 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec4_2_apply_6 (v : Vec 4) (w : Vec 2) :
    kronVec v w 6 = v 3 * w 0 := by
  have hdiv : (((6 : Fin (4 * 2))).divNat : Fin 4) = 3 := by native_decide
  have hmod : (((6 : Fin (4 * 2))).modNat : Fin 2) = 0 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec4_2_apply_7 (v : Vec 4) (w : Vec 2) :
    kronVec v w 7 = v 3 * w 1 := by
  have hdiv : (((7 : Fin (4 * 2))).divNat : Fin 4) = 3 := by native_decide
  have hmod : (((7 : Fin (4 * 2))).modNat : Fin 2) = 1 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec2_4_apply_0 (v : Vec 2) (w : Vec 4) :
    kronVec v w 0 = v 0 * w 0 := by
  have hdiv : (((0 : Fin (2 * 4))).divNat : Fin 2) = 0 := by native_decide
  have hmod : (((0 : Fin (2 * 4))).modNat : Fin 4) = 0 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec2_4_apply_1 (v : Vec 2) (w : Vec 4) :
    kronVec v w 1 = v 0 * w 1 := by
  have hdiv : (((1 : Fin (2 * 4))).divNat : Fin 2) = 0 := by native_decide
  have hmod : (((1 : Fin (2 * 4))).modNat : Fin 4) = 1 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec2_4_apply_2 (v : Vec 2) (w : Vec 4) :
    kronVec v w 2 = v 0 * w 2 := by
  have hdiv : (((2 : Fin (2 * 4))).divNat : Fin 2) = 0 := by native_decide
  have hmod : (((2 : Fin (2 * 4))).modNat : Fin 4) = 2 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec2_4_apply_3 (v : Vec 2) (w : Vec 4) :
    kronVec v w 3 = v 0 * w 3 := by
  have hdiv : (((3 : Fin (2 * 4))).divNat : Fin 2) = 0 := by native_decide
  have hmod : (((3 : Fin (2 * 4))).modNat : Fin 4) = 3 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec2_4_apply_4 (v : Vec 2) (w : Vec 4) :
    kronVec v w 4 = v 1 * w 0 := by
  have hdiv : (((4 : Fin (2 * 4))).divNat : Fin 2) = 1 := by native_decide
  have hmod : (((4 : Fin (2 * 4))).modNat : Fin 4) = 0 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec2_4_apply_5 (v : Vec 2) (w : Vec 4) :
    kronVec v w 5 = v 1 * w 1 := by
  have hdiv : (((5 : Fin (2 * 4))).divNat : Fin 2) = 1 := by native_decide
  have hmod : (((5 : Fin (2 * 4))).modNat : Fin 4) = 1 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec2_4_apply_6 (v : Vec 2) (w : Vec 4) :
    kronVec v w 6 = v 1 * w 2 := by
  have hdiv : (((6 : Fin (2 * 4))).divNat : Fin 2) = 1 := by native_decide
  have hmod : (((6 : Fin (2 * 4))).modNat : Fin 4) = 2 := by native_decide
  simp [kronVec, hdiv, hmod]

@[simp] lemma kronVec_vec2_4_apply_7 (v : Vec 2) (w : Vec 4) :
    kronVec v w 7 = v 1 * w 3 := by
  have hdiv : (((7 : Fin (2 * 4))).divNat : Fin 2) = 1 := by native_decide
  have hmod : (((7 : Fin (2 * 4))).modNat : Fin 4) = 3 := by native_decide
  simp [kronVec, hdiv, hmod]

lemma isQubit_iff_star_dot_eq_one {n : ℕ} (v : Vec n) :
    IsQubit v ↔ star v ⬝ᵥ v = (1 : ℂ) := by
  have hsum : (((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v) := by
    calc
      (((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ)) = ∑ i, (((‖v i‖ ^ 2 : ℝ) : ℂ)) := by simp
      _ = ∑ i, star (v i) * v i := by
          congr with i
          rw [← Complex.normSq_eq_norm_sq]
          simpa using (Complex.normSq_eq_conj_mul_self (z := v i))
      _ = star v ⬝ᵥ v := rfl
  constructor
  · intro h
    have h' : (((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = 1) := by
      exact_mod_cast h
    exact hsum.symm.trans h'
  · intro h
    have h' : (((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = 1) := hsum.trans h
    exact Complex.ofReal_injective (by simpa using h')

lemma isQubit_ket0 : IsQubit ket0 := by
  simp [IsQubit, ket0, Fin.sum_univ_two]

lemma isQubit_ket1 : IsQubit ket1 := by
  simp [IsQubit, ket1, Fin.sum_univ_two]

lemma isQubit_ketPlus : IsQubit ketPlus := by
  have hsqrt : (Real.sqrt 2 : ℝ) ≠ 0 := by
    positivity
  simp [IsQubit, ketPlus, Fin.sum_univ_two]
  field_simp [hsqrt]
  have hsq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
  nlinarith

lemma isQubit_ne_zero {n : ℕ} {v : Vec n} (hv : IsQubit v) : v ≠ 0 := by
  intro hz
  have hv' : star v ⬝ᵥ v = (1 : ℂ) := (isQubit_iff_star_dot_eq_one v).mp hv
  rw [hz] at hv'
  simp at hv'

@[simp] lemma kronVec_zero_left (x : Vec n) :
    kronVec (0 : Vec m) x = 0 := by
  ext i
  simp [kronVec]

@[simp] lemma kronVec_zero_right (x : Vec m) :
    kronVec x (0 : Vec n) = 0 := by
  ext i
  simp [kronVec]

@[simp] lemma kronVec_add_left (x y : Vec m) (z : Vec n) :
    kronVec (x + y) z = kronVec x z + kronVec y z := by
  ext i
  simp [kronVec, add_mul]

@[simp] lemma kronVec_add_right (x : Vec m) (y z : Vec n) :
    kronVec x (y + z) = kronVec x y + kronVec x z := by
  ext i
  simp [kronVec, mul_add]

@[simp] lemma kronVec_smul_left (c : ℂ) (x : Vec m) (y : Vec n) :
    kronVec (c • x) y = c • kronVec x y := by
  ext i
  simp [kronVec, mul_assoc]

@[simp] lemma kronVec_smul_right (c : ℂ) (x : Vec m) (y : Vec n) :
    kronVec x (c • y) = c • kronVec x y := by
  ext i
  simp [kronVec, mul_left_comm]

lemma vec2_basis_decomp (x : Vec 2) :
    x = x 0 • ket0 + x 1 • ket1 := by
  ext i
  fin_cases i <;> simp [ket0, ket1]

lemma vec4_basis_decomp (φ : Vec 4) :
    φ = kronVec ket0 ![φ 0, φ 1] + kronVec ket1 ![φ 2, φ 3] := by
  ext i
  fin_cases i <;>
    simp [ket0, ket1, kronVec_vec2_apply_0, kronVec_vec2_apply_1,
      kronVec_vec2_apply_2, kronVec_vec2_apply_3]

lemma kronVec_ket0_ket0_ne_zero : kronVec ket0 ket0 ≠ 0 := by
  intro h
  have h0 : kronVec ket0 ket0 0 = 0 := by simpa using congrFun h 0
  norm_num [kronVec_vec2_apply_0, ket0] at h0

lemma kronVec_ket1_ket0_ne_zero : kronVec ket1 ket0 ≠ 0 := by
  intro h
  have h2 : kronVec ket1 ket0 2 = 0 := by simpa using congrFun h 2
  norm_num [kronVec_vec2_apply_2, ket1, ket0] at h2

lemma mulVec_ne_zero_of_unitary {n : ℕ} (U : Square n)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {x : Vec n} (hx : x ≠ 0) :
    U.mulVec x ≠ 0 := by
  intro hUx
  have hleft : U† * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have : x = 0 := by
    calc
      x = (1 : Square n).mulVec x := by simp
      _ = (U† * U).mulVec x := by rw [hleft]
      _ = U†.mulVec (U.mulVec x) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hUx, Matrix.mulVec_zero]
  exact hx this

lemma isQubit_mulVec_of_unitary {n : ℕ} (U : Square n)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {x : Vec n} (hx : IsQubit x) :
    IsQubit (U.mulVec x) := by
  rw [isQubit_iff_star_dot_eq_one] at hx ⊢
  have hleft : U† * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  calc
    star (U.mulVec x) ⬝ᵥ U.mulVec x = (star x ᵥ* U†) ⬝ᵥ U.mulVec x := by
      rw [Matrix.star_mulVec]
    _ = star x ⬝ᵥ U†.mulVec (U.mulVec x) := by
      rw [← Matrix.dotProduct_mulVec]
    _ = star x ⬝ᵥ (U† * U).mulVec x := by
      rw [← Matrix.mulVec_mulVec]
    _ = star x ⬝ᵥ x := by
      rw [hleft, Matrix.one_mulVec]
    _ = 1 := hx

def detVec2 (u v : Vec 2) : ℂ :=
  u 0 * v 1 - u 1 * v 0

def detVec4 (v : Vec 4) : ℂ :=
  v 0 * v 3 - v 1 * v 2

lemma detVec4_smul (c : ℂ) (v : Vec 4) :
    detVec4 (c • v) = c ^ 2 * detVec4 v := by
  unfold detVec4
  simp [Pi.smul_apply, pow_two, mul_assoc, mul_left_comm]
  ring

lemma detVec4_kronVec (a b : Vec 2) :
    detVec4 (kronVec a b) = 0 := by
  unfold detVec4
  simp [kronVec_vec2_apply_0, kronVec_vec2_apply_1, kronVec_vec2_apply_2, kronVec_vec2_apply_3]
  ring

lemma detVec4_add_kronVec (a₀ b₀ a₁ b₁ : Vec 2) :
    detVec4 (kronVec a₀ b₀ + kronVec a₁ b₁) = detVec2 a₀ a₁ * detVec2 b₀ b₁ := by
  unfold detVec4 detVec2
  simp [kronVec_vec2_apply_0, kronVec_vec2_apply_1, kronVec_vec2_apply_2, kronVec_vec2_apply_3]
  ring

lemma detVec4_add_smul (u v : Vec 4) (c : ℂ) :
    detVec4 (u + c • v) =
      detVec4 u + c * (u 0 * v 3 + v 0 * u 3 - u 1 * v 2 - v 1 * u 2) + c ^ 2 * detVec4 v := by
  unfold detVec4
  simp [Pi.add_apply, Pi.smul_apply]
  ring

lemma isProductState_of_detVec4_eq_zero (v : Vec 4) (hdet : detVec4 v = 0) :
    IsProductState v := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · refine ⟨ket1, ![v 2, v 3], ?_⟩
      ext i
      fin_cases i <;>
        simp [kronVec_vec2_apply_0, kronVec_vec2_apply_1, kronVec_vec2_apply_2,
          kronVec_vec2_apply_3, ket1, h0, h1]
    · have h12 : v 1 * v 2 = 0 := by
        simpa [detVec4, h0] using hdet
      have h2 : v 2 = 0 := (mul_eq_zero.mp h12).resolve_left h1
      refine ⟨![v 1, v 3], ket1, ?_⟩
      ext i
      fin_cases i <;>
        simp [kronVec_vec2_apply_0, kronVec_vec2_apply_1, kronVec_vec2_apply_2,
          kronVec_vec2_apply_3, ket1, h0, h2]
  · have h03 : v 0 * v 3 = v 1 * v 2 := by
      exact sub_eq_zero.mp hdet
    refine ⟨![v 0, v 2], ![1, v 1 / v 0], ?_⟩
    ext i
    fin_cases i
    · simp [kronVec_vec2_apply_0]
    · have h01 : v 0 * (v 1 / v 0) = v 1 := by
        field_simp [h0]
      simpa [kronVec_vec2_apply_1, mul_comm] using h01.symm
    · simp [kronVec_vec2_apply_2]
    · have hlast : v 2 * (v 1 / v 0) = v 3 := by
        apply mul_right_cancel₀ h0
        calc
          (v 2 * (v 1 / v 0)) * v 0 = v 2 * v 1 := by
            field_simp [h0]
          _ = v 0 * v 3 := by simpa [mul_comm, mul_left_comm, mul_assoc] using h03.symm
          _ = v 3 * v 0 := by ring
      simp [kronVec_vec2_apply_3, hlast]

lemma detVec4_eq_zero_of_isProductState {v : Vec 4} (hv : IsProductState v) :
    detVec4 v = 0 := by
  rcases hv with ⟨a, b, rfl⟩
  exact detVec4_kronVec a b

lemma isProductState_iff_detVec4_eq_zero (v : Vec 4) :
    IsProductState v ↔ detVec4 v = 0 := by
  constructor
  · exact detVec4_eq_zero_of_isProductState
  · exact isProductState_of_detVec4_eq_zero v

lemma isEntangled_iff_detVec4_ne_zero (v : Vec 4) :
    IsEntangled v ↔ detVec4 v ≠ 0 := by
  rw [IsEntangled, isProductState_iff_detVec4_eq_zero]

lemma dot_kronVec_two_two (a b : Vec 2) :
    star (kronVec a b) ⬝ᵥ kronVec a b = (star a ⬝ᵥ a) * (star b ⬝ᵥ b) := by
  simp [dotProduct, Fin.sum_univ_four, Fin.sum_univ_two,
    kronVec_vec2_apply_0, kronVec_vec2_apply_1, kronVec_vec2_apply_2, kronVec_vec2_apply_3,
    mul_assoc, mul_comm]
  ring

lemma isQubit_of_kron_right {a b : Vec 2}
    (hk : IsQubit (kronVec a b)) (hb : IsQubit b) : IsQubit a := by
  rw [isQubit_iff_star_dot_eq_one] at hk hb ⊢
  rw [dot_kronVec_two_two] at hk
  simpa [hb] using hk

lemma isQubit_of_kron_left {a b : Vec 2}
    (hk : IsQubit (kronVec a b)) (ha : IsQubit a) : IsQubit b := by
  rw [isQubit_iff_star_dot_eq_one] at hk ha ⊢
  rw [dot_kronVec_two_two] at hk
  simpa [ha] using hk

lemma sumSq_ne_zero_of_ne_zero (v : Vec 2) (hv : v ≠ 0) :
    ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 ≠ 0 := by
  intro hsum
  have h0 : ‖v 0‖ = 0 := by
    nlinarith [sq_nonneg (‖v 0‖), sq_nonneg (‖v 1‖), hsum]
  have h1 : ‖v 1‖ = 0 := by
    nlinarith [sq_nonneg (‖v 0‖), sq_nonneg (‖v 1‖), hsum]
  apply hv
  ext i
  fin_cases i
  · exact norm_eq_zero.mp h0
  · exact norm_eq_zero.mp h1

lemma normalize_vec2 (v : Vec 2) (hv : v ≠ 0) :
    ∃ ψ : Vec 2, IsQubit ψ ∧ ∃ μ : ℂ, μ ≠ 0 ∧ v = μ • ψ := by
  let r2 : ℝ := ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2
  have hr2_ne : r2 ≠ 0 := sumSq_ne_zero_of_ne_zero v hv
  have hr2_nonneg : 0 ≤ r2 := by
    dsimp [r2]
    positivity
  have hr2_pos : 0 < r2 := lt_of_le_of_ne hr2_nonneg (Ne.symm hr2_ne)
  let r : ℝ := Real.sqrt r2
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hr_ne : r ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 hr2_pos
  refine ⟨((r : ℂ)⁻¹) • v, ?_, (r : ℂ), by exact_mod_cast hr_ne, ?_⟩
  · simp [IsQubit, Fin.sum_univ_two]
    field_simp [hr_ne]
    have hsq : r ^ 2 = r2 := by
      dsimp [r]
      nlinarith [Real.sq_sqrt hr2_nonneg]
    have habs : |r| = r := abs_of_nonneg hr_nonneg
    simp [habs] at *
    nlinarith
  · ext i
    simp [hr_ne]

lemma isProductState_smul (c : ℂ) {v : Vec 4} (hv : IsProductState v) :
    IsProductState (c • v) := by
  rcases hv with ⟨a, b, rfl⟩
  exact ⟨c • a, b, by rw [kronVec_smul_left]⟩

lemma left_ne_zero_of_kronVec_ne_zero {a b : Vec 2}
    (h : kronVec a b ≠ 0) : a ≠ 0 := by
  intro ha
  apply h
  simp [ha]

lemma right_ne_zero_of_kronVec_ne_zero {a b : Vec 2}
    (h : kronVec a b ≠ 0) : b ≠ 0 := by
  intro hb
  apply h
  simp [hb]

lemma exists_smul_of_detVec2_eq_zero {u v : Vec 2}
    (hu : u ≠ 0) (hdet : detVec2 u v = 0) :
    ∃ c : ℂ, v = c • u := by
  by_cases hu0 : u 0 = 0
  · have hu1 : u 1 ≠ 0 := by
      intro hu1
      apply hu
      ext i
      fin_cases i <;> simp [hu0, hu1]
    have hcross : u 0 * v 1 = u 1 * v 0 := sub_eq_zero.mp hdet
    have hv0 : v 0 = 0 := by
      have hmul : u 1 * v 0 = 0 := by simpa [hu0] using hcross.symm
      exact (mul_eq_zero.mp hmul).resolve_left hu1
    refine ⟨v 1 / u 1, ?_⟩
    ext i
    fin_cases i
    · simp [hv0, hu0]
    · have h11 : (v 1 / u 1) * u 1 = v 1 := by
          field_simp [hu1]
      calc
        v 1 = (v 1 / u 1) * u 1 := by simpa [mul_comm] using h11.symm
        _ = ((v 1 / u 1) • u) 1 := by simp [Pi.smul_apply]
  · refine ⟨v 0 / u 0, ?_⟩
    ext i
    fin_cases i
    · have h00 : (v 0 / u 0) * u 0 = v 0 := by
          field_simp [hu0]
      calc
        v 0 = (v 0 / u 0) * u 0 := h00.symm
        _ = ((v 0 / u 0) • u) 0 := by simp [Pi.smul_apply]
    · have hcross : u 0 * v 1 = u 1 * v 0 := sub_eq_zero.mp hdet
      have h01 : v 1 = (v 0 / u 0) * u 1 := by
        apply mul_left_cancel₀ hu0
        calc
          u 0 * v 1 = u 1 * v 0 := hcross
          _ = (v 0 / u 0) * u 1 * u 0 := by
                field_simp [hu0]
          _ = u 0 * ((v 0 / u 0) * u 1) := by ring
      simpa [Pi.smul_apply, mul_comm] using h01

lemma quadratic_root_eq_zero (A B C : ℂ) (hC : C ≠ 0) :
    ∃ t : ℂ, A + B * t + C * t ^ 2 = 0 := by
  let p : Polynomial ℂ := Polynomial.C C * Polynomial.X ^ 2 + Polynomial.C B * Polynomial.X + Polynomial.C A
  have hp2 : p.coeff 2 = C := by
    simp [p]
  have hp0 : p ≠ 0 := by
    intro hp0
    apply hC
    have hcoeff : p.coeff 2 = 0 := by simp [hp0]
    exact hp2.symm.trans hcoeff
  have hpdegNat : p.natDegree ≠ 0 := by
    intro hdeg
    have hcoeff : p.coeff 2 = 0 := by
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    exact hC (hp2.symm.trans hcoeff)
  have hpdeg : p.degree ≠ 0 := by
    simpa [Polynomial.degree_eq_natDegree hp0] using hpdegNat
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p hpdeg
  refine ⟨t, ?_⟩
  simpa [p, pow_two, mul_assoc, add_assoc, add_left_comm, add_comm] using ht

set_option maxHeartbeats 400000 in
lemma qubit_product_state_factors {v : Vec 4}
    (hvQ : IsQubit v) (hvProd : IsProductState v) :
    ∃ ψ φ : Vec 2, IsQubit ψ ∧ IsQubit φ ∧ v = kronVec ψ φ := by
  rcases hvProd with ⟨a, b, rfl⟩
  have hk_ne : kronVec a b ≠ 0 := isQubit_ne_zero hvQ
  have ha_ne : a ≠ 0 := left_ne_zero_of_kronVec_ne_zero hk_ne
  rcases normalize_vec2 a ha_ne with ⟨ψ, hψ, μ, _hμ_ne, ha⟩
  let φ : Vec 2 := μ • b
  have hEq : kronVec a b = kronVec ψ φ := by
    calc
      kronVec a b = kronVec (μ • ψ) b := by rw [ha]
      _ = kronVec ψ (μ • b) := by rw [kronVec_smul_left, ← kronVec_smul_right]
      _ = kronVec ψ φ := by rfl
  have hφ : IsQubit φ := by
    rw [hEq] at hvQ
    rw [isQubit_iff_star_dot_eq_one] at hvQ hψ ⊢
    rw [dot_kronVec_two_two] at hvQ
    simpa [hψ] using hvQ
  exact ⟨ψ, φ, hψ, hφ, hEq⟩

lemma isQubit_kron {a b : Vec 2}
    (ha : IsQubit a) (hb : IsQubit b) : IsQubit (kronVec a b) := by
  rw [isQubit_iff_star_dot_eq_one] at ha hb ⊢
  rw [dot_kronVec_two_two]
  simp [ha, hb]

lemma dot_kronVec_two_two_cross (a b c d : Vec 2) :
    star (kronVec a b) ⬝ᵥ kronVec c d = (star a ⬝ᵥ c) * (star b ⬝ᵥ d) := by
  simp [dotProduct, Fin.sum_univ_four, Fin.sum_univ_two,
    kronVec_vec2_apply_0, kronVec_vec2_apply_1, kronVec_vec2_apply_2, kronVec_vec2_apply_3,
    mul_assoc, mul_comm]
  ring

lemma kronVec_comp_finProdFinEquiv_eq_vec {m n : ℕ} (x : Vec m) (y : Vec n) :
    kronVec x y ∘ finProdFinEquiv = Matrix.vec (Matrix.vecMulVec y x) := by
  funext ij
  rcases ij with ⟨i, j⟩
  have hpair : ((@finProdFinEquiv m n).symm ((@finProdFinEquiv m n) (i, j))) = (i, j) := by
    simp
  have hdiv : (((@finProdFinEquiv m n) (i, j)).divNat : Fin m) = i := by
    change (((@finProdFinEquiv m n).symm ((@finProdFinEquiv m n) (i, j))).1 = i)
    exact congrArg Prod.fst hpair
  have hmod : (((@finProdFinEquiv m n) (i, j)).modNat : Fin n) = j := by
    change (((@finProdFinEquiv m n).symm ((@finProdFinEquiv m n) (i, j))).2 = j)
    exact congrArg Prod.snd hpair
  simp [kronVec, Matrix.vec, Matrix.vecMulVec_apply, hdiv, hmod, mul_comm]

lemma kron_mulVec_reindexed {m n : ℕ}
    (A : Square m) (B : Square n) (x : Vec m) (y : Vec n) :
    (A ⊗ₖ B).mulVec (kronVec x y) = kronVec (A.mulVec x) (B.mulVec y) := by
  let X : Matrix (Fin n) (Fin m) ℂ := Matrix.vecMulVec y x
  have hReindex :
      (A ⊗ₖ B).mulVec (kronVec x y) =
        ((Matrix.kroneckerMap (· * ·) A B) *ᵥ (kronVec x y ∘ finProdFinEquiv)) ∘
          finProdFinEquiv.symm := by
    simpa [TwoControl.kron] using
      (Matrix.submatrix_mulVec_equiv
        (M := Matrix.kroneckerMap (· * ·) A B)
        (v := kronVec x y)
        (e₁ := finProdFinEquiv.symm)
        (e₂ := finProdFinEquiv.symm))
  have hKronecker :
      (Matrix.kroneckerMap (· * ·) A B) *ᵥ (kronVec x y ∘ finProdFinEquiv) =
        Matrix.vec (B * X * Aᵀ) := by
    rw [kronVec_comp_finProdFinEquiv_eq_vec]
    simpa [X] using (Matrix.kronecker_mulVec_vec (A := B) (X := X) (B := A))
  have hMatrix :
      B * X * Aᵀ = Matrix.vecMulVec (B.mulVec y) (A.mulVec x) := by
    calc
      B * X * Aᵀ = (B * X) * Aᵀ := by simp
      _ = Matrix.vecMulVec (B.mulVec y) x * Aᵀ := by rw [Matrix.mul_vecMulVec]
      _ = Matrix.vecMulVec (B.mulVec y) (x ᵥ* Aᵀ) := by rw [Matrix.vecMulVec_mul]
      _ = Matrix.vecMulVec (B.mulVec y) (A.mulVec x) := by rw [Matrix.vecMul_transpose]
  rw [hReindex, hKronecker, hMatrix]
  ext i
  rcases finProdFinEquiv.symm i with ⟨r, c⟩
  simp [kronVec, Matrix.vec, Matrix.vecMulVec_apply, mul_comm]

lemma kron_mulVec_two_two (A B : Square 2) (x y : Vec 2) :
    (A ⊗ₖ B).mulVec (kronVec x y) = kronVec (A.mulVec x) (B.mulVec y) :=
  kron_mulVec_reindexed A B x y

@[simp] lemma proj0_mulVec_ket0 : proj0.mulVec ket0 = ket0 := by
  ext i
  fin_cases i <;> simp [proj0, ketbra, ket0, Matrix.mulVec, dotProduct]

@[simp] lemma proj0_mulVec_ket1 : proj0.mulVec ket1 = 0 := by
  ext i
  fin_cases i <;> simp [proj0, ketbra, ket0, ket1, Matrix.mulVec, dotProduct]

@[simp] lemma proj1_mulVec_ket0 : proj1.mulVec ket0 = 0 := by
  ext i
  fin_cases i <;> simp [proj1, ketbra, ket0, ket1, Matrix.mulVec, dotProduct]

@[simp] lemma proj1_mulVec_ket1 : proj1.mulVec ket1 = ket1 := by
  ext i
  fin_cases i <;> simp [proj1, ketbra, ket1, Matrix.mulVec, dotProduct]

@[simp] lemma proj01_mulVec_ket0 : proj01.mulVec ket0 = 0 := by
  ext i
  fin_cases i <;> simp [proj01, ketbra, ket0, ket1, Matrix.mulVec, dotProduct]

@[simp] lemma proj01_mulVec_ket1 : proj01.mulVec ket1 = ket0 := by
  ext i
  fin_cases i <;> simp [proj01, ketbra, ket0, ket1, Matrix.mulVec, dotProduct]

@[simp] lemma proj10_mulVec_ket0 : proj10.mulVec ket0 = ket1 := by
  ext i
  fin_cases i <;> simp [proj10, ketbra, ket0, ket1, Matrix.mulVec, dotProduct]

@[simp] lemma proj10_mulVec_ket1 : proj10.mulVec ket1 = 0 := by
  ext i
  fin_cases i <;> simp [proj10, ketbra, ket0, ket1, Matrix.mulVec, dotProduct]

def colMatrix (u v : Vec 2) : Square 2 :=
  ![![u 0, v 0], ![u 1, v 1]]

lemma colMatrix_mulVec (u v x : Vec 2) :
    (colMatrix u v).mulVec x = x 0 • u + x 1 • v := by
  ext i
  fin_cases i <;>
    simp [colMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply,
      mul_comm]
  all_goals ring

@[simp] lemma colMatrix_mulVec_ket0 (u v : Vec 2) :
    (colMatrix u v).mulVec ket0 = u := by
  simp [colMatrix_mulVec, ket0]

@[simp] lemma colMatrix_mulVec_ket1 (u v : Vec 2) :
    (colMatrix u v).mulVec ket1 = v := by
  simp [colMatrix_mulVec, ket1]

lemma colMatrix_unitary_of_orthonormal (u v : Vec 2)
    (hu : IsQubit u) (hv : IsQubit v) (huv : star u ⬝ᵥ v = 0) :
    colMatrix u v ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hu' : star u ⬝ᵥ u = (1 : ℂ) := (isQubit_iff_star_dot_eq_one u).mp hu
  have hv' : star v ⬝ᵥ v = (1 : ℂ) := (isQubit_iff_star_dot_eq_one v).mp hv
  have hu'' : star (u 0) * u 0 + star (u 1) * u 1 = (1 : ℂ) := by
    simpa [dotProduct, Fin.sum_univ_two] using hu'
  have hv'' : star (v 0) * v 0 + star (v 1) * v 1 = (1 : ℂ) := by
    simpa [dotProduct, Fin.sum_univ_two] using hv'
  have huv' : star (u 0) * v 0 + star (u 1) * v 1 = (0 : ℂ) := by
    simpa [dotProduct, Fin.sum_univ_two] using huv
  have hvu : star v ⬝ᵥ u = (0 : ℂ) := by
    simpa [dotProduct, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc, mul_comm] using
      congrArg star huv
  have hvu' : star (v 0) * u 0 + star (v 1) * u 1 = (0 : ℂ) := by
    simpa [dotProduct, Fin.sum_univ_two] using hvu
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [colMatrix, Matrix.mul_apply, Fin.sum_univ_two] using hu''
  · simpa [colMatrix, Matrix.mul_apply, Fin.sum_univ_two] using huv'
  · simpa [colMatrix, Matrix.mul_apply, Fin.sum_univ_two] using hvu'
  · simpa [colMatrix, Matrix.mul_apply, Fin.sum_univ_two] using hv''

noncomputable def qubitPerp (ψ : Vec 2) : Vec 2 :=
  ![-star (ψ 1), star (ψ 0)]

lemma qubitPerp_orthogonal (ψ : Vec 2) :
    star ψ ⬝ᵥ qubitPerp ψ = 0 := by
  simp [qubitPerp, dotProduct, Fin.sum_univ_two]
  ring

lemma isQubit_qubitPerp {ψ : Vec 2} (hψ : IsQubit ψ) :
    IsQubit (qubitPerp ψ) := by
  rw [isQubit_iff_star_dot_eq_one] at hψ ⊢
  simp [qubitPerp, dotProduct, Fin.sum_univ_two]
  simpa [dotProduct, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc, mul_comm] using hψ

lemma qubit_basis_unitary (ψ : Vec 2) (hψ : IsQubit ψ) :
    colMatrix ψ (qubitPerp ψ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply colMatrix_unitary_of_orthonormal ψ (qubitPerp ψ) hψ (isQubit_qubitPerp hψ)
  exact qubitPerp_orthogonal ψ

lemma unitary_fix_of_adj_fix {n : ℕ} (U : Square n)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {x : Vec n}
    (hx : U.mulVec x = x) :
    U†.mulVec x = x := by
  have hleft : U† * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  calc
    U†.mulVec x = U†.mulVec (U.mulVec x) := by rw [hx]
    _ = (U† * U).mulVec x := by rw [← Matrix.mulVec_mulVec]
    _ = x := by rw [hleft, Matrix.one_mulVec]

lemma kronVec_assoc_222 (a b c : Vec 2) :
    (kronVec (kronVec a b) c : Vec 8) = kronVec a (kronVec b c) := by
  ext i
  fin_cases i <;> simp [mul_assoc]

lemma kronVec_right_cancel_ket0_vec4 {φ ψ : Vec 4}
    (h : kronVec φ ket0 = kronVec ψ ket0) :
    φ = ψ := by
  ext i
  fin_cases i
  · simpa [ket0, kronVec_vec4_2_apply_0] using congrFun h 0
  · simpa [ket0, kronVec_vec4_2_apply_2] using congrFun h 2
  · simpa [ket0, kronVec_vec4_2_apply_4] using congrFun h 4
  · simpa [ket0, kronVec_vec4_2_apply_6] using congrFun h 6

lemma kronVec_left_cancel_ket0_vec4 {φ ψ : Vec 4}
    (h : kronVec ket0 φ = kronVec ket0 ψ) :
    φ = ψ := by
  ext i
  fin_cases i
  · simpa [ket0, kronVec_vec2_4_apply_0] using congrFun h 0
  · simpa [ket0, kronVec_vec2_4_apply_1] using congrFun h 1
  · simpa [ket0, kronVec_vec2_4_apply_2] using congrFun h 2
  · simpa [ket0, kronVec_vec2_4_apply_3] using congrFun h 3

lemma kronVec_right_cancel_of_ne_zero_vec4 {φ ψ : Vec 4} {b : Vec 2}
    (hb : b ≠ 0) (h : kronVec φ b = kronVec ψ b) :
    φ = ψ := by
  have hbnz : b 0 ≠ 0 ∨ b 1 ≠ 0 := by
    by_contra hzero
    apply hb
    ext i
    fin_cases i
    · exact by simpa using (not_or.mp hzero).1
    · exact by simpa using (not_or.mp hzero).2
  rcases hbnz with hb0 | hb1
  · ext i
    fin_cases i
    · exact mul_right_cancel₀ hb0 <| by simpa [kronVec_vec4_2_apply_0] using congrFun h 0
    · exact mul_right_cancel₀ hb0 <| by simpa [kronVec_vec4_2_apply_2] using congrFun h 2
    · exact mul_right_cancel₀ hb0 <| by simpa [kronVec_vec4_2_apply_4] using congrFun h 4
    · exact mul_right_cancel₀ hb0 <| by simpa [kronVec_vec4_2_apply_6] using congrFun h 6
  · ext i
    fin_cases i
    · exact mul_right_cancel₀ hb1 <| by simpa [kronVec_vec4_2_apply_1] using congrFun h 1
    · exact mul_right_cancel₀ hb1 <| by simpa [kronVec_vec4_2_apply_3] using congrFun h 3
    · exact mul_right_cancel₀ hb1 <| by simpa [kronVec_vec4_2_apply_5] using congrFun h 5
    · exact mul_right_cancel₀ hb1 <| by simpa [kronVec_vec4_2_apply_7] using congrFun h 7

lemma kronVec_left_cancel_of_ne_zero_vec4 {a : Vec 2} {φ ψ : Vec 4}
    (ha : a ≠ 0) (h : kronVec a φ = kronVec a ψ) :
    φ = ψ := by
  have hanz : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
    by_contra hzero
    apply ha
    ext i
    fin_cases i
    · exact by simpa using (not_or.mp hzero).1
    · exact by simpa using (not_or.mp hzero).2
  rcases hanz with ha0 | ha1
  · ext i
    fin_cases i
    · exact mul_left_cancel₀ ha0 <| by simpa [kronVec_vec2_4_apply_0] using congrFun h 0
    · exact mul_left_cancel₀ ha0 <| by simpa [kronVec_vec2_4_apply_1] using congrFun h 1
    · exact mul_left_cancel₀ ha0 <| by simpa [kronVec_vec2_4_apply_2] using congrFun h 2
    · exact mul_left_cancel₀ ha0 <| by simpa [kronVec_vec2_4_apply_3] using congrFun h 3
  · ext i
    fin_cases i
    · exact mul_left_cancel₀ ha1 <| by simpa [kronVec_vec2_4_apply_4] using congrFun h 4
    · exact mul_left_cancel₀ ha1 <| by simpa [kronVec_vec2_4_apply_5] using congrFun h 5
    · exact mul_left_cancel₀ ha1 <| by simpa [kronVec_vec2_4_apply_6] using congrFun h 6
    · exact mul_left_cancel₀ ha1 <| by simpa [kronVec_vec2_4_apply_7] using congrFun h 7

lemma dot_mulVec_of_unitary {n : ℕ} (U : Square n)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (x y : Vec n) :
    star (U.mulVec x) ⬝ᵥ U.mulVec y = star x ⬝ᵥ y := by
  have hleft : U† * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  calc
    star (U.mulVec x) ⬝ᵥ U.mulVec y = (star x ᵥ* U†) ⬝ᵥ U.mulVec y := by
      rw [Matrix.star_mulVec]
    _ = star x ⬝ᵥ U†.mulVec (U.mulVec y) := by
      rw [← Matrix.dotProduct_mulVec]
    _ = star x ⬝ᵥ (U† * U).mulVec y := by
      rw [← Matrix.mulVec_mulVec]
    _ = star x ⬝ᵥ y := by rw [hleft, Matrix.one_mulVec]

lemma colMatrix_conjTranspose_mulVec_left (u v : Vec 2)
    (hUV : colMatrix u v ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    (colMatrix u v)†.mulVec u = ket0 := by
  have hleft : (colMatrix u v)† * colMatrix u v = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hUV
  calc
    (colMatrix u v)†.mulVec u = (colMatrix u v)†.mulVec ((colMatrix u v).mulVec ket0) := by
      rw [colMatrix_mulVec_ket0]
    _ = ((colMatrix u v)† * colMatrix u v).mulVec ket0 := by
      rw [← Matrix.mulVec_mulVec]
    _ = ket0 := by rw [hleft, Matrix.one_mulVec]

lemma colMatrix_conjTranspose_mulVec_right (u v : Vec 2)
    (hUV : colMatrix u v ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    (colMatrix u v)†.mulVec v = ket1 := by
  have hleft : (colMatrix u v)† * colMatrix u v = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hUV
  calc
    (colMatrix u v)†.mulVec v = (colMatrix u v)†.mulVec ((colMatrix u v).mulVec ket1) := by
      rw [colMatrix_mulVec_ket1]
    _ = ((colMatrix u v)† * colMatrix u v).mulVec ket1 := by
      rw [← Matrix.mulVec_mulVec]
    _ = ket1 := by rw [hleft, Matrix.one_mulVec]

lemma exists_unitary_of_fixed_right_factor (V : Square 4)
    (hV : V ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    {ψ : Vec 2} (hψ : IsQubit ψ)
    (hprop : ∀ x : Vec 2, IsQubit x →
      ∃ z : Vec 2, IsQubit z ∧ V.mulVec (kronVec x ket0) = kronVec z ψ) :
    ∃ Q : Square 2, Q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      ∀ x : Vec 2, IsQubit x → V.mulVec (kronVec x ket0) = kronVec (Q.mulVec x) ψ := by
  rcases hprop ket0 isQubit_ket0 with ⟨w0, hw0, hw0eq⟩
  rcases hprop ket1 isQubit_ket1 with ⟨w1, hw1, hw1eq⟩
  have horth_in : star (kronVec ket0 ket0) ⬝ᵥ kronVec ket1 ket0 = 0 := by
    rw [dot_kronVec_two_two_cross]
    simp [dotProduct, ket0, ket1, Fin.sum_univ_two]
  have horth_out : star w0 ⬝ᵥ w1 = 0 := by
    have hpres := dot_mulVec_of_unitary V hV (kronVec ket0 ket0) (kronVec ket1 ket0)
    rw [hw0eq, hw1eq, dot_kronVec_two_two_cross] at hpres
    rw [horth_in] at hpres
    have hψnorm : star ψ ⬝ᵥ ψ = 1 := (isQubit_iff_star_dot_eq_one ψ).mp hψ
    have hzero : (star w0 ⬝ᵥ w1) * 1 = 0 := by simpa [hψnorm] using hpres
    simpa using hzero
  let Q : Square 2 := colMatrix w0 w1
  have hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    dsimp [Q]
    exact colMatrix_unitary_of_orthonormal w0 w1 hw0 hw1 horth_out
  refine ⟨Q, hQ, ?_⟩
  intro x hx
  have hx_decomp : x = x 0 • ket0 + x 1 • ket1 := vec2_basis_decomp x
  calc
    V.mulVec (kronVec x ket0)
        = V.mulVec (kronVec (x 0 • ket0 + x 1 • ket1) ket0) := by
            conv_lhs => rw [hx_decomp]
    _ = V.mulVec (x 0 • kronVec ket0 ket0 + x 1 • kronVec ket1 ket0) := by
          rw [kronVec_add_left, kronVec_smul_left, kronVec_smul_left]
    _ = x 0 • V.mulVec (kronVec ket0 ket0) + x 1 • V.mulVec (kronVec ket1 ket0) := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    _ = x 0 • kronVec w0 ψ + x 1 • kronVec w1 ψ := by rw [hw0eq, hw1eq]
    _ = kronVec (x 0 • w0) ψ + kronVec (x 1 • w1) ψ := by
          rw [← kronVec_smul_left, ← kronVec_smul_left]
    _ = kronVec (x 0 • w0 + x 1 • w1) ψ := by rw [← kronVec_add_left]
    _ = kronVec (Q.mulVec x) ψ := by
          simp [Q, colMatrix_mulVec]

lemma exists_unitary_of_fixed_left_factor (V : Square 4)
    (hV : V ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    {ψ : Vec 2} (hψ : IsQubit ψ)
    (hprop : ∀ x : Vec 2, IsQubit x →
      ∃ z : Vec 2, IsQubit z ∧ V.mulVec (kronVec x ket0) = kronVec ψ z) :
    ∃ Q : Square 2, Q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      ∀ x : Vec 2, IsQubit x → V.mulVec (kronVec x ket0) = kronVec ψ (Q.mulVec x) := by
  rcases hprop ket0 isQubit_ket0 with ⟨w0, hw0, hw0eq⟩
  rcases hprop ket1 isQubit_ket1 with ⟨w1, hw1, hw1eq⟩
  have horth_in : star (kronVec ket0 ket0) ⬝ᵥ kronVec ket1 ket0 = 0 := by
    rw [dot_kronVec_two_two_cross]
    simp [dotProduct, ket0, ket1, Fin.sum_univ_two]
  have horth_out : star w0 ⬝ᵥ w1 = 0 := by
    have hpres := dot_mulVec_of_unitary V hV (kronVec ket0 ket0) (kronVec ket1 ket0)
    rw [hw0eq, hw1eq, dot_kronVec_two_two_cross] at hpres
    rw [horth_in] at hpres
    have hψnorm : star ψ ⬝ᵥ ψ = 1 := (isQubit_iff_star_dot_eq_one ψ).mp hψ
    have hzero : 1 * (star w0 ⬝ᵥ w1) = 0 := by simpa [hψnorm, mul_comm] using hpres
    simpa using hzero
  let Q : Square 2 := colMatrix w0 w1
  have hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    dsimp [Q]
    exact colMatrix_unitary_of_orthonormal w0 w1 hw0 hw1 horth_out
  refine ⟨Q, hQ, ?_⟩
  intro x hx
  have hx_decomp : x = x 0 • ket0 + x 1 • ket1 := vec2_basis_decomp x
  calc
    V.mulVec (kronVec x ket0)
        = V.mulVec (kronVec (x 0 • ket0 + x 1 • ket1) ket0) := by
            conv_lhs => rw [hx_decomp]
    _ = V.mulVec (x 0 • kronVec ket0 ket0 + x 1 • kronVec ket1 ket0) := by
          rw [kronVec_add_left, kronVec_smul_left, kronVec_smul_left]
    _ = x 0 • V.mulVec (kronVec ket0 ket0) + x 1 • V.mulVec (kronVec ket1 ket0) := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    _ = x 0 • kronVec ψ w0 + x 1 • kronVec ψ w1 := by rw [hw0eq, hw1eq]
    _ = kronVec ψ (x 0 • w0) + kronVec ψ (x 1 • w1) := by
          rw [← kronVec_smul_right, ← kronVec_smul_right]
    _ = kronVec ψ (x 0 • w0 + x 1 • w1) := by rw [← kronVec_add_right]
    _ = kronVec ψ (Q.mulVec x) := by
          simp [Q, colMatrix_mulVec]

end StateHelpers

end TwoControl

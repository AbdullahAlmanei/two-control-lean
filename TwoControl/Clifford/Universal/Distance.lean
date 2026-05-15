import TwoControl.Clifford.Universal.GateSets
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace TwoControl
namespace Clifford
namespace Universal

open scoped Matrix.Norms.Frobenius

/-!
Hilbert-Schmidt distance layer from `doc.tex`.  The statements here are the
error-accounting API needed after Lemma 12 replaces `R_z` gates by `{H,T}`
circuits.
-/

private lemma conj_mul_eq_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    star z * z = 1 := by
  calc
    star z * z = (((‖z‖ ^ 2 : ℝ) : ℂ)) := by
      rw [← Complex.normSq_eq_norm_sq]
      simpa using (Complex.normSq_eq_conj_mul_self (z := z)).symm
    _ = 1 := by simp [hz]

private lemma norm_eq_one_of_inner_self_eq_one {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] {x : E}
    (hx : inner ℂ x x = 1) :
    ‖x‖ = 1 := by
  have hx_sq : ‖x‖ ^ 2 = 1 := by
    have hsq := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [hx] at hsq
    norm_num at hsq
    linarith
  have hsq : ‖x‖ ^ 2 = 1 ^ 2 := by simpa using hx_sq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · linarith [norm_nonneg x]

private lemma phase_align_mul (z : ℂ) :
    Complex.exp (-(Complex.arg z) * Complex.I) * z = (‖z‖ : ℂ) := by
  have hz : z = (‖z‖ : ℂ) * Complex.exp (Complex.arg z * Complex.I) := by
    exact (Complex.norm_mul_exp_arg_mul_I z).symm
  calc
    Complex.exp (-(Complex.arg z) * Complex.I) * z
        = Complex.exp (-(Complex.arg z) * Complex.I) *
            ((‖z‖ : ℂ) * Complex.exp (Complex.arg z * Complex.I)) := by
              exact congrArg (fun w => Complex.exp (-(Complex.arg z) * Complex.I) * w) hz
    _ = (‖z‖ : ℂ) *
          (Complex.exp (-(Complex.arg z) * Complex.I) *
            Complex.exp (Complex.arg z * Complex.I)) := by
              ring
    _ = (‖z‖ : ℂ) * Complex.exp 0 := by
          congr 1
          rw [← Complex.exp_add]
          congr 1
          ring
    _ = (‖z‖ : ℂ) := by simp

private lemma sq_le_one_of_nonneg_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r ^ 2 ≤ 1 := by
  have habs : |r| ≤ |(1 : ℝ)| := by
    simpa [abs_of_nonneg hr0] using hr1
  simpa [pow_two] using (sq_le_sq).2 habs

private lemma one_sub_sq_div_nat_eq {N : ℕ} (r : ℝ) :
    1 - (r / N) ^ 2 = 1 - r ^ 2 * ((N : ℝ) ^ 2)⁻¹ := by
  by_cases hN : (N : ℝ) = 0
  · simp [hN]
  · field_simp [div_eq_mul_inv, hN]

private noncomputable def vecHS {N : ℕ} (A : Square N) :
    PiLp 2 (fun _ : Fin N => PiLp 2 (fun _ : Fin N => ℂ)) :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A i j))

private lemma vecHS_inner_eq_trace {N : ℕ} (A B : Square N) :
    inner ℂ (vecHS A) (vecHS B) = Matrix.trace (A† * B) := by
  rw [PiLp.inner_apply]
  simp [vecHS, PiLp.inner_apply, Matrix.trace, Matrix.mul_apply, mul_comm]
  rw [Finset.sum_comm]

private lemma vecHS_inner_self_of_unitary {N : ℕ} (U : Square N)
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    inner ℂ (vecHS U) (vecHS U) = (N : ℂ) := by
  have hUU : U† * U = (1 : Square N) := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [vecHS_inner_eq_trace]
  rw [hUU, Matrix.trace_one]
  simp

private lemma inner_self_eq_one_of_norm_eq_one {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] {x : E}
    (hx : ‖x‖ = 1) :
    inner ℂ x x = 1 := by
  apply Complex.ext
  · simpa [hx] using (inner_self_eq_norm_sq (𝕜 := ℂ) x)
  · simpa using inner_self_im (𝕜 := ℂ) x

private lemma inv_sqrt_nat_sq_eq_inv {N : ℕ} :
    star (((↑(Real.sqrt N) : ℂ)⁻¹)) * ((↑(Real.sqrt N) : ℂ)⁻¹) = ((N : ℂ)⁻¹) := by
  calc
    star (((↑(Real.sqrt N) : ℂ)⁻¹)) * ((↑(Real.sqrt N) : ℂ)⁻¹)
        = (((↑(Real.sqrt N) : ℂ) * (↑(Real.sqrt N) : ℂ))⁻¹) := by
        have h := (mul_inv_rev (↑(Real.sqrt N) : ℂ) (↑(Real.sqrt N) : ℂ)).symm
        simpa using h
    _ = ((N : ℂ))⁻¹ := by
          have hsq : ((↑(Real.sqrt N) : ℂ) * (↑(Real.sqrt N) : ℂ)) = (N : ℂ) := by
            have hsq' : (Real.sqrt N : ℝ) * Real.sqrt N = N := by
              have h := Real.sq_sqrt (show (0 : ℝ) ≤ N by exact_mod_cast Nat.zero_le N)
              simpa [pow_two] using h
            exact_mod_cast hsq'
          rw [hsq]

private noncomputable def normalizedVec {N : ℕ} (A : Square N) :
    PiLp 2 (fun _ : Fin N => PiLp 2 (fun _ : Fin N => ℂ)) :=
  ((↑(Real.sqrt N) : ℂ)⁻¹) • vecHS A

private lemma normalizedVec_inner_eq {N : ℕ} (_hN : 0 < N) (A B : Square N) :
    inner ℂ (normalizedVec A) (normalizedVec B) =
      ((N : ℂ)⁻¹) * Matrix.trace (A† * B) := by
  unfold normalizedVec
  rw [inner_smul_left, inner_smul_right, vecHS_inner_eq_trace]
  calc
    star ((↑(Real.sqrt N) : ℂ)⁻¹) * (((↑(Real.sqrt N) : ℂ)⁻¹) * Matrix.trace (A† * B))
        = (star ((↑(Real.sqrt N) : ℂ)⁻¹) * ((↑(Real.sqrt N) : ℂ)⁻¹)) * Matrix.trace (A† * B) := by
            ring
    _ = ((N : ℂ)⁻¹) * Matrix.trace (A† * B) := by rw [inv_sqrt_nat_sq_eq_inv]

private lemma normalizedVec_norm_one_of_unitary {N : ℕ} (hN : 0 < N)
    (U : Square N) (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ‖normalizedVec U‖ = 1 := by
  have hinner : inner ℂ (normalizedVec U) (normalizedVec U) = 1 := by
    have hUU : U† * U = (1 : Square N) := Matrix.mem_unitaryGroup_iff'.mp hU
    rw [normalizedVec_inner_eq hN]
    rw [hUU, Matrix.trace_one]
    simp only [Fintype.card_fin]
    have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    field_simp [hNne]
  exact norm_eq_one_of_inner_self_eq_one hinner

private theorem unit_vector_trace_inequality {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {x y z : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    Real.sqrt (1 - ‖inner ℂ x z‖ ^ 2) ≤
      Real.sqrt (1 - ‖inner ℂ x y‖ ^ 2) + Real.sqrt (1 - ‖inner ℂ y z‖ ^ 2) := by
  let a : ℝ := ‖inner ℂ x y‖
  let b : ℝ := ‖inner ℂ y z‖
  let c : ℝ := ‖inner ℂ x z‖
  let ux : ℂ := Complex.exp (Complex.arg (inner ℂ x y) * Complex.I)
  let uz : ℂ := Complex.exp (-(Complex.arg (inner ℂ y z)) * Complex.I)
  let x1 : E := ux • x
  let z1 : E := uz • z
  have hux_norm : ‖ux‖ = 1 := by
    dsimp [ux]
    exact Complex.norm_exp_ofReal_mul_I (Complex.arg (inner ℂ x y))
  have huz_norm : ‖uz‖ = 1 := by
    dsimp [uz]
    simpa [neg_mul] using Complex.norm_exp_ofReal_mul_I (-(Complex.arg (inner ℂ y z)))
  have hxy : inner ℂ x1 y = (a : ℂ) := by
    dsimp [x1, ux, a]
    rw [inner_smul_left]
    have hux_sq : star ux * ux = 1 := conj_mul_eq_one_of_norm_eq_one hux_norm
    have hpolar : inner ℂ x y = (a : ℂ) * ux := by
      dsimp [a, ux]
      exact (Complex.norm_mul_exp_arg_mul_I (inner ℂ x y)).symm
    calc
      star ux * inner ℂ x y = star ux * ((a : ℂ) * ux) := by rw [hpolar]
      _ = (a : ℂ) * (star ux * ux) := by ring
      _ = (a : ℂ) := by rw [hux_sq]; simp
  have hyz : inner ℂ y z1 = (b : ℂ) := by
    dsimp [z1, uz, b]
    rw [inner_smul_right]
    simpa [mul_assoc, mul_comm, mul_left_comm] using phase_align_mul (inner ℂ y z)
  have hx1_norm : ‖x1‖ = 1 := by
    dsimp [x1]
    rw [norm_smul, hux_norm, hx]
    norm_num
  have hz1_norm : ‖z1‖ = 1 := by
    dsimp [z1]
    rw [norm_smul, huz_norm, hz]
    norm_num
  have hxx1 : inner ℂ x1 x1 = 1 := inner_self_eq_one_of_norm_eq_one hx1_norm
  have hyy : inner ℂ y y = 1 := inner_self_eq_one_of_norm_eq_one hy
  have hzz1 : inner ℂ z1 z1 = 1 := inner_self_eq_one_of_norm_eq_one hz1_norm
  have hyx1 : inner ℂ y x1 = (a : ℂ) := by
    calc
      inner ℂ y x1 = star (inner ℂ x1 y) := by
        symm
        exact inner_conj_symm y x1
      _ = (a : ℂ) := by simp [hxy]
  have hz1y : inner ℂ z1 y = (b : ℂ) := by
    calc
      inner ℂ z1 y = star (inner ℂ y z1) := by
        symm
        exact inner_conj_symm z1 y
      _ = (b : ℂ) := by simp [hyz]
  have hx1z1_eq : inner ℂ x1 z1 = (uz * star ux) * inner ℂ x z := by
    dsimp [x1, z1, ux, uz]
    rw [inner_smul_left, inner_smul_right]
    ring
  have hx1z1_norm : ‖inner ℂ x1 z1‖ = c := by
    dsimp [c]
    rw [hx1z1_eq, norm_mul, norm_mul, norm_star, hux_norm, huz_norm, one_mul, one_mul]
  have ha_nonneg : 0 ≤ a := by dsimp [a]; exact norm_nonneg _
  have hb_nonneg : 0 ≤ b := by dsimp [b]; exact norm_nonneg _
  have hc_nonneg : 0 ≤ c := by dsimp [c]; exact norm_nonneg _
  let xPerp : E := x1 - (a : ℂ) • y
  let zPerp : E := z1 - (b : ℂ) • y
  have hxPerp_sq : ‖xPerp‖ ^ 2 = 1 - a ^ 2 := by
    dsimp [xPerp]
    rw [norm_sub_sq (𝕜 := ℂ), hx1_norm]
    change 1 ^ 2 - 2 * RCLike.re (inner ℂ x1 ((a : ℂ) • y)) + ‖((a : ℂ) • y)‖ ^ 2 = 1 - a ^ 2
    have hxy_re : RCLike.re (inner ℂ x1 ((a : ℂ) • y)) = a ^ 2 := by
      rw [inner_smul_right, hxy]
      simp [pow_two]
    have hsmul : ‖((a : ℂ) • y)‖ = a := by
      rw [norm_smul, hy, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha_nonneg]
    rw [hxy_re, hsmul]
    ring
  have hzPerp_sq : ‖zPerp‖ ^ 2 = 1 - b ^ 2 := by
    dsimp [zPerp]
    rw [norm_sub_sq (𝕜 := ℂ), hz1_norm]
    change 1 ^ 2 - 2 * RCLike.re (inner ℂ z1 ((b : ℂ) • y)) + ‖((b : ℂ) • y)‖ ^ 2 = 1 - b ^ 2
    have hz1y_re : RCLike.re (inner ℂ z1 ((b : ℂ) • y)) = b ^ 2 := by
      rw [inner_smul_right, hz1y]
      simp [pow_two]
    have hsmul : ‖((b : ℂ) • y)‖ = b := by
      rw [norm_smul, hy, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb_nonneg]
    rw [hz1y_re, hsmul]
    ring
  have hperp_inner : inner ℂ xPerp zPerp = inner ℂ x1 z1 - (a * b : ℂ) := by
    have hx1_by : inner ℂ x1 ((b : ℂ) • y) = (a * b : ℂ) := by
      rw [inner_smul_right, hxy]
      ring
    have hay_z1 : inner ℂ ((a : ℂ) • y) z1 = (a * b : ℂ) := by
      rw [inner_smul_left, hyz]
      simp
    have hay_by : inner ℂ ((a : ℂ) • y) ((b : ℂ) • y) = (a * b : ℂ) := by
      rw [inner_smul_left, inner_smul_right]
      simp [hy]
    calc
      inner ℂ xPerp zPerp
          = inner ℂ x1 z1 - inner ℂ x1 ((b : ℂ) • y) - inner ℂ ((a : ℂ) • y) z1
              + inner ℂ ((a : ℂ) • y) ((b : ℂ) • y) := by
                dsimp [xPerp, zPerp]
                rw [inner_sub_left, inner_sub_right, inner_sub_right]
                ring
      _ = inner ℂ x1 z1 - (a * b : ℂ) - (a * b : ℂ) + (a * b : ℂ) := by
            rw [hx1_by, hay_z1, hay_by]
      _ = inner ℂ x1 z1 - (a * b : ℂ) := by ring
  have hperp_cauchy : ‖inner ℂ xPerp zPerp‖ ≤ ‖xPerp‖ * ‖zPerp‖ :=
    norm_inner_le_norm _ _
  have hperp_cauchy_sq : ‖inner ℂ xPerp zPerp‖ ^ 2 ≤ (1 - a ^ 2) * (1 - b ^ 2) := by
    calc
      ‖inner ℂ xPerp zPerp‖ ^ 2 = ‖inner ℂ xPerp zPerp‖ * ‖inner ℂ xPerp zPerp‖ := by ring
      _ ≤ (‖xPerp‖ * ‖zPerp‖) * (‖xPerp‖ * ‖zPerp‖) := by
            exact mul_self_le_mul_self (norm_nonneg (inner ℂ xPerp zPerp)) hperp_cauchy
      _ = (‖xPerp‖ ^ 2) * (‖zPerp‖ ^ 2) := by ring
      _ = (1 - a ^ 2) * (1 - b ^ 2) := by rw [hxPerp_sq, hzPerp_sq]
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    calc
      ‖inner ℂ x y‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hx, hy]; norm_num
  have hb_le_one : b ≤ 1 := by
    dsimp [b]
    calc
      ‖inner ℂ y z‖ ≤ ‖y‖ * ‖z‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hy, hz]; norm_num
  have hc_le_one : c ≤ 1 := by
    dsimp [c]
    calc
      ‖inner ℂ x z‖ ≤ ‖x‖ * ‖z‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hx, hz]; norm_num
  have hprod_nonneg : 0 ≤ (1 - a ^ 2) * (1 - b ^ 2) := by
    have ha_sq_le_one : a ^ 2 ≤ 1 := sq_le_one_of_nonneg_le_one ha_nonneg ha_le_one
    have hb_sq_le_one : b ^ 2 ≤ 1 := sq_le_one_of_nonneg_le_one hb_nonneg hb_le_one
    have hxa : 0 ≤ 1 - a ^ 2 := by linarith
    have hyb : 0 ≤ 1 - b ^ 2 := by linarith
    exact mul_nonneg hxa hyb
  have habc_norm : ‖inner ℂ x1 z1 - (a * b : ℂ)‖ ≤ Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) := by
    rw [← hperp_inner]
    have hsqrt_sq : (Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2))) ^ 2 = (1 - a ^ 2) * (1 - b ^ 2) := by
      rw [Real.sq_sqrt hprod_nonneg]
    have hsq : ‖inner ℂ xPerp zPerp‖ ^ 2 ≤ (Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2))) ^ 2 := by
      simpa [hsqrt_sq] using hperp_cauchy_sq
    have habs := (sq_le_sq.mp hsq)
    simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)] using habs
  have habc_norm_rev : ‖(a * b : ℂ) - inner ℂ x1 z1‖ ≤ Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) := by
    simpa [norm_sub_rev] using habc_norm
  have hab_sub_c : a * b - c ≤ Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) := by
    have htri := norm_add_le ((a * b : ℂ) - inner ℂ x1 z1) (inner ℂ x1 z1)
    have htri' : a * b ≤ ‖(a * b : ℂ) - inner ℂ x1 z1‖ + c := by
      rw [show ((a * b : ℂ) - inner ℂ x1 z1) + inner ℂ x1 z1 = (a * b : ℂ) by ring] at htri
      simpa [hx1z1_norm, RCLike.norm_ofReal, abs_mul, abs_of_nonneg ha_nonneg,
        abs_of_nonneg hb_nonneg, abs_of_nonneg (mul_nonneg ha_nonneg hb_nonneg)] using htri
    have hbound : a * b ≤ Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) + c := by
      have hnorm : ‖(a * b : ℂ) - inner ℂ x1 z1‖ + c ≤ Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) + c := by
        simpa [add_comm] using add_le_add_right habc_norm_rev c
      exact le_trans htri' hnorm
    linarith
  have hc_sub_ab : c - a * b ≤ Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) := by
    have htri := norm_add_le (inner ℂ x1 z1 - (a * b : ℂ)) (a * b : ℂ)
    have htri' : c ≤ ‖inner ℂ x1 z1 - (a * b : ℂ)‖ + a * b := by
      rw [show (inner ℂ x1 z1 - (a * b : ℂ)) + (a * b : ℂ) = inner ℂ x1 z1 by ring] at htri
      simpa [hx1z1_norm, RCLike.norm_ofReal, abs_mul, abs_of_nonneg ha_nonneg,
        abs_of_nonneg hb_nonneg, abs_of_nonneg (mul_nonneg ha_nonneg hb_nonneg)] using htri
    have hbound : c ≤ Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) + a * b := by
      have hnorm : ‖inner ℂ x1 z1 - (a * b : ℂ)‖ + a * b ≤ Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) + a * b := by
        simpa [add_comm] using add_le_add_right habc_norm (a * b)
      exact le_trans htri' hnorm
    linarith
  let sx : ℝ := Real.sqrt (1 - a ^ 2)
  let sy : ℝ := Real.sqrt (1 - b ^ 2)
  have hsx_sq : sx ^ 2 = 1 - a ^ 2 := by
    dsimp [sx]
    have ha_sq_le_one : a ^ 2 ≤ 1 := sq_le_one_of_nonneg_le_one ha_nonneg ha_le_one
    have hxa : 0 ≤ 1 - a ^ 2 := by linarith
    rw [Real.sq_sqrt hxa]
  have hsy_sq : sy ^ 2 = 1 - b ^ 2 := by
    dsimp [sy]
    have hb_sq_le_one : b ^ 2 ≤ 1 := sq_le_one_of_nonneg_le_one hb_nonneg hb_le_one
    have hyb : 0 ≤ 1 - b ^ 2 := by linarith
    rw [Real.sq_sqrt hyb]
  have hsqrt_mul : Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) = sx * sy := by
    dsimp [sx, sy]
    have ha_sq_le_one : a ^ 2 ≤ 1 := sq_le_one_of_nonneg_le_one ha_nonneg ha_le_one
    have hb_sq_le_one : b ^ 2 ≤ 1 := sq_le_one_of_nonneg_le_one hb_nonneg hb_le_one
    have hxa : 0 ≤ 1 - a ^ 2 := by linarith
    simpa using (Real.sqrt_mul hxa (1 - b ^ 2))
  have habc_abs : |a * b - c| ≤ sx * sy := by
    rw [← hsqrt_mul]
    exact abs_le.mpr ⟨by linarith [hc_sub_ab], hab_sub_c⟩
  have hmul_abs : (a * b - c) * (a * b + c) ≤ |a * b - c| * (a * b + c) := by
    apply mul_le_mul_of_nonneg_right (le_abs_self (a * b - c))
    have hab_nonneg : 0 ≤ a * b := mul_nonneg ha_nonneg hb_nonneg
    linarith
  have habc_mul : |a * b - c| * (a * b + c) ≤ (sx * sy) * (a * b + c) := by
    apply mul_le_mul_of_nonneg_right habc_abs
    have hab_nonneg : 0 ≤ a * b := mul_nonneg ha_nonneg hb_nonneg
    linarith
  have hsq : 1 - c ^ 2 ≤ (sx + sy) ^ 2 := by
    have hab_le_one : a * b ≤ 1 := by
      have hab_le_b : a * b ≤ b := by
        simpa using (mul_le_mul_of_nonneg_right ha_le_one hb_nonneg)
      linarith
    have hsxsy_nonneg : 0 ≤ sx * sy := by
      dsimp [sx, sy]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hupper : (1 - a ^ 2 * b ^ 2) + (sx * sy) * (a * b + c) ≤ (sx + sy) ^ 2 := by
      have hdecomp :
          (sx + sy) ^ 2 = (1 - a ^ 2 * b ^ 2) + (sx * sy) * (a * b + c) +
            (sx * sy) * (sx * sy + 2 - (a * b + c)) := by
        calc
          (sx + sy) ^ 2 = sx ^ 2 + 2 * sx * sy + sy ^ 2 := by ring
          _ = (1 - a ^ 2) + 2 * sx * sy + (1 - b ^ 2) := by rw [hsx_sq, hsy_sq]
          _ = (1 - a ^ 2 * b ^ 2) + (sx * sy) * (a * b + c) +
                (sx * sy) * (sx * sy + 2 - (a * b + c)) := by
                  ring_nf
                  rw [hsx_sq, hsy_sq]
                  ring
      have htail_nonneg : 0 ≤ (sx * sy) * (sx * sy + 2 - (a * b + c)) := by
        apply mul_nonneg hsxsy_nonneg
        linarith [hab_le_one, hc_le_one]
      linarith
    calc
      1 - c ^ 2 = (1 - a ^ 2 * b ^ 2) + (a * b - c) * (a * b + c) := by ring
      _ ≤ (1 - a ^ 2 * b ^ 2) + |a * b - c| * (a * b + c) := by linarith
      _ ≤ (1 - a ^ 2 * b ^ 2) + (sx * sy) * (a * b + c) := by linarith
      _ ≤ (sx + sy) ^ 2 := hupper
  have hleft_nonneg : 0 ≤ 1 - c ^ 2 := by
    have hc_sq_le_one : c ^ 2 ≤ 1 := sq_le_one_of_nonneg_le_one hc_nonneg hc_le_one
    linarith
  have hs_nonneg : 0 ≤ sx + sy := by
    dsimp [sx, sy]
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsqroot : (Real.sqrt (1 - c ^ 2)) ^ 2 ≤ (sx + sy) ^ 2 := by
    rw [Real.sq_sqrt hleft_nonneg]
    exact hsq
  have habs := (sq_le_sq.mp hsqroot)
  exact by
    simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hs_nonneg] using habs

/-- Hilbert-Schmidt distance used in `doc.tex`, specialized to square matrices. -/
noncomputable def hsDistance {N : ℕ} (U V : Square N) : ℝ :=
  Real.sqrt (1 - (‖Matrix.trace (U† * V)‖ ^ 2) / ((N : ℝ) ^ 2))

/-- Lemma 7 in `doc.tex`: the distance from a unitary to itself is zero. -/
theorem hsDistance_self {N : ℕ} (hN : 0 < N)
    (U : Square N) (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    hsDistance U U = 0 := by
  unfold hsDistance
  have hUU : U† * U = (1 : Square N) := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [hUU, Matrix.trace_one]
  simp only [Fintype.card_fin]
  rw [Complex.norm_natCast]
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hfrac : (N : ℝ) ^ 2 / (N : ℝ) ^ 2 = 1 := by
    field_simp [hNne]
  rw [hfrac]
  norm_num

/-- Global phase does not change the Hilbert-Schmidt distance. -/
theorem hsDistance_eq_zero_of_globalPhaseEquivalent {N : ℕ} (hN : 0 < N)
    {U V : Square N}
    (_hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (h : GlobalPhaseEquivalent U V) :
    hsDistance U V = 0 := by
  rcases h with ⟨z, hz, hUV⟩
  unfold hsDistance
  have hVV : V† * V = (1 : Square N) := Matrix.mem_unitaryGroup_iff'.mp hV
  have htrace : Matrix.trace (U† * V) = star z * (N : ℂ) := by
    calc
      Matrix.trace (U† * V) = Matrix.trace (((z • V)†) * V) := by rw [hUV]
      _ = Matrix.trace (((star z) • V†) * V) := by rw [Matrix.conjTranspose_smul]
      _ = Matrix.trace ((star z) • (V† * V)) := by rw [Matrix.smul_mul]
      _ = Matrix.trace ((star z) • (1 : Square N)) := by rw [hVV]
      _ = star z * (N : ℂ) := by
        rw [Matrix.trace_smul, Matrix.trace_one]
        simp
  rw [htrace]
  have hnorm : ‖star z * (N : ℂ)‖ = (N : ℝ) := by
    rw [norm_mul, norm_star, hz, Complex.norm_natCast, one_mul]
  rw [hnorm]
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hfrac : (N : ℝ) ^ 2 / (N : ℝ) ^ 2 = 1 := by
    field_simp [hNne]
  rw [hfrac]
  norm_num

/-- Lemma 8 in `doc.tex`: the trace inequality used for product-error bounds.

This is the external Wang-Zhang analytic inequality cited by the paper.  The
distance layer isolates it here as a single assumption and proves all circuit
error-accounting lemmas from that interface.
-/
theorem trace_inequality {N : ℕ} (hN : 0 < N)
    (U V : Square N)
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    Real.sqrt (1 - (‖Matrix.trace (U * V)‖ ^ 2) / ((N : ℝ) ^ 2)) ≤
      Real.sqrt (1 - (‖Matrix.trace U‖ ^ 2) / ((N : ℝ) ^ 2)) +
        Real.sqrt (1 - (‖Matrix.trace V‖ ^ 2) / ((N : ℝ) ^ 2)) := by
  let x := normalizedVec (U†)
  let y := normalizedVec (1 : Square N)
  let z := normalizedVec V
  have hx : ‖x‖ = 1 := by
    simpa [x] using normalizedVec_norm_one_of_unitary hN U† (TwoControl.conjTranspose_mem_unitaryGroup hU)
  have hy : ‖y‖ = 1 := by
    simpa [y] using normalizedVec_norm_one_of_unitary hN (1 : Square N) (Submonoid.one_mem _)
  have hz : ‖z‖ = 1 := by
    simpa [z] using normalizedVec_norm_one_of_unitary hN V hV
  have hmain := unit_vector_trace_inequality hx hy hz
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hxz : ‖inner ℂ x z‖ = ‖Matrix.trace (U * V)‖ / N := by
    dsimp [x, z]
    rw [normalizedVec_inner_eq hN]
    rw [Matrix.conjTranspose_conjTranspose, norm_mul, norm_inv, Complex.norm_natCast]
    simp [div_eq_mul_inv, mul_comm]
  have hxy : ‖inner ℂ x y‖ = ‖Matrix.trace U‖ / N := by
    dsimp [x, y]
    rw [normalizedVec_inner_eq hN]
    rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_one, norm_mul, norm_inv, Complex.norm_natCast]
    simp [div_eq_mul_inv, mul_comm]
  have hyz : ‖inner ℂ y z‖ = ‖Matrix.trace V‖ / N := by
    dsimp [y, z]
    rw [normalizedVec_inner_eq hN]
    rw [Matrix.conjTranspose_one, Matrix.one_mul, norm_mul, norm_inv, Complex.norm_natCast]
    simp [div_eq_mul_inv, mul_comm]
  simpa [hxz, hxy, hyz, one_sub_sq_div_nat_eq] using hmain

/-- Lemma 9 in `doc.tex`: errors of two multiplied unitary factors add. -/
theorem hsDistance_mul_le {N : ℕ} (hN : 0 < N)
    (U₁ U₂ V₁ V₂ : Square N)
    (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hU₂ : U₂ ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hV₁ : V₁ ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hV₂ : V₂ ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    hsDistance (U₁ * U₂) (V₁ * V₂) ≤
      hsDistance U₁ V₁ + hsDistance U₂ V₂ := by
  let A : Square N := U₁† * V₁
  let B : Square N := V₂ * U₂†
  have hA : A ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    exact Submonoid.mul_mem _ (TwoControl.conjTranspose_mem_unitaryGroup hU₁) hV₁
  have hB : B ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    exact Submonoid.mul_mem _ hV₂ (TwoControl.conjTranspose_mem_unitaryGroup hU₂)
  have htr_left : Matrix.trace ((U₂† * U₁†) * (V₁ * V₂)) = Matrix.trace (A * B) := by
    calc
      Matrix.trace ((U₂† * U₁†) * (V₁ * V₂))
          = Matrix.trace (U₂† * (U₁† * V₁) * V₂) := by
            congr 1
            simp [mul_assoc]
      _ = Matrix.trace (V₂ * U₂† * (U₁† * V₁)) := by
            rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace ((U₁† * V₁) * (V₂ * U₂†)) := by
            rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (A * B) := by rfl
  have htr_right : Matrix.trace B = Matrix.trace (U₂† * V₂) := by
    calc
      Matrix.trace B = Matrix.trace (V₂ * U₂†) := by rfl
      _ = Matrix.trace (U₂† * V₂) := Matrix.trace_mul_comm V₂ U₂†
  simpa [hsDistance, A, B, htr_left, htr_right, Matrix.conjTranspose_mul] using
    trace_inequality hN A B hA hB

private theorem circuitMatrix_mem_unitaryGroup {N : ℕ} (gates : List (Square N))
    (hgates : ∀ U ∈ gates, U ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    circuitMatrix gates ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  induction gates with
  | nil =>
      simp
  | cons gate gates ih =>
      simp [circuitMatrix]
      exact Submonoid.mul_mem _ (hgates gate (by simp))
        (ih (fun U hU => hgates U (by simp [hU])))

/-- Lemma 10 in `doc.tex`: errors of products of unitary factors add. -/
theorem hsDistance_circuitMatrix_le_sum {N : ℕ} (hN : 0 < N)
    (Us Vs : List (Square N))
    (hlen : Us.length = Vs.length)
    (hUs : ∀ U ∈ Us, U ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hVs : ∀ V ∈ Vs, V ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    hsDistance (circuitMatrix Us) (circuitMatrix Vs) ≤
      (List.zipWith (fun U V => hsDistance U V) Us Vs).sum := by
  induction Us generalizing Vs with
  | nil =>
      cases Vs with
      | nil =>
          simp [hsDistance_self hN (1 : Square N) (Submonoid.one_mem _)]
      | cons V Vs =>
          simp at hlen
  | cons U Us ih =>
      cases Vs with
      | nil =>
          simp at hlen
      | cons V Vs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          have hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ := hUs U (by simp)
          have hV : V ∈ Matrix.unitaryGroup (Fin N) ℂ := hVs V (by simp)
          have hUs_tail : ∀ W ∈ Us, W ∈ Matrix.unitaryGroup (Fin N) ℂ := by
            intro W hW
            exact hUs W (by simp [hW])
          have hVs_tail : ∀ W ∈ Vs, W ∈ Matrix.unitaryGroup (Fin N) ℂ := by
            intro W hW
            exact hVs W (by simp [hW])
          have hCU : circuitMatrix Us ∈ Matrix.unitaryGroup (Fin N) ℂ :=
            circuitMatrix_mem_unitaryGroup Us hUs_tail
          have hCV : circuitMatrix Vs ∈ Matrix.unitaryGroup (Fin N) ℂ :=
            circuitMatrix_mem_unitaryGroup Vs hVs_tail
          have hmul := hsDistance_mul_le hN U (circuitMatrix Us) V (circuitMatrix Vs)
            hU hCU hV hCV
          have htail := ih Vs hlen hUs_tail hVs_tail
          simp only [circuitMatrix_cons, List.zipWith_cons_cons, List.sum_cons]
          exact le_trans hmul (add_le_add (le_refl (hsDistance U V)) htail)

end Universal
end Clifford
end TwoControl

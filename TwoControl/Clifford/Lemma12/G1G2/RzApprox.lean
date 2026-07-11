import TwoControl.Clifford.Lemma12.G1G2.Orthogonality

namespace TwoControl
namespace Clifford
namespace Lemma12
namespace G1G2

open Universal
open Matrix

/-!
# `{H,T}` circuits approximate every `R_z` rotation

Paper Lemma `approximation-of-rz`, assembled from the `G₁/G₂` track of
`universal_new_gates.tex`:

1. `R_z(θ)` is a rotation about the standard `z`-axis
   (`rz_eq_axisRotation_standardZ`).
2. Since the axes of `G₁, G₂` are orthogonal (`g_axes_data`), the generalized
   Euler decomposition (`standardZ_axisRotation_orthogonal_euler`, paper
   Lemma `generalized-euler-decomposition` / `from-rz-to-g1-g2`) writes it as
   an exact three-factor product `R(n₁,a)·R(n₂,b)·R(n₁,c)`.
3. Each factor is approximated to `ε/3` by an integer power of the
   corresponding gate word (`axisRotation_powers_dense_smul`, paper Lemma
   `approximate-g1-a-g2-b`; the words realize `G₁, G₂` up to the global
   phase `gPhase`, which the distance ignores).
4. The three errors add up (`hsDistance_triple_mul_le`, paper Lemma
   `hs-big-product-rule`).
-/

/-- Paper Lemma `approximation-of-rz` (Lemma 12): for every angle `θ` and
`ε > 0` there is an `{H,T}` circuit within `ε` of `R_z(θ)` in
Hilbert-Schmidt distance. -/
theorem HT_rz_dense_g1g2 (θ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : HTCircuit, hsDistance (rz θ) (HTCircuit.eval C) < ε := by
  obtain ⟨n₁, n₂, α₁, α₂, hn₁, hn₂, hg1, hg2, hirr₁, hirr₂, hortho⟩ := g_axes_data
  obtain ⟨a, b, c, hEuler⟩ :=
    standardZ_axisRotation_orthogonal_euler n₁ n₂ hn₁ hn₂ hortho (-(θ / 2))
  have hε3 : 0 < ε / 3 := by positivity
  have hU1 : HTCircuit.eval g1Word = gPhase⁻¹ • axisRotation n₁ α₁ := by
    rw [g1Word_eval, hg1]
  have hU2 : HTCircuit.eval g2Word = gPhase⁻¹ • axisRotation n₂ α₂ := by
    rw [g2Word_eval, hg2]
  obtain ⟨k₁, hk₁⟩ := axisRotation_powers_dense_smul n₁ hn₁ (HTCircuit.eval g1Word)
    gPhase_inv_norm α₁ a hU1 hirr₁ hε3
  obtain ⟨k₂, hk₂⟩ := axisRotation_powers_dense_smul n₂ hn₂ (HTCircuit.eval g2Word)
    gPhase_inv_norm α₂ b hU2 hirr₂ hε3
  obtain ⟨k₃, hk₃⟩ := axisRotation_powers_dense_smul n₁ hn₁ (HTCircuit.eval g1Word)
    gPhase_inv_norm α₁ c hU1 hirr₁ hε3
  refine ⟨zpowCircuit g1Word k₁ ++ zpowCircuit g2Word k₂ ++ zpowCircuit g1Word k₃, ?_⟩
  have h1 : hsDistance (axisRotation n₁ a)
      (HTCircuit.eval (zpowCircuit g1Word k₁)) < ε / 3 := by
    rw [eval_zpowCircuit]
    exact hk₁
  have h2 : hsDistance (axisRotation n₂ b)
      (HTCircuit.eval (zpowCircuit g2Word k₂)) < ε / 3 := by
    rw [eval_zpowCircuit]
    exact hk₂
  have h3 : hsDistance (axisRotation n₁ c)
      (HTCircuit.eval (zpowCircuit g1Word k₃)) < ε / 3 := by
    rw [eval_zpowCircuit]
    exact hk₃
  rw [rz_eq_axisRotation_standardZ, hEuler, HTCircuit_eval_append,
    HTCircuit_eval_append]
  have hle :
      hsDistance
        (axisRotation n₁ a * axisRotation n₂ b * axisRotation n₁ c)
        (HTCircuit.eval (zpowCircuit g1Word k₁) *
          HTCircuit.eval (zpowCircuit g2Word k₂) *
            HTCircuit.eval (zpowCircuit g1Word k₃)) ≤
      hsDistance (axisRotation n₁ a) (HTCircuit.eval (zpowCircuit g1Word k₁)) +
        hsDistance (axisRotation n₂ b) (HTCircuit.eval (zpowCircuit g2Word k₂)) +
        hsDistance (axisRotation n₁ c) (HTCircuit.eval (zpowCircuit g1Word k₃)) :=
    hsDistance_triple_mul_le
      (axisRotation_mem_unitaryGroup n₁ hn₁ a)
      (HTCircuit_eval_mem_unitaryGroup _)
      (axisRotation_mem_unitaryGroup n₂ hn₂ b)
      (HTCircuit_eval_mem_unitaryGroup _)
      (axisRotation_mem_unitaryGroup n₁ hn₁ c)
      (HTCircuit_eval_mem_unitaryGroup _)
  exact lt_of_le_of_lt hle (by linarith [h1, h2, h3])

end G1G2
end Lemma12
end Clifford
end TwoControl

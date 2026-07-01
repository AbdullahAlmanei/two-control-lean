import TwoControl.Clifford.Lemma12.MainTheorem
import TwoControl.Clifford.Lemma12.LogPrecision

namespace TwoControl
namespace Clifford
namespace Lemma12

open TwoControl.Clifford.Universal

/-!
Quantitative Lemma 12 interface.

The compactness-only scaffold has been removed: it gave a finite bound for each
epsilon but no closed form.  The intended proof route for this file is the
Ross-Selinger/KMM path:

* solve the one-qubit `R_z` approximation problem with logarithmic T-count;
* convert the resulting exact one-qubit Clifford+T circuit to the existing
  `{H,T}` primitive list with only linear overhead;
* measure the result using the project's Hilbert-Schmidt distance.

The constants are deliberately abstract.  The useful theorem is the shape:
`length <= A * (logPrecision epsilon + 1) + B`.
-/

/-- Ross-Selinger-style logarithmic synthesis, stated directly in the project's
`{H,T}` one-qubit circuit alphabet and Hilbert-Schmidt distance.

This is the quantitative heart of Lemma 12.  The constants are global: they do
not depend on the angle or on `epsilon`. -/
theorem exists_rz_approximation_by_ht_log_length_constants :
    ∃ constants : ℕ × ℕ,
      0 < constants.1 ∧
      ∀ (theta : ℝ) {epsilon : ℝ}, 0 < epsilon →
        ∃ gates : List OneQubitHTPrimitive,
          hsDistance (rz theta) (oneQubitHTCircuitMatrix gates) < epsilon ∧
          gates.length ≤
            constants.1 * (logPrecision epsilon + 1) + constants.2 := by
  sorry

/-- Global slope in the one-qubit logarithmic `R_z` approximation bound. -/
noncomputable def rzApproxLogSlope : ℕ :=
  (Classical.choose exists_rz_approximation_by_ht_log_length_constants).1

/-- Global additive constant in the one-qubit logarithmic `R_z` approximation
bound. -/
noncomputable def rzApproxLogIntercept : ℕ :=
  (Classical.choose exists_rz_approximation_by_ht_log_length_constants).2

theorem rzApproxLogSlope_pos : 0 < rzApproxLogSlope := by
  dsimp [rzApproxLogSlope]
  exact (Classical.choose_spec
    exists_rz_approximation_by_ht_log_length_constants).1

/-- The bounded form of Lemma 12 used by the universal theorem. -/
theorem lemma12_rz_approximation_by_ht_log_bounded
    (theta : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ gates : List OneQubitHTPrimitive,
      hsDistance (rz theta) (oneQubitHTCircuitMatrix gates) < epsilon ∧
      gates.length ≤
        rzApproxLogSlope * (logPrecision epsilon + 1) +
          rzApproxLogIntercept := by
  dsimp [rzApproxLogSlope, rzApproxLogIntercept]
  exact (Classical.choose_spec
    exists_rz_approximation_by_ht_log_length_constants).2 theta hepsilon

/-- The original qualitative Lemma 12 follows from the quantitative interface. -/
theorem lemma12_rz_approximation_by_ht_from_log_bound
    (theta : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ gates : List OneQubitHTPrimitive,
      hsDistance (rz theta) (oneQubitHTCircuitMatrix gates) < epsilon := by
  rcases lemma12_rz_approximation_by_ht_log_bounded theta hepsilon with
    ⟨gates, hDistance, _hLength⟩
  exact ⟨gates, hDistance⟩

end Lemma12
end Clifford
end TwoControl

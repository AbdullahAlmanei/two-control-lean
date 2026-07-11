import TwoControl.Clifford.Universal.RzApproximation
import TwoControl.Clifford.Universal.BoundedSynthesis
import TwoControl.Clifford.Lemma12.Bounded

namespace TwoControl
namespace Clifford
namespace Universal

/-!
Length-preserving lifting of the quantitative Lemma 12 interface through the
existing embedding API.
-/

theorem length_embedOneQubitHTCircuit {n : ℕ}
    (p : OneQubitPlacement n) (gates : List OneQubitHTPrimitive) :
    (embedOneQubitHTCircuit p gates).length = gates.length := by
  simp [embedOneQubitHTCircuit]

theorem length_embedTwoQubitCliffordTCircuit {n : ℕ}
    (p : TwoQubitPlacement n) (gates : List TwoQubitCliffordTPrimitive) :
    (embedTwoQubitCliffordTCircuit p gates).length = gates.length := by
  simp [embedTwoQubitCliffordTCircuit]

theorem length_map_onFirst (gates : List OneQubitHTPrimitive) :
    (gates.map TwoQubitCliffordTPrimitive.onFirst).length = gates.length := by
  simp

theorem length_map_onSecond (gates : List OneQubitHTPrimitive) :
    (gates.map TwoQubitCliffordTPrimitive.onSecond).length = gates.length := by
  simp

/-- Embedded logarithmic Lemma 12 for replacing one `R_z` gate inside an
`n`-qubit circuit. -/
theorem embedded_rz_approximation_by_clifford_t_log_bounded {n : ℕ}
    {R : Square (2 ^ n)} {theta delta : ℝ}
    (hdelta : 0 < delta)
    (hR : IsEmbeddedOneQubitGate n (rz theta) R) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      hsDistance R (circuitMatrix gates) < delta ∧
      gates.length ≤
        TwoControl.Clifford.Lemma12.rzApproxLogSlope *
            (TwoControl.Clifford.Lemma12.logPrecision delta + 1) +
          TwoControl.Clifford.Lemma12.rzApproxLogIntercept := by
  sorry

end Universal
end Clifford
end TwoControl

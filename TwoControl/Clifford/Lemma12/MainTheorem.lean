import TwoControl.Clifford.Lemma12.G1G2.RzApprox

namespace TwoControl
namespace Clifford
namespace Lemma12

open TwoControl.Clifford.Universal

/-!
# Lemma 12: {H,T} approximates arbitrary Rz rotations

Every `R_z(θ)` is approximable by `{H,T}` circuits in Hilbert-Schmidt
distance.

The proof follows `reference/cliff/universal_new_gates.tex` (July 2026):
the gates `G₁ = e^{-3iπ/8}·THTHT` and `G₂ = (HT⁴)·G₁·(HT⁴)†` are rotations
by a common irrational angle about *orthogonal* axes
(`G1G2/Generators.lean`, `G1G2/AngleIdentification.lean`,
`G1G2/Orthogonality.lean`), so the two-axis Euler decomposition expresses
any `R_z` exactly as a three-factor product, and integer powers of the
`G₁, G₂` gate words approximate each factor (`G1G2/RzApprox.lean`).
-/

/-- **Lemma 12**: `{H,T}` approximates every `R_z(θ)` to arbitrary
Hilbert-Schmidt precision.

This is the main universality result needed for Clifford+T compilation:
given any z-rotation and any precision ε > 0, there exists an HT circuit
that approximates it within ε in Hilbert-Schmidt distance. -/
theorem lemma12_rz_approximation_by_ht
    (θ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List OneQubitHTPrimitive,
      hsDistance (rz θ) (oneQubitHTCircuitMatrix gates) < ε := by
  simpa [HTCircuit.eval] using G1G2.HT_rz_dense_g1g2 θ hε

end Lemma12
end Clifford
end TwoControl

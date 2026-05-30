import TwoControl.Clifford.Lemma12.Boykin.BoykinDensity

namespace TwoControl
namespace Clifford
namespace Lemma12

open TwoControl.Clifford.Universal

/-!
# Lemma 12: {H,T} approximates arbitrary Rz rotations

Lemma 12 of `doc.tex`: every `R_z(θ)` is approximable by `{H,T}` circuits in
Hilbert-Schmidt distance.

The proof now uses the Boykin-style density theorem `HT_Rz_dense`, which proves
that {H,T} circuits are dense in SU(2) by constructing irrational rotations
around orthogonal axes.

The proof path here is Boykin's concrete irrational-rotation construction,
specialized to the z rotations needed by Lemma 12.
-/

/-- **Lemma 12** in `doc.tex`: `{H,T}` approximates every `R_z(θ)` to arbitrary
Hilbert-Schmidt precision.

This is the main universality result needed for Clifford+T compilation:
given any z-rotation and any precision ε > 0, there exists an HT circuit
that approximates it within ε in Hilbert-Schmidt distance. -/
theorem lemma12_rz_approximation_by_ht
    (θ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List OneQubitHTPrimitive,
      hsDistance (rz θ) (oneQubitHTCircuitMatrix gates) < ε := by
  simpa [HTCircuit.eval] using HT_Rz_dense θ hε

end Lemma12
end Clifford
end TwoControl

import DyadicCyclotomic.Basic

namespace RossSelinger

open TwoControl
open DyadicCyclotomic

/-- The Diophantine right-hand side `ξ = 1 - u†u`. -/
noncomputable def completionXi (u : ℂ) : ℂ :=
  1 - star u * u

/-- `t` solves the Ross-Selinger norm equation for `ξ`. -/
def SolvesNormEquation (ξ t : ℂ) : Prop :=
  InDyadicCyclotomic t ∧ star t * t = ξ

end RossSelinger

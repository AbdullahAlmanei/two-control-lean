import RossSelinger.Correctness

namespace RossSelinger

/-!
Optional oracle-facing adapter.

The older version of this file tried to prove an unconditional existence
statement for a completable candidate and then synthesized a circuit from that
existence proof.  That is not the conditional Ross-Selinger compiler boundary:
candidate generation, factorization, and termination live in the oracle
contract, while correctness is claimed only when a finite-fuel search actually
returns.
-/

/-- Circuit-language consequence of a returned factoring-oracle search. -/
theorem ross_selinger_Rz_approx_oracle_if_returns
    (oracle : RSOracleSolver)
    (fuel : ℕ)
    (input : RSInput)
    {C : CliffordTCircuit}
    (hrun : rossSelingerOracleSearch oracle fuel input = some C) :
    IsRzApproxCircuit input.θ input.ε C :=
  rossSelingerOracleSearch_sound_if_returns oracle fuel input hrun

end RossSelinger

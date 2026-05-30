import TwoControl.Clifford.Universal.GateSets
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace TwoControl.RossSelinger

open TwoControl.Clifford
open scoped Matrix.Norms.L2Operator

/-!
Basic Ross-Selinger-side vocabulary for the conditional Ross-Selinger
compiler leg.  This file deliberately contains only definitions and
lightweight circuit algebra; the algorithm, conditional correctness, and
conditional `T`-count optimality live in `Algorithm.lean`, `Correctness.lean`,
and `Optimality.lean` respectively.
-/

/-- One-qubit gates used by the Ross-Selinger approximation theorem.  The
paper works with Clifford+T plus a scalar `ω = exp(iπ/4)`. -/
inductive RossSelingerPrimitive where
  | h
  | s
  | t
  | omega
deriving DecidableEq

/-- Matrix semantics of the Ross-Selinger one-qubit gate alphabet. -/
noncomputable def RossSelingerPrimitive.eval : RossSelingerPrimitive → Square 2
  | .h => hadamard2
  | .s => phaseS
  | .t => phaseT
  | .omega => Complex.exp (Complex.I * (Real.pi / 4)) • (1 : Square 2)

/-- One-qubit Clifford+T circuits in the Ross-Selinger branch. -/
abbrev CliffordTCircuit := List RossSelingerPrimitive

/-- Number of `T` gates in a Ross-Selinger one-qubit Clifford+T circuit. -/
def TCount : CliffordTCircuit → ℕ
  | [] => 0
  | gate :: rest =>
    (match gate with
      | .t => 1
      | _  => 0) + TCount rest

@[simp] theorem TCount_nil : TCount [] = 0 := rfl

@[simp] theorem TCount_cons (gate : RossSelingerPrimitive) (rest : CliffordTCircuit) :
    TCount (gate :: rest) =
      (match gate with
        | .t => 1
        | _ => 0) + TCount rest := rfl

theorem TCount_append (left right : CliffordTCircuit) :
    TCount (left ++ right) = TCount left + TCount right := by
  induction left with
  | nil => simp
  | cons gate left ih =>
      cases gate <;> simp [ih, Nat.add_assoc]

theorem TCount_replicate_t (n : ℕ) :
    TCount (List.replicate n RossSelingerPrimitive.t) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ]
      simp [ih, Nat.add_comm]

theorem TCount_replicate_omega (n : ℕ) :
    TCount (List.replicate n RossSelingerPrimitive.omega) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ]
      simp [ih]

/-- Ross-Selinger's preferred `T`-count at denominator level `k`: the paper's
`k = 0` base case and its `2k - 2` branch for positive `k`. -/
def rossLevelTCount (k : ℕ) : ℕ :=
  if k = 0 then 0 else 2 * k - 2

/-- The Ross-Selinger returned-branch T-count bound is monotone in the
denominator level. -/
theorem rossLevelTCount_mono {k l : ℕ} (hkl : k ≤ l) :
    rossLevelTCount k ≤ rossLevelTCount l := by
  unfold rossLevelTCount
  by_cases hk : k = 0
  · simp [hk]
  · have hl : l ≠ 0 := by omega
    simp [hk, hl]
    omega

namespace CliffordTCircuit

/-- Matrix semantics of a Ross-Selinger one-qubit circuit. -/
noncomputable def eval (gates : CliffordTCircuit) : Square 2 :=
  gates.foldr (fun gate acc => RossSelingerPrimitive.eval gate * acc) 1

@[simp] theorem eval_nil : eval [] = (1 : Square 2) := by
  rfl

@[simp] theorem eval_cons (gate : RossSelingerPrimitive) (gates : CliffordTCircuit) :
    eval (gate :: gates) = RossSelingerPrimitive.eval gate * eval gates := by
  rfl

theorem eval_append (left right : CliffordTCircuit) :
    eval (left ++ right) = eval left * eval right := by
  induction left with
  | nil => simp [eval]
  | cons gate left ih =>
      calc
        eval ((gate :: left) ++ right)
            = RossSelingerPrimitive.eval gate * eval (left ++ right) := by
                simp [eval]
        _ = RossSelingerPrimitive.eval gate * (eval left * eval right) := by
                rw [ih]
        _ = eval (gate :: left) * eval right := by
                simp [eval, mul_assoc]

end CliffordTCircuit

end RossSelinger
end TwoControl

import TwoControl.CosineSine.Definitions
import TwoControl.Definitions
import TwoControl.GateHelpers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential

open Matrix

namespace TwoControl
namespace Clifford

/-- The standard one-qubit Hadamard gate. -/
noncomputable def hadamard2 : Square 2 :=
  (((1 / Real.sqrt 2 : ℝ) : ℂ)) • Matrix.of ![![1, 1], ![1, -1]]

/-- The phase gate `S = diag(1, i)`. -/
def phaseS : Square 2 :=
  diag2 1 Complex.I

/-- The adjoint phase gate `S† = diag(1, -i)`. -/
def phaseSdagger : Square 2 :=
  diag2 1 (-Complex.I)

/-- The phase gate `T = diag(1, exp(i pi / 4))`. -/
noncomputable def phaseT : Square 2 :=
  diag2 1 (Complex.exp (Complex.I * (Real.pi / 4)))

/-- The one-qubit phase gate `P(φ) = diag(1, exp(i φ))`. -/
noncomputable def phaseShift (φ : ℝ) : Square 2 :=
  diag2 1 (Complex.exp (Complex.I * φ))

/-- The one-qubit `R_z` rotation in matrix form. -/
noncomputable def rz (θ : ℝ) : Square 2 :=
  diag2 (Complex.exp (-Complex.I * (θ / 2))) (Complex.exp (Complex.I * (θ / 2)))

/-- Alias for the standard CNOT gate already available in the helper layer. -/
def cnot : Square 4 :=
  GateHelpers.notc

/-- Promote a one-qubit gate to the first tensor factor. -/
noncomputable def localOnFirst (U : Square 2) : Square 4 :=
  U ⊗ₖ (1 : Square 2)

/-- Promote a one-qubit gate to the second tensor factor. -/
noncomputable def localOnSecond (U : Square 2) : Square 4 :=
  (1 : Square 2) ⊗ₖ U

/-- Controlled-U with the control on the second tensor factor. -/
noncomputable def reverseControlledGate (U : Square 2) : Square 4 :=
  swap2 * controlledGate U * swap2

/-- A conditional `R_z` pair, matching the middle factor used in the Clifford track. -/
noncomputable def controlledRzPair (α₀ α₁ : ℝ) : Square 4 :=
  rz α₀ ⊗ₖ proj0 + rz α₁ ⊗ₖ proj1

/-- One-qubit primitives allowed in the local Clifford Lemma 11 track. -/
inductive OneQubitPrimitive where
  | h
  | t
  | rz (θ : ℝ)

/-- Matrix semantics for one-qubit primitives. -/
noncomputable def OneQubitPrimitive.eval : OneQubitPrimitive → Square 2
  | .h => hadamard2
  | .t => phaseT
  | .rz θ => Clifford.rz θ

/-- Compose a list of one-qubit primitives from left to right as a circuit matrix. -/
noncomputable def oneQubitCircuitMatrix (gates : List OneQubitPrimitive) : Square 2 :=
  gates.foldr (fun gate acc => OneQubitPrimitive.eval gate * acc) 1

@[simp] theorem oneQubitCircuitMatrix_nil :
    oneQubitCircuitMatrix [] = (1 : Square 2) := by
  rfl

@[simp] theorem oneQubitCircuitMatrix_cons (gate : OneQubitPrimitive)
    (gates : List OneQubitPrimitive) :
    oneQubitCircuitMatrix (gate :: gates) =
      OneQubitPrimitive.eval gate * oneQubitCircuitMatrix gates := by
  rfl

theorem oneQubitCircuitMatrix_append (left right : List OneQubitPrimitive) :
    oneQubitCircuitMatrix (left ++ right) =
      oneQubitCircuitMatrix left * oneQubitCircuitMatrix right := by
  induction left with
  | nil => simp [oneQubitCircuitMatrix]
  | cons gate left ih =>
      calc
        oneQubitCircuitMatrix ((gate :: left) ++ right)
            = OneQubitPrimitive.eval gate * oneQubitCircuitMatrix (left ++ right) := by
                simp [oneQubitCircuitMatrix]
        _ = OneQubitPrimitive.eval gate *
              (oneQubitCircuitMatrix left * oneQubitCircuitMatrix right) := by
                rw [ih]
        _ = oneQubitCircuitMatrix (gate :: left) * oneQubitCircuitMatrix right := by
                simp [oneQubitCircuitMatrix, mul_assoc]

/-- Two-qubit primitives allowed in the local Clifford Lemma 11 track. -/
inductive TwoQubitPrimitive where
  | cnot
  | onFirst (gate : OneQubitPrimitive)
  | onSecond (gate : OneQubitPrimitive)

/-- Matrix semantics for two-qubit primitives. -/
noncomputable def TwoQubitPrimitive.eval : TwoQubitPrimitive → Square 4
  | .cnot => Clifford.cnot
  | .onFirst gate => localOnFirst (OneQubitPrimitive.eval gate)
  | .onSecond gate => localOnSecond (OneQubitPrimitive.eval gate)

/-- Compose a list of two-qubit primitives from left to right as a circuit matrix. -/
noncomputable def twoQubitCircuitMatrix (gates : List TwoQubitPrimitive) : Square 4 :=
  gates.foldr (fun gate acc => TwoQubitPrimitive.eval gate * acc) 1

@[simp] theorem twoQubitCircuitMatrix_nil :
    twoQubitCircuitMatrix [] = (1 : Square 4) := by
  rfl

@[simp] theorem twoQubitCircuitMatrix_cons (gate : TwoQubitPrimitive)
    (gates : List TwoQubitPrimitive) :
    twoQubitCircuitMatrix (gate :: gates) =
      TwoQubitPrimitive.eval gate * twoQubitCircuitMatrix gates := by
  rfl

theorem twoQubitCircuitMatrix_append (left right : List TwoQubitPrimitive) :
    twoQubitCircuitMatrix (left ++ right) =
      twoQubitCircuitMatrix left * twoQubitCircuitMatrix right := by
  induction left with
  | nil => simp [twoQubitCircuitMatrix]
  | cons gate left ih =>
      calc
        twoQubitCircuitMatrix ((gate :: left) ++ right)
            = TwoQubitPrimitive.eval gate * twoQubitCircuitMatrix (left ++ right) := by
                simp [twoQubitCircuitMatrix]
        _ = TwoQubitPrimitive.eval gate *
              (twoQubitCircuitMatrix left * twoQubitCircuitMatrix right) := by
                rw [ih]
        _ = twoQubitCircuitMatrix (gate :: left) * twoQubitCircuitMatrix right := by
                simp [twoQubitCircuitMatrix, mul_assoc]

/-- Lift a one-qubit circuit to the first tensor factor. -/
def liftFirst (gates : List OneQubitPrimitive) : List TwoQubitPrimitive :=
  gates.map TwoQubitPrimitive.onFirst

theorem twoQubitCircuitMatrix_liftFirst (gates : List OneQubitPrimitive) :
    twoQubitCircuitMatrix (liftFirst gates) = localOnFirst (oneQubitCircuitMatrix gates) := by
  induction gates with
  | nil =>
      simpa [liftFirst, localOnFirst, oneQubitCircuitMatrix, twoQubitCircuitMatrix] using
        (TwoControl.one_kron_one 2 2).symm
  | cons gate gates ih =>
      calc
        twoQubitCircuitMatrix (liftFirst (gate :: gates))
            = localOnFirst (OneQubitPrimitive.eval gate) *
                twoQubitCircuitMatrix (liftFirst gates) := by
                  simp [liftFirst, twoQubitCircuitMatrix, TwoQubitPrimitive.eval]
        _ = localOnFirst (OneQubitPrimitive.eval gate) *
              localOnFirst (oneQubitCircuitMatrix gates) := by
              rw [ih]
        _ = (OneQubitPrimitive.eval gate * oneQubitCircuitMatrix gates) ⊗ₖ
              ((1 : Square 2) * (1 : Square 2)) := by
              rw [show localOnFirst (OneQubitPrimitive.eval gate) =
                    OneQubitPrimitive.eval gate ⊗ₖ (1 : Square 2) by rfl,
                show localOnFirst (oneQubitCircuitMatrix gates) =
                    oneQubitCircuitMatrix gates ⊗ₖ (1 : Square 2) by rfl,
                ← kron_mul_two]
        _ = localOnFirst (oneQubitCircuitMatrix (gate :: gates)) := by
              simp [localOnFirst, oneQubitCircuitMatrix]

/-- Lift a one-qubit circuit to the second tensor factor. -/
def liftSecond (gates : List OneQubitPrimitive) : List TwoQubitPrimitive :=
  gates.map TwoQubitPrimitive.onSecond

theorem twoQubitCircuitMatrix_liftSecond (gates : List OneQubitPrimitive) :
    twoQubitCircuitMatrix (liftSecond gates) = localOnSecond (oneQubitCircuitMatrix gates) := by
  induction gates with
  | nil =>
      simpa [liftSecond, localOnSecond, oneQubitCircuitMatrix, twoQubitCircuitMatrix] using
        (TwoControl.one_kron_one 2 2).symm
  | cons gate gates ih =>
      calc
        twoQubitCircuitMatrix (liftSecond (gate :: gates))
            = localOnSecond (OneQubitPrimitive.eval gate) *
                twoQubitCircuitMatrix (liftSecond gates) := by
                  simp [liftSecond, twoQubitCircuitMatrix, TwoQubitPrimitive.eval]
        _ = localOnSecond (OneQubitPrimitive.eval gate) *
              localOnSecond (oneQubitCircuitMatrix gates) := by
              rw [ih]
        _ = ((1 : Square 2) * (1 : Square 2)) ⊗ₖ
              (OneQubitPrimitive.eval gate * oneQubitCircuitMatrix gates) := by
              rw [show localOnSecond (OneQubitPrimitive.eval gate) =
                    (1 : Square 2) ⊗ₖ OneQubitPrimitive.eval gate by rfl,
                show localOnSecond (oneQubitCircuitMatrix gates) =
                    (1 : Square 2) ⊗ₖ oneQubitCircuitMatrix gates by rfl,
                ← kron_mul_two]
        _ = localOnSecond (oneQubitCircuitMatrix (gate :: gates)) := by
              simp [localOnSecond, oneQubitCircuitMatrix]

end Clifford
end TwoControl
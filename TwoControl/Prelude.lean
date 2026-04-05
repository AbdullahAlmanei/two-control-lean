import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open scoped ComplexOrder

namespace TwoControl

/-! ## Type aliases for fixed-size complex matrices -/

abbrev Mat (n m : ℕ) := Matrix (Fin n) (Fin m) ℂ
abbrev Square (n : ℕ) := Mat n n
abbrev Vec (n : ℕ) := Fin n → ℂ

/-! ## Notation for conjugate transpose -/

scoped postfix:max "†" => Matrix.conjTranspose

/-! ## Kronecker product -/

/-- Kronecker product of square matrices, reindexed from `Fin m × Fin n` to `Fin (m * n)`. -/
noncomputable def kron (A : Square m) (B : Square n) : Square (m * n) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.kroneckerMap (· * ·) A B)

scoped infixl:71 " ⊗ₖ " => kron

end TwoControl

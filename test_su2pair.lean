import TwoControl.Clifford.Lemma12.Boykin.BoykinDensity

open Matrix Complex

lemma test_su2Pair_01 (a : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    (TwoControl.Clifford.Lemma12.su2Pair a u) 0 1 = Complex.I * (u 0 : ℂ) + (u 1 : ℂ) := by
  simp only [TwoControl.Clifford.Lemma12.su2Pair, TwoControl.Clifford.Lemma12.pauliVec,
             TwoControl.Clifford.Lemma12.pauliX, TwoControl.Clifford.Lemma12.pauliY,
             TwoControl.Clifford.Lemma12.pauliZ,
             Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue]
  trace "{goal}"
  sorry

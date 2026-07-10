# Lemma-by-lemma map: `universal_new_gates.tex` (July 2026) → Lean

Status 2026-07-10: complete. `lake build` green;
`#print axioms clifford_t_is_universal` = `[propext, Classical.choice,
Quot.sound]`; the dependency closure of the main theorem contains neither
Lemma 11, nor `EasyGate`'s arbitrary-two-qubit branch, nor any Boykin-track
declaration (the Boykin track was deleted).

Gate counts (`14·4^{n-1} − 9·2^{n-1}`, Lemma `rzcount`'s arithmetic) are out
of scope by prior agreement; the qualitative content of every paper lemma is
formalized.

## Main theorem and exact synthesis (paper Part 1–2)

| Paper | Lean | File |
|---|---|---|
| Theorem `clifford-plus-t-is-universal` | `clifford_t_is_universal` | `Universal/MainTheorem.lean` |
| Lemma `clifford-plus-rx-is-universal` (qualitative) | `clifford_rz_universal` | `Universal/RecursiveDecomposition.lean` |
| — gate set `{CX,H,S,S†,R_z}` | `CliffordRzGate` | `Universal/GateSets.lean` |
| Lemma `clifford-plus-rx-is-universal-for-1-qubit-gates` (N&C ZYZ) | `one_qubit_exact_clifford_rz` | `Clifford/Statements.lean` |
| Lemma `cosinesine` (Paige–Wei) | `general_cosine_sine_step` | `Universal/RecursiveDecomposition.lean` |
| Lemma `ryrz` (Shende–Markov–Bullock) | `hadamard_mul_rz_neg_mul_hadamard_eq_core`, `phaseSdagger_mul_core_mul_phaseS_eq_ry` | `Clifford/Statements.lean` |
| Lemma `demultiplexing` (Shende–Bullock–Markov) | `general_demultiplexing_step` | `Universal/RecursiveDecomposition.lean` |
| Lemma `rzrz` (Möttönen et al.) | `controlled_rz_reduction_step` | `Universal/RecursiveDecomposition.lean` |
| Lemma `rzcount` (qualitative content) | `synthesizes_controlled_rz_family_cliffordRz` | `Universal/RecursiveDecomposition.lean` |
| `S = T²`, `S† = T⁶` final conversion | `clifford_rz_to_clifford_t_rz` | `Universal/CliffordRz.lean` |
| (SWAP for wire plumbing, not in paper) `SWAP = CX·(H⊗H)·CX·(H⊗H)·CX` | `swap2_decomposition` | `Universal/RecursiveDecomposition.lean` |

## Distance layer (paper Lemmas 7–14)

| Paper | Lean | File |
|---|---|---|
| `hs-distance-to-itself-is-zero` | `hsDistance_self` | `Universal/Distance.lean` |
| `hs-distance-and-global-phase` | `hsDistance_smul_right`; `hsDistance_eq_of_globalPhaseEquivalent_left` | `Lemma12/G1G2/AxisRotation.lean`; `Universal/MainTheorem.lean` |
| `distance-equality-for-products` | `hsDistance_product_rearrange` | `Universal/Distance.lean` |
| `distance-to-identity` | `hsDistance_one_mul_mul`, `hsDistance_mul_mul_one` | `Universal/Distance.lean` |
| `distance-of-conjugated-unitaries` | `hsDistance_conjTranspose_symm` | `Universal/Distance.lean` |
| `trace-inequality` (Wang–Zhang) | `trace_inequality`; paper shape `hsDistance_le_hsDistance_one_add` | `Universal/Distance.lean` |
| `hs-small-product-rule` | `hsDistance_mul_le` (also `hsDistance_triple_mul_le`) | `Universal/Distance.lean`; `AxisRotation.lean` |
| `hs-big-product-rule` | `hsDistance_circuitMatrix_le_sum` | `Universal/Distance.lean` |

## Lemma 12: `R_z` approximation via `G₁, G₂` (paper Part 3)

| Paper | Lean | File |
|---|---|---|
| `G₁ = e^{-3iπ/8}·THTHT`, `G₂ = (HT⁴)G₁(HT⁴)†` | `g1`, `g2`, `g1Word`, `g2Word` | `Lemma12/G1G2/Generators.lean` |
| Lemma `properties-of-g1-g2` (det, trace) | `g1_det`, `g2_det`, `g1_trace_sq`, `g2_trace_sq`, `g1_g2_trace` | `Generators.lean` |
| Lemma `from-unitary-to-exponentiated-hamiltonian` (N&C Ex. 4.8) | `su2_eq_axisRotation` | `Lemma12/G1G2/SpectralForm.lean` |
| Lemma `trace-of-g1-and-trace-of-g2-expressed-via-alphas` | `trace_axisRotation` | `Lemma12/G1G2/AxisRotation.lean` |
| Lemma `a1-and-a2-anticommute` (orthogonal axes) | `g_axes_data` (inner-product clause) | `Lemma12/G1G2/Orthogonality.lean` |
| Lemma `generalized-euler-decomposition` (N&C Ex. 4.11, orthogonal axes) | `standardZ_axisRotation_orthogonal_euler`, `euler_product_expansion` | `AxisRotation.lean` |
| Lemma `from-rz-to-g1-g2` | instantiated in `HT_rz_dense_g1g2` (real powers kept as `axisRotation nᵢ (a·αᵢ)`) | `Lemma12/G1G2/RzApprox.lean` |
| Hardy–Wright density | `dense_addSubgroupClosure_pair_iff` (Mathlib) via `axisRotation_powers_dense` | `AxisRotation.lean` |
| Lemma `approximate-g-to-the-m-when-…-irr-multiple-of-pi` | `axisRotation_powers_dense`, phased form `axisRotation_powers_dense_smul` | `AxisRotation.lean` |
| Lemma `a-specific-lambda-is-irrational` | `irrational_div_two_pi_of_four_cos_sq` (sign-free form; reduces to `¬IsIntegral ℤ (1/2)`) | `Lemma12/G1G2/AngleIdentification.lean` |
| Lemma `approximate-g1-a-g2-b` | angle data + density instantiations in `HT_rz_dense_g1g2` | `AngleIdentification.lean`, `RzApprox.lean` |
| Lemma `approximation-of-rz` (Lemma 12) | `HT_rz_dense_g1g2`; wrapper `lemma12_rz_approximation_by_ht` | `RzApprox.lean`; `Lemma12/MainTheorem.lean` |
| `G₁⁻¹ ∼ T⁷HT⁷HT⁷` (negative powers) | `primitiveInvCircuit` (`T⁻¹ = T⁷`), `circuitInverse`, `zpowCircuit` | `AxisRotation.lean` |

Formalization deltas from the paper (all sound, noted for review):

* **Squares instead of signed traces.** The angle identification uses
  `(2cos α)² = 1 + 1/√2` rather than `Tr(Gᵢ) = √(1+1/√2)`; the paper's `λ` is
  never named and the sign of `cos αᵢ` is never computed.  The irrationality
  argument only consumes the square (`(x²−1)² = 1/2`), so this is exactly the
  paper's proof minus a redundant branch.  Every matrix computation stays in
  `ℚ(i, √2)` — no `π/8` trigonometry.
* **Orthogonality from one trace.** `⟪n₁,n₂⟫ = 0` is derived from
  `Tr(G₁G₂) = 1/2 + √2/4` plus a case split on the sign of
  `cos α₁ cos α₂` (the negative branch contradicts Cauchy–Schwarz), instead
  of computing the Hermitian generators.
* **Non-commutation of `G₁G₂`** (third clause of `properties-of-g1-g2`) is
  not formalized: it is subsumed by orthogonality, which is what the Euler
  decomposition actually consumes.
* **Global phases.** The circuit words realize `Gᵢ` up to the phase
  `e^{-3iπ/8}`; the density theorem absorbs it once
  (`axisRotation_powers_dense_smul`) since `hsDistance` is phase-invariant.
* The exact-synthesis half is stated up to global phase
  (`SynthesizesUpToGlobalPhase`), entering through the one-qubit base case,
  exactly as in the paper (`U ∼ C`).

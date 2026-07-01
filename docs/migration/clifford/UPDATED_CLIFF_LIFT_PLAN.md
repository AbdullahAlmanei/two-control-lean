# Plan: Lift the Clifford+T Universality Proof to `updated_cliff.tex` (June 2026)

Target reference: `reference/cliff/updated_cliff.tex`.
Old reference: `reference/cliff/doc.tex` (Mar 2025), which the current
formalization follows.

The updated paper proves the **same theorem** with the **same two ideas**
(irrational rotations give dense powers; two-axis Euler decomposition
transfers the axis), but repackages both halves:

* **Part A (exact synthesis):** one induction straight to
  `{CX, H, S, R_z}` with a one-qubit base case. Arbitrary two-qubit gates
  and Lemma 11 (Ross-Selinger) disappear from the chain.
* **Part B (R_z approximation):** the Boykin geometry (explicit axes,
  coordinate computations) is replaced by an abstract argument about
  `G₁ = e^{-iπ/4}·THTH` and `G₂ = e^{-iπ/4}·HTHT`, using only their
  determinant, trace, and non-commutation.

This plan lifts the formalization to that presentation while reusing every
proved component whose mathematical content is unchanged.

**Non-goals (explicitly out of scope):** all gate-count work
(`14·4^{n-1} − 9·2^{n-1}`, Lemma `rzcount`), and all `*Bounds.lean` /
`Bounded.lean` / `LogPrecision.lean` files. They stay untouched and must keep
compiling; nothing in this plan may rename or delete a declaration they use.

---

## 0. Erratum in the updated paper (must be fixed during the lift)

The paper's Lemma `generalized-euler-decomposition` (N&C Ex. 4.11) claims
that for **nonparallel** Hermitian axes `A₁, A₂`, every det-1 unitary is
`∼ e^{iaA₁} e^{ibA₂} e^{icA₁}` — a **three-factor** sandwich. This is false
for non-orthogonal axes, and the paper's own `G₁, G₂` have non-orthogonal
axes.

Verified analytically and numerically (2026-07-01):

* Writing `U = su2Pair(t, w)` and `k = ⟪n₁, n₂⟫`, the reachable set of
  `R(n₁,a)·R(n₂,b)·R(n₁,c)` is exactly `{ t² + ⟪w,n₁⟫² ≥ k² }`, because
  `t + i·⟪w,n₁⟫ = e^{i(a+c)}·(cos b + i·k·sin b)` and
  `|cos b + i·k·sin b|² = 1 − (1−k²)sin²b ∈ [k², 1]`.
* For `G₁, G₂`: `k = ⟪n₁,n₂⟫ ≈ 0.8420` (`k² ≈ 0.7089`, exact value
  `(2√2−1)/(5−2√2)`), while `n₁z² ≈ 0.4605`. So `R_z(π)` (where `t = 0`)
  violates the constraint; brute-force optimization confirms the best
  three-factor product stays at `hsDistance ≈ 0.254` from it.
* Sufficient condition for `R_z(θ)`:
  `cos²(θ/2) + sin²(θ/2)·n₁z² ≥ k²`; in particular `cos²(θ/2) ≥ k²`
  suffices, which holds whenever `|θ/2| ≤ 1/2` (since `cos²(1/2) ≈ 0.770`).

**Fix (angle splitting):** `rz θ = (rz (θ/N))^N` with `N := ⌈|θ|⌉ + 1`, so
each small factor is three-factor reachable. Approximate each of the `3N`
sandwich factors to `ε/(3N)` and use the existing product-distance bound.
This preserves the paper's ideas exactly; only the bookkeeping changes.
Also draft an erratum note for the paper author (separate deliverable, D6).

---

## 1. Ground-truth inventory (what exists today, all sorry-free)

| Component | Location | Status / role in lift |
|---|---|---|
| `hsDistance`, Lemmas 7–10 (self-zero, phase-invariance, Wang-Zhang `trace_inequality`, `hsDistance_mul_le`, `hsDistance_circuitMatrix_le_sum`) | `Universal/Distance.lean` | **Reuse verbatim.** Matches the paper's Lemmas 7–13 one-to-one. |
| Gate-set predicates `EasyGate`, `CliffordTRzGate`, `CliffordTGate`; placements, embeddings | `Universal/GateSets.lean` | Reuse; add one new predicate (B1). |
| CS decomposition step `general_cosine_sine_step` (any `n ≥ 1`) | `Universal/RecursiveDecomposition.lean` | **Reuse.** Already supports the `n = 2 → m = 1` case the new base needs. |
| SBM demultiplexing `general_demultiplexing_step` (`1 ≤ m`) | `RecursiveDecomposition.lean:1146` | **Reuse.** This is the paper's Lemma `demultiplexing`. |
| Möttönen recursion `controlled_rz_reduction_step` (`controlledRzFamily (m+1) = CX · lift R_β · CX · lift R_γ`, CX already typed `IsEmbeddedTwoQubitGate cnot`) | `RecursiveDecomposition.lean:~1949` | **Reuse.** This IS the paper's Lemma `rzrz` — already formalized. |
| `synthesizes_controlled_rz_family`, `synthesizes_controlled_ry_family`, `synthesizes_first_qubit_block_diag`, `liftLower/liftMiddle` lemmas | `RecursiveDecomposition.lean:2258–2366` | Retype from `EasyGate` to the new predicate (B3). |
| `lemma1_decomposition_to_easy_gate_set` (strong induction, base `n = 2` via `two_qubit_unitary_is_easy_gate`) | `RecursiveDecomposition.lean:2366` | Restructure: base moves to `n = 1` (B4). |
| Ry↔Rz bridge (`ryBridgeCore`: `H·rz(−θ)·H`, then `S†·_·S = ry θ`) | `Clifford/Statements.lean:71–125` | **Reuse.** This is the paper's Lemma `ryrz`. |
| One-qubit synthesis `one_qubit_exact_h_t_rz` (built from an internal `rz·ry·rz` ZYZ preparation) | `Statements.lean:1046` | Mine its internals for the new n=1 base case (B2). |
| Lemma 11 `lemma11_two_qubit_synthesis` + `clifford_rz_synthesis_from_lemma1` | `Statements.lean:1229`, `Universal/CliffordRz.lean:340` | **Drops off the main-theorem path.** Keep compiling (bounds files reference the `_bounded` variants). |
| `phaseT_sq_eq_phaseS` (`T² = S`), `phaseT_six_eq_phaseSdagger` (`T⁶ = S†`) | `Universal/CliffordRz.lean:21,43` | Reuse for the `S ↦ T²` final conversion (B5). |
| Boykin track: `su2Pair`, `su2Pair_mul`, `cross` algebra, `axisRotation`, `axisRotation_closed_form`, `pauliVec_sq_eq_one`, `axisRotation_powers_dense`, `rz_eq_axisRotation_standardZ`, `hsDistance_triple_mul_le`, `circuitPower/circuitInverse` | `Lemma12/Boykin/BoykinDensity.lean` | **Heavy reuse** in Phase A. The file stays; new track imports from it (or from a shared extraction). |
| `boykinLambda`, `boykinLambda_irrational` | `BoykinDensity.lean` | **Reuse verbatim** — the paper's λ is the same real number: `(1/2)(1+1/√2) = 1/2 + 1/(2√2)`. |
| Public wrapper `lemma12_rz_approximation_by_ht` | `Lemma12/MainTheorem.lean` | Statement frozen; proof re-pointed at the new track (D1). |
| Main theorem `clifford_t_is_universal` | `Universal/MainTheorem.lean` | Statement frozen; internals rewired (D2). |

Everything below EasyGate membership in the recursion already uses only
`{CX, H, S, S†, R_z}` **except** two spots:
`two_qubit_unitary_is_easy_gate` (the n=2 base — eliminated by B4) and
`topTwoUnitary m swap2` inside `synthesizes_liftMiddle`
(`RecursiveDecomposition.lean:2219` — needs the SWAP = 3-CNOT decomposition,
B3a).

---

## 2. Phase A — Lift Lemma 12 to the G₁/G₂ presentation

New directory: `TwoControl/Clifford/Lemma12/G1G2/`. The Boykin track stays
untouched and compiling until D1 flips the wrapper.

### A1. `G1G2/Generators.lean` — concrete gates and circuits

```lean
noncomputable def g1 : Square 2 :=
  Complex.exp (-(Complex.I * (Real.pi / 4))) • (phaseT * hadamard2 * phaseT * hadamard2)
noncomputable def g2 : Square 2 :=
  Complex.exp (-(Complex.I * (Real.pi / 4))) • (hadamard2 * phaseT * hadamard2 * phaseT)
```

Prove (all finite `2×2` computations, `fin_cases` + `ring_nf` style):
* `g1_mem_unitaryGroup`, `g2_mem_unitaryGroup`.
* `g1_det : g1.det = 1`, `g2_det : g2.det = 1`.
* `g1_trace : Matrix.trace g1 = 1 + (↑(Real.sqrt 2))⁻¹` (and same for g2).
  Note `(THTH)₀₀ = (1 + e^{iπ/4})/2`; the trace comes out real after the
  phase factor.
* `g1_g2_not_commute : g1 * g2 ≠ g2 * g1` (exhibit one differing entry;
  paper computes `(G₁G₂)₀₀ = (1−i)/2` vs `(G₂G₁)₀₀ = (1−i√2)/2`).
* Circuit realization **up to explicit phase**:
  `g1_circuit_eval : oneQubitHTCircuitMatrix [.t,.h,.t,.h] = Complex.exp (Complex.I * (Real.pi/4)) • g1`
  (and the `[.h,.t,.h,.t]` version for g2). Corollary:
  `GlobalPhaseEquivalent (oneQubitHTCircuitMatrix [.t,.h,.t,.h]) g1`.

This replaces the old `sigmaZPow/sigmaXPow/sigmaYPow/HPow` circuit tower and
the long `boykinB_circuit` word (4 letters instead of ~30).

### A2. `G1G2/SpectralForm.lean` — N&C Exercise 4.8, in `axisRotation` form

The paper's Hermitian `A` with `A² = I` is exactly our `pauliVec n` for a
unit `n` (`pauliVec_sq_eq_one`), and `e^{iαA}` is exactly `axisRotation n α`.
So formalize Ex. 4.8 as:

```lean
theorem su2_eq_axisRotation (U : Square 2)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ (n : EuclideanSpace ℝ (Fin 3)) (α : ℝ),
      ‖n‖ = 1 ∧ 0 ≤ α ∧ α ≤ Real.pi ∧ U = axisRotation n α
```

Proof route (entirely elementary, no spectral theorem):
1. `su2_form`: unitary + det 1 ⟹ `U = ![![a, b], ![-star b, star a]]`
   with `‖a‖² + ‖b‖² = 1` (entry computation from `U† * U = 1` and `det`).
2. Read off the `su2Pair` coordinates: `t = re a`,
   `x = (im b, re b, im a)`, so `U = su2Pair t x` with `t² + ‖x‖² = 1`
   (check against `pauliVec` conventions; four-entry verification).
3. `α := Real.arccos t`; then `sin α = √(1−t²) = ‖x‖`.
   If `‖x‖ ≠ 0`: `n := ‖x‖⁻¹ • x`; conclude via
   `axisRotation_closed_form` and `axisRotation_eq_su2Pair`.
   If `‖x‖ = 0`: `U = ±1`; take `n := standardZAxis`, `α ∈ {0, π}`.

### A3. `G1G2/AngleIdentification.lean` — pin the rotation angle by trace

* `trace_axisRotation : ‖n‖ = 1 → Matrix.trace (axisRotation n α) = 2 * Real.cos α`
  (from `axisRotation_closed_form`; `trace (pauliVec n) = 0`).
* Tiny bridging lemma: `(1/2) * (1 + 1/√2) = 1/2 + 1/(2√2)` so the paper's λ
  is literally `boykinLambda`; reuse `boykinLambda_cos_axis` giving
  `cos (λπ) = 1/2 + 1/(2√2)` and `0 ≤ λπ ≤ π`.
* Pinning: from A2 get `g1 = axisRotation n₁ α` with `α ∈ [0,π]`; from
  `g1_trace` and `trace_axisRotation`, `cos α = cos (λπ)`; injectivity of
  `cos` on `[0,π]` (`Real.injOn_cos` / `Real.strictAntiOn_cos`) gives
  `α = λπ`. Deliverables:

```lean
theorem g1_is_irrational_rotation :
    ∃ n₁, ‖n₁‖ = 1 ∧ g1 = axisRotation n₁ (boykinLambda * Real.pi)
-- same for g2
```

**This is the payoff of the lift:** it replaces the two giant entrywise
identification proofs (`boykinA_is_axisRotation`, `boykinB_is_axisRotation`
plus every `HPow_*_matrix` and sine-coordinate lemma) with a trace argument.
The axes stay abstract (`∃ n`) — no coordinates ever computed.

### A4. `G1G2/Nonparallel.lean` — axes from non-commutation

* `axisRotation_comm_of_parallel : n₂ = c • n₁ → Commute (axisRotation n₁ α) (axisRotation n₂ β)`
  (via `pauliVec_smul` and `axisRotation_add`; for unit vectors `c = ±1`).
* Contrapositive with `g1_g2_not_commute`: the axes from A3 satisfy
  `n₂ ≠ n₁ ∧ n₂ ≠ -n₁`, hence (Cauchy-Schwarz equality case,
  `abs_inner_lt_norm` variants) `|⟪n₁, n₂⟫_ℝ| < 1`.
  Deliverable: `g_axes_nonparallel : |⟪n₁, n₂⟫_ℝ| < 1`.
  (Caution: `sin(λπ) ≠ 0` is needed to divide out the scalar parts —
  available from `boykinLambda_sin_nonneg` + `cos(λπ) ≠ ±1`.)

### A5. `G1G2/EulerGeneral.lean` — corrected generalized Euler decomposition

The mathematically new core. For unit `n₁ n₂` with `k := ⟪n₁,n₂⟫`,
`|k| < 1`, `s := √(1−k²) > 0`:

* **Frame:** `e₁ := n₁`, `e₂ := s⁻¹ • (n₂ − k • n₁)`, `e₃ := cross e₁ e₂`.
  Orthonormality reuses `cross_orthogonal_unit_is_unit`,
  `euler_cross_orthogonal_*` from the Boykin file.
* **General product expansion** (generalizes
  `boykin_euler_product_expansion` by carrying `k`-terms): via `su2Pair_mul`
  twice, with `n₂ = k • e₁ + s • e₂`. Key scalar/e₁ identities to state:
  `scalar = cos b · cos(a+c) − k · sin b · sin(a+c)` and
  `⟪vector, e₁⟫ = cos b · sin(a+c) + k · sin b · cos(a+c)`,
  i.e. `scalar + i·⟪vector,e₁⟫ = e^{i(a+c)} · (cos b + i·k·sin b)`;
  transverse part has norm `s·|sin b|` with direction controlled by `a − c`.
* **Constrained inversion** (the corrected Ex. 4.11):

```lean
theorem euler_decomposition_of_reachable
    (hU : U = su2Pair t w) (ht : t^2 + ⟪w, n₁⟫_ℝ^2 ≥ k^2) :
    ∃ a b c, U = axisRotation n₁ a * axisRotation n₂ b * axisRotation n₁ c
```

  Inversion recipe (mirrors the three `Complex.arg` extractions in the
  existing `standardZ_axisRotation_boykin_euler`, so the proof pattern is
  proven technology):
  1. `ρ² := ‖w‖² − ⟪w,n₁⟫²`; from `t² + ⟪w,n₁⟫² + ρ² = 1` and the
     hypothesis, `ρ ≤ s`; choose `b` with `sin b = ρ/s` and
     `cos b = √(1 − ρ²/s²)` (so `|cos b + i k sin b|² = t² + ⟪w,n₁⟫²`).
  2. `u := Complex.arg ((t + i·⟪w,n₁⟫) / (cos b + i·k·sin b))`; set
     `a + c = u` (the divisor is nonzero: its norm² `≥ k² > 0` when `k ≠ 0`;
     if `k = 0` fall back to the existing orthogonal-axes theorem).
  3. Third `arg` extraction fixes `a − c` from the transverse direction of
     `w` in the `(e₂, e₃)` plane. Totality at zero vectors is fine —
     Mathlib's `arg 0 = 0` conventions worked for the existing proof.
* Exact equality (no global phase needed), matching the existing z-axis
  theorem.

### A6. `G1G2/RzApprox.lean` — splitting fix + density + assembly

1. **Reachability of small rotations**:
   `rz_small_reachable : cos (θ/2)^2 ≥ k^2 → (t² + w₁² ≥ k²)` for the target
   `rz θ = R(z, −θ/2)` (reuse `rz_eq_axisRotation_standardZ`; the target's
   `t = cos(θ/2)`).
2. **Splitting**: `rz_pow_split : rz θ = (rz (θ/N))^N` (diagonal matrix
   power, `Complex.exp_nat_mul`); choose `N := ⌈|θ|⌉ + 1` so
   `|θ/(2N)| ≤ 1/2 < arccos |k|` — discharge `cos²(1/2) > k²` numerically
   via interval bounds on `k² = (2√2−1)/(5−2√2)` (a closed algebraic number;
   `norm_num`-friendly after clearing denominators. NOTE: `k` is defined
   abstractly via A3's existential axes, so state this step against the
   *hypothesis* `|k| < cos(1/2)` and prove that hypothesis once from the
   trace data: `k = (cos²(λπ) − 1/2)/sin²(λπ)` — derive this identity from
   `Tr(g1*g2) = 1`, i.e. one more finite matrix computation
   `g1g2_trace : Matrix.trace (g1 * g2) = 1`, plus
   `trace_su2Pair_mul : Tr(PQ)/2 = t_P·t_Q − sin·sin·⟪n₁,n₂⟫`).
3. **Density** (reuse): instantiate `axisRotation_powers_dense` at
   `g1 = axisRotation n₁ (λπ)` with irrationality ratio `λ/2`
   (copy the 3-line ratio argument from `boykinA_powers_dense_axis₁`).
   Deliverables `g1_powers_dense`, `g2_powers_dense` — this is the paper's
   `d(G^a, G^m) < ε` lemma, with `G^a` kept as `axisRotation n (a·λπ)`
   rather than introducing the paper's representation-dependent real-power
   notation.
4. **Circuit powers** (reuse): `circuitPower`/`circuitInverse` on
   `[.t,.h,.t,.h]` and `[.h,.t,.h,.t]`. New phase bookkeeping:
   `eval (power circuit m) = e^{i·m·π/4} • g1^m`, so state the density
   conclusions against `hsDistance _ (eval C) < ε` using phase invariance
   (see C1) to erase the scalar.
5. **Assembly**:

```lean
theorem HT_rz_dense_g1g2 (θ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : HTCircuit, hsDistance (rz θ) (HTCircuit.eval C) < ε
```

   Proof: split into `N` factors (step 2); for each factor apply A5 to get a
   three-factor sandwich; approximate each of the `3N` factors to
   `ε/(3N)` (steps 3–4); combine with `hsDistance_circuitMatrix_le_sum` /
   iterated `hsDistance_mul_le` (both exist). Strictness: use
   `ε/(3N+1)`-style slack or strict-sum lemma as in the existing
   `clifford_rz_synthesis_approximates_by_clifford_t`.

### A7. Optional (nice-to-have, not blocking)

* Add the paper's simpler irrationality certificate as an alternative proof:
  `x = 1 + 1/√2` satisfies `2x² − 4x + 1 = 0`, non-monic + irreducible ⟹ not
  an algebraic integer. Keep `boykinLambda_irrational` as the default —
  it is finished and proves the identical statement.

---

## 3. Phase B — Exact synthesis without Lemma 11

Target statement (paper's Lemma `clifford-plus-rx-is-universal`, counts
dropped):

```lean
theorem clifford_rz_universal {n : ℕ} (hn : 1 ≤ n)
    (U : Square (2 ^ n)) (hU : U ∈ Matrix.unitaryGroup _ ℂ) :
    SynthesizesUpToGlobalPhase (CliffordRzGate n) U
```

### B1. New gate-set predicate (in `Universal/GateSets.lean`)

```lean
/-- Paper gate set {CX, H, S, S†, R_z}. S† kept explicitly (= SSS = T⁶). -/
def CliffordRzGate (n : ℕ) (U : Square (2 ^ n)) : Prop :=
  IsEmbeddedTwoQubitGate n cnot U ∨
  IsEmbeddedOneQubitGate n hadamard2 U ∨
  IsEmbeddedOneQubitGate n phaseS U ∨
  IsEmbeddedOneQubitGate n phaseSdagger U ∨
  (∃ θ, IsEmbeddedOneQubitGate n (rz θ) U)
```

Plus constructors, `mem_unitaryGroup`, and monotonicity
`CliffordRzGate n U → EasyGate n U` (so any old result can be recovered).

### B2. One-qubit base case (paper's N&C lemma)

The machinery behind `one_qubit_exact_h_t_rz` (`Statements.lean`) already
constructs `U ∼ rz α · ry β · rz γ` internally (see the `rz_add_two_pi`
manipulation at `Statements.lean:1040`). Extract/derive:

```lean
theorem one_qubit_zyz (U : Square 2) (hU : U ∈ unitaryGroup _ ℂ) :
    ∃ α β γ, GlobalPhaseEquivalent U (rz α * CosineSine.ry β * rz γ)
```

then substitute `ry β = phaseSdagger * hadamard2 * rz (−β) * hadamard2 * phaseS`
(compose the two existing bridge lemmas in `Statements.lean:71–125`) to get a
7-gate word over `{H, S, S†, R_z}`:

```lean
theorem one_qubit_clifford_rz_word (U : Square 2) (hU : _) :
    SynthesizesUpToGlobalPhase (CliffordRzGate 1) U
```

(embedding via `oneQubitPlacement1` — promote it from `private` in
`Universal/MainTheorem.lean:264`). The paper's literal `2H + 3Rz` shape
(absorbing `S = e^{iπ/4}·rz(π/2)` into neighboring `rz` gates) is optional
polish; any word over the set suffices for the qualitative theorem.

### B3. Retype the recursion interior from `EasyGate` to `CliffordRzGate`

Audit result — only three `EasyGate.of_embedded_two_qubit` sites exist in
`RecursiveDecomposition.lean` (lines 1265, 2166, 2219):

* **CX in Möttönen step** (`:2295`): the CX is already
  `IsEmbeddedTwoQubitGate _ cnot _`; membership becomes
  `CliffordRzGate.cnot`. Mechanical.
* **B3a — `swap2` in `synthesizes_liftMiddle`** (`:2219`): SWAP is not in
  the paper set. Add the standard 3-CNOT decomposition:
  `swap2_eq_three_cnots : swap2 = cnot * (localOnFirst H * localOnSecond H) * cnot * (localOnFirst H * localOnSecond H) * cnot`
  — i.e. `SWAP = CX·(H⊗H)·CX·(H⊗H)·CX` (reversed-control CNOT via H-conjugation;
  one `fin_cases` 4×4 check). Then `synthesizes_liftMiddle` produces
  `topTwoUnitary` images of cnot and H's, all `CliffordRzGate` members
  (`topTwoUnitary` distributes over `*` via `TwoQubitPlacement.embed_mul`).
* **Line 1265 / `two_qubit_unitary_is_easy_gate`**: eliminated by B4 (this
  was the n=2 base case).
* One-qubit memberships (`:2168–2174`, `:2291`, `:2322–2330`): H, S, S†, Rz —
  map 1:1 onto the new constructors.

Implementation choice: prove the `CliffordRzGate` versions as the primary
lemmas and recover the `EasyGate` versions by `CircuitOver.mono`, so
nothing downstream (incl. bounds files) breaks.

### B4. Restructure the strong induction (base `n = 1`)

Rewrite `lemma1_decomposition_to_easy_gate_set`'s induction as
`clifford_rz_universal` (statement above):

* **Base `n = 1`**: B2.
* **Step `n = m+1`, `m ≥ 1`**: exactly the existing body —
  `general_cosine_sine_step` (already valid for all `n ≥ 1`) →
  `synthesizes_first_qubit_block_diag` (already requires only `1 ≤ m`) →
  `synthesizes_controlled_ry_family` / `synthesizes_controlled_rz_family` —
  with the retyped memberships from B3. The `n = 2` case now flows through
  the general step with 1-qubit blocks instead of the special-cased
  `two_qubit_unitary_is_easy_gate`.
* **Phase plumbing**: interior lemmas are exact (`Synthesizes`), the base is
  up-to-phase. Add the small composition lemma
  `synthesizesUpToGlobalPhase_mul` (phases multiply; norm-1 closed under
  `*`) and the corresponding `map`/`lift` congruences — check
  `Universal/CliffordRz.lean` first, the Lemma-11 chain composes phases the
  same way and may already export these.

Pre-check to run first (cheap): confirm `general_cosine_sine_step` and
`general_demultiplexing_step` really elaborate at `m = 1` (grep shows the
hypotheses allow it; verify by instantiating in a scratch file before
committing to B4's structure).

### B5. Conversion `CliffordRzGate → CliffordTRzGate` (no Lemma 11)

Per-gate local rewrite, up to no phase at all:
`S = T·T` (`phaseT_sq_eq_phaseS`), `S† = T⁶` (`phaseT_six_eq_phaseSdagger`),
CX/H/Rz unchanged. Embedded versions come free from
`OneQubitPlacement.embed_mul` / `IsEmbeddedOneQubitGate` (each embedded S
becomes two embedded T's at the same placement). Deliverable:

```lean
theorem clifford_rz_to_clifford_t_rz {n : ℕ} {U : Square (2 ^ n)}
    (h : SynthesizesUpToGlobalPhase (CliffordRzGate n) U) :
    SynthesizesUpToGlobalPhase (CliffordTRzGate n) U
```

This is the drop-in replacement for `clifford_rz_synthesis_from_lemma1` —
after this, **`MainTheorem.lean`'s approximation pipeline applies unchanged**
(it consumes exactly `SynthesizesUpToGlobalPhase (CliffordTRzGate n) U`).

---

## 4. Phase C — Distance-layer alignment with the paper (small, mostly naming)

All in `Universal/Distance.lean`; extractions from existing proofs, no new
mathematics:

* **C1** `hsDistance_congr_globalPhase` (paper Lemma
  `hs-distance-and-global-phase`, two-sided): promote/generalize the private
  `hsDistance_eq_of_globalPhaseEquivalent_left` from
  `Universal/MainTheorem.lean:19`. Needed by A6 step 4 — do this first.
* **C2** `hsDistance_product_rearrange : d(U₁U₂, V₁V₂) = d(V₁†U₁, V₂U₂†)`
  (paper Lemma `distance-equality-for-products`) — extract the calc already
  inlined in `hsDistance_mul_le`.
* **C3** `hsDistance_to_identity`, `hsDistance_conjTranspose_symm`
  (paper Lemmas `distance-to-identity`, `distance-of-conjugated-unitaries`)
  — one-line corollaries of C2.
* **C4** Wang-Zhang in the paper's shape
  `d(U,V) ≤ d(U,I) + d(I,V)` as a named corollary of `trace_inequality`.
* **C5 (cosmetic, optional)** re-derive `hsDistance_mul_le` through C2–C4 to
  mirror the paper's proof text.

---

## 5. Phase D — Rewiring, compatibility, verification

* **D1** Re-point `lemma12_rz_approximation_by_ht`
  (`Lemma12/MainTheorem.lean`) at `HT_rz_dense_g1g2`. Statement unchanged.
  Downstream (`Universal/RzApproximation.lean`, `MainTheorem.lean`) compiles
  untouched.
* **D2** Rewire `clifford_t_is_universal` (`Universal/MainTheorem.lean`):
  * `n = 0` case unchanged.
  * `n ≥ 1`: single path `clifford_rz_universal` (B4) →
    `clifford_rz_to_clifford_t_rz` (B5) →
    existing `clifford_rz_synthesis_approximates_by_clifford_t`.
  * Delete the separate `n = 1` special case (subsumed). **Public statement
    stays byte-identical.**
  * Optional cosmetic: switch the error budget from `ε/(len+1)` over all
    gates to the paper's `ε/k` over Rz gates only, with a `k = 0` branch.
    Not required; note in a comment either way.
* **D3** Legacy quarantine (compile-only, no deletions): Lemma 11
  (`lemma11_two_qubit_synthesis`), `two_qubit_gate_has_clifford_rz_circuit`,
  `two_qubit_unitary_is_easy_gate`, and the Boykin identification lemmas stay
  where they are; add module docstrings marking them off the main path.
  Bounds files keep importing them — untouched by prior agreement.
* **D4** Verification gates:
  1. `lake build` green.
  2. `#print axioms clifford_t_is_universal` and
     `#print axioms lemma12_rz_approximation_by_ht` →
     `[propext, Classical.choice, Quot.sound]` only.
  3. Dependency audit (same `Expr.getUsedConstants` method as
     `HT_RZ_DENSE_PROOF_TREE.md`): confirm `lemma11_two_qubit_synthesis`,
     `boykinA_is_axisRotation`, `boykinB_is_axisRotation`, and
     `standardZ_axisRotation_boykin_euler` are **absent** from the
     transitive closure of `clifford_t_is_universal`.
* **D5** Documentation: update `HT_RZ_DENSE_PROOF_TREE.md`-style audit for
  the new G₁/G₂ track (can be regenerated at the end).
* **D6** Erratum note to the paper author: three-factor generalized Euler
  fails for the non-orthogonal G₁/G₂ axes (Section 0 above, with the
  numeric witness `R_z(π)`, best distance ≈ 0.254, and the angle-splitting
  repair). Draft only — sending is a separate decision.

---

## 6. Ordering, parallelism, risk

**Dependency order:**

```
C1 ─┐
A1 ─┼→ A3 → A4 ─┐
A2 ─┘            ├→ A5 → A6 → D1
                 │
B1 → B2 ─┐       │
B3  ─────┼→ B4 → B5 → D2 → D3/D4/D5
(B3a)  ──┘
```

Phase A and Phase B are fully independent — can proceed in parallel.
Phase C is tiny and unblocking (C1 before A6).

**Risk register:**

| Risk | Likelihood | Mitigation |
|---|---|---|
| A5 inversion algebra (non-orthogonal frame) harder than expected | medium | Proof pattern cloned from `standardZ_axisRotation_boykin_euler` (three `Complex.arg` extractions, already proven technology). Fallback: state A5 only for `R_z`-type targets (`w ∥ z`), which is all A6 needs. |
| `k² < cos²(1/2)` numeric discharge fiddly (nested radicals) | low | `k` satisfies the closed identity `k = (cos²(λπ) − ½)/sin²(λπ)` with `cos(λπ) = ½ + 1/(2√2)`; clear denominators to a polynomial inequality in `√2` and `nlinarith [Real.sq_sqrt]`. |
| `general_cosine_sine_step` breaks at `m = 1` despite permissive signature | low | Pre-check task in B4 before restructuring. |
| Retyping churn in the 2400-line `RecursiveDecomposition.lean` | medium | B3 strategy: new-predicate lemmas primary, old `EasyGate` versions recovered via `CircuitOver.mono` — old names never change, bounds files unaffected. |
| Phase bookkeeping for `eval = e^{imπ/4} • g1^m` leaks everywhere | low | Centralize: one lemma `hsDistance_eval_powerCircuit` stating the distance directly against `g1^m` via C1; downstream never sees the scalar. |

**Definition of done:** `lake build` green; D4 checks pass;
`clifford_t_is_universal`'s statement unchanged; its proof no longer depends
on Lemma 11, the arbitrary-2-qubit `EasyGate` branch, or any
coordinate-level Boykin axis lemma; Lemma 12 flows through the G₁/G₂ track
with the documented splitting fix.

---

## 7. File map (created / modified)

| File | Action |
|---|---|
| `Lemma12/G1G2/Generators.lean` | new (A1) |
| `Lemma12/G1G2/SpectralForm.lean` | new (A2) |
| `Lemma12/G1G2/AngleIdentification.lean` | new (A3) |
| `Lemma12/G1G2/Nonparallel.lean` | new (A4) |
| `Lemma12/G1G2/EulerGeneral.lean` | new (A5) |
| `Lemma12/G1G2/RzApprox.lean` | new (A6) |
| `Lemma12/MainTheorem.lean` | modify proof only (D1) |
| `Universal/GateSets.lean` | add `CliffordRzGate` + constructors (B1) |
| `Clifford/Statements.lean` | extract `one_qubit_zyz`; compose ry-bridge (B2) |
| `Universal/RecursiveDecomposition.lean` | B3/B3a/B4: retype + rebase induction at n=1 |
| `Universal/CliffordRz.lean` | add B5 conversion; Lemma-11 path marked legacy |
| `Universal/Distance.lean` | C1–C4 named lemmas |
| `Universal/MainTheorem.lean` | D2 rewiring; promote `oneQubitPlacement1` |
| `Lemma12/Boykin/BoykinDensity.lean` | untouched (shared infra imported by G1G2 track) |
| all `*Bounds*`, `Bounded.lean`, `LogPrecision.lean` | untouched |
| `docs/migration/clifford/` erratum note | new (D6) |

# Plan: Lift the Clifford+T Universality Proof to `universal_new_gates.tex` (July 2026)

Target reference: `reference/cliff/universal_new_gates.tex` (July 1, 2026).

Supersedes: `UPDATED_CLIFF_LIFT_PLAN.md`, which targeted
`reference/cliff/updated_cliff.tex` (June 2026). That plan's Section 0
documented an erratum in the June paper — the three-factor
`G₁^a G₂^b G₁^c` Euler step is false for the June gates
(`G₁ = e^{-iπ/4}THTH`, `G₂ = e^{-iπ/4}HTHT`), whose axes are non-orthogonal;
`R_z(π)` is an exact counterexample (see
`g1g2_euler_counterexample_math.tex`, `G1G2_HALF_ANGLE_REPAIR_PROOF.md`).
The July paper **resolves the erratum by changing the gates**, which removes
the entire splitting/half-angle repair from the critical path and makes the
paper's Lemma-12 proof structurally identical to the already-formalized
Boykin track. This plan is the corresponding rework.

**Non-goals (unchanged):** all gate-count work
(`14·4^{n-1} − 9·2^{n-1}`, Lemma `rzcount`), and all `*Bounds.lean` /
`Bounded.lean` / `LogPrecision.lean` files. They stay untouched and must keep
compiling; nothing here may rename or delete a declaration they use.

> **Status update (2026-07-10, execution).** The additive-only constraint on
> the Boykin file was lifted by the user ("we do not care about the old
> proof — remove whatever isn't needed; stay lean, match the paper
> lemma-by-lemma"). **Phase A is complete and merged into the build:**
> the generic infrastructure was extracted from `Boykin/BoykinDensity.lean`
> into `G1G2/AxisRotation.lean` (Euler theorem generalized to arbitrary
> orthogonal axes, phased-rotation density added), the concrete track lives
> in `G1G2/{Generators,SpectralForm,AngleIdentification,Orthogonality,
> RzApprox}.lean`, `lemma12_rz_approximation_by_ht` is re-pointed (statement
> unchanged), and the entire Boykin layer plus `HalfAngleRepair.lean` were
> **deleted** (not quarantined). `lake build` green;
> `#print axioms` for `lemma12_rz_approximation_by_ht` and
> `clifford_t_is_universal`: `[propext, Classical.choice, Quot.sound]`.
>
> **Phases B, C, D are also complete** (same session): `CliffordRzGate`
> predicate (B1); one-qubit base case `one_qubit_exact_clifford_rz` (B2);
> retyped recursion with `SWAP = CX·(H⊗H)·CX·(H⊗H)·CX` and global-phase
> plumbing, culminating in `clifford_rz_universal` with base `n = 1`
> (B3/B3a/B4, appended to `RecursiveDecomposition.lean`);
> `clifford_rz_to_clifford_t_rz` via `S = T²`, `S† = T⁶` (B5, in
> `CliffordRz.lean`); paper distance Lemmas 9–12 as named lemmas (C);
> `clifford_t_is_universal` rewired through the single paper path for all
> `n ≥ 1`, legacy `n = 1` / `n ≥ 2` branches deleted (D2).  Dependency audit
> (D4): Lemma 11, `two_qubit_unitary_is_easy_gate`,
> `lemma1_decomposition_to_easy_gate_set`, and the whole Boykin track are
> absent from the main theorem's closure.  The EasyGate/Lemma-11 layer itself
> remains compiling for the `*Bounds*` files (non-goal scope).
> See `NEW_GATES_LEMMA_MAP.md` for the paper-lemma ↔ Lean-declaration table.

---

## 0. What the July paper changed, and what it kills in the old plan

New gates (paper section [We show how to approximate R_z gates]):

```
G₁ = e^{-3iπ/8} · THTHT            (was  e^{-iπ/4} · THTH)
G₂ = (HT⁴) · G₁ · (HT⁴)†           (was  e^{-iπ/4} · HTHT)
```

with `Tr(G₁) = Tr(G₂) = √(1 + 1/√2)` (was `1 + 1/√2`), and the load-bearing
new lemma `a1-and-a2-anticommute`: **`A₁A₂ = −A₂A₁`**, i.e. the two rotation
axes are *orthogonal*. For orthogonal axes the three-factor Euler
decomposition is globally valid, so the June counterexample no longer
applies. The irrationality certificate also changed: the new
`λ = (1/π)·arccos(½·√(1+1/√2))`, shown irrational via
`x = 2cos(λπ) ⟹ x²−1 = 1/√2`, which is not an algebraic integer
(minimal polynomial `2X²−1` is not monic). Negative powers use
`G₁⁻¹ ∼ T⁷HT⁷HT⁷` (exact, since `T† = T⁷`).

**Numerically verified 2026-07-10** (all claims of the July paper check out,
unlike the June version): `G₁, G₂` unitary with det exactly 1; both traces
`= √(1+1/√2) ≈ 1.30656`; both rotation angles equal with
`cos α = ½√(1+1/√2)`; axes exactly orthogonal (`⟪n₁,n₂⟫ = 0`,
`A₁A₂ = −A₂A₁` to machine precision); `Tr(G₁G₂) = 1/2 + √2/4`;
`G₁G₂ ≠ G₂G₁`; `(THTHT)† = T⁷HT⁷HT⁷` exactly.

Consequences for the old plan:

| Old-plan item | Fate |
|---|---|
| §0 erratum + angle-splitting fix (`rz θ = (rz(θ/N))^N`, `N = ⌈|θ|⌉+1`) | **Deleted.** No splitting anywhere. |
| A5 `EulerGeneral.lean` — corrected non-orthogonal Ex. 4.11 with reachability constraint `t² + ⟪w,n₁⟫² ≥ k²` (the "mathematically new core", medium risk) | **Deleted.** Replaced by a mechanical generalization of the existing orthogonal-axes Euler proof (new A5, low risk). |
| A6 steps 1–2 (small-rotation reachability, `rz_pow_split`, numeric `k² < cos²(1/2)` discharge) | **Deleted.** |
| A4 `Nonparallel.lean` (`|k| < 1` from non-commutation) | **Replaced** by orthogonality `k = 0` from two trace computations (new A4) — stronger and simpler. |
| Reuse of `boykinLambda` / `boykinLambda_irrational` "verbatim" | **Invalid.** The July λ is a *different real number* (`cos(λπ) = ½√(1+1/√2)`, vs Boykin's `½(1+1/√2)`). New irrationality lemma needed (new A3); the *machinery* (root-of-unity ⟹ algebraic integer, `¬IsIntegral` pattern) is reusable. |
| `TwoControl/Clifford/Lemma12/G1G2/HalfAngleRepair.lean` (uncommitted) | **Off the critical path.** Its constants are the June-paper axes. Keep as an archival record of the erratum with a "historical — superseded by universal_new_gates.tex" docstring, or delete. Recommendation: keep (it is self-contained and documents why the July paper exists), but do not import it from the main chain. |
| D6 erratum note to the author | **Resolved.** The July 1 paper is the author-side fix. Commit the counterexample docs (`g1g2_euler_counterexample_math.tex`, `..._email_body.txt`, `G1G2_HALF_ANGLE_REPAIR_PROOF.md`) as the historical record, each with a one-line "resolved by universal_new_gates.tex (July 1, 2026)" header. |

Everything in Phases B (exact synthesis), C (distance layer), and D
(rewiring) of the old plan is **unaffected** by the gate change — the July
paper is byte-identical to the June paper outside the Lemma-12 subsection.
Those phases are carried over below (condensed, with unchanged content
marked) so this document is self-contained.

---

## 1. Ground-truth inventory (delta view)

Sorry-free components, updated reuse verdicts:

| Component | Location | Verdict for this lift |
|---|---|---|
| `hsDistance`, Lemmas 7–13 layer (`hsDistance_self`, phase lemmas, `trace_inequality`, `hsDistance_mul_le`, `hsDistance_circuitMatrix_le_sum`) | `Universal/Distance.lean` | Reuse verbatim (as before). |
| `axisRotation`, `axisRotation_closed_form`, `pauliVec_sq_eq_one`, `exp_of_sq_eq_one`, `axisRotation_mem_unitaryGroup` | `Boykin/BoykinDensity.lean` | Reuse (public). |
| `su2Pair`, `su2Pair_mul`, `axisRotation_eq_su2Pair`, `cross` algebra | `BoykinDensity.lean` | Reuse (public). |
| `boykin_euler_product_expansion` — **already stated for arbitrary orthogonal unit axes** `n₁ n₂`, `⟪n₁,n₂⟫ = 0` | `BoykinDensity.lean:2021` | **Reuse as-is.** The July paper's orthogonality is exactly its hypothesis. |
| `standardZ_axisRotation_boykin_euler` (z-rotation = 3-factor product over the two Boykin axes) | `BoykinDensity.lean:2230` | Proof is **coordinate-free** (orthonormal frame + 3 `Complex.arg` extractions; uses only unit norms + orthogonality). Generalize by hypothesis-abstraction (new A5). |
| `axisRotation_powers_dense` (any unit axis, any `U = axisRotation n θ`, `Irrational (θ/2π)`) | `BoykinDensity.lean:1593`, `private` | Reuse — needs `private` flip (A0). |
| `zpowMatrix`, `circuitPower`, `circuitInverse`, `primitiveInvCircuit` + eval lemmas | `BoykinDensity.lean:1421–1490` | Reuse (`zpowMatrix` public; eval helpers private — flip as needed). |
| `hsDistance_triple_mul_le` | `BoykinDensity.lean:2125` | Reuse (public). |
| `rational_angle_is_rootOfUnity`, `exp_I_trace`, `not_isIntegral_seven_div_four_complex` (proof pattern), `boykinZeta`/`boykinPolynomial` scaffolding | `BoykinDensity.lean:1050–1210` | Reuse the *pattern*; `rational_angle_is_rootOfUnity` needs `private` flip. `boykinLambda_irrational` itself: **not reusable** (different λ). |
| `standardZAxis`, `standardZAxis_unit`, `rz_eq_axisRotation_standardZ` | `BoykinDensity.lean:1654–1665`, `private` | Reuse — flip `private` (A0). |
| Boykin identification lemmas (`boykinA_is_axisRotation`, `boykinB_is_axisRotation`, σ-power towers, `HPow_*`) | `BoykinDensity.lean` | **Not used** by the new track (that's the payoff: trace-based identification instead of coordinates). Stay compiling, D3 quarantine. |
| Gate sets, CS/demultiplexing/Möttönen recursion, ry↔rz bridge, one-qubit ZYZ internals, `phaseT_sq_eq_phaseS`, `phaseT_six_eq_phaseSdagger`, Lemma 11 chain | as in old plan §1 | Verdicts unchanged (Phase B below). |
| Public wrappers `lemma12_rz_approximation_by_ht`, `clifford_t_is_universal` | `Lemma12/MainTheorem.lean`, `Universal/MainTheorem.lean` | Statements frozen; proofs re-pointed (D1, D2). |

Build wiring note: the `TwoControl` lib builds only what
`TwoControl.lean` transitively imports. New `G1G2/*` files must be imported
from `Lemma12/MainTheorem.lean` (D1) to be built; the archival
`HalfAngleRepair.lean` should *not* be (leave it unimported, or hang it off a
docs-only import if we want CI to keep checking it).

---

## 2. Phase A0 — Shared infrastructure exposure (tiny, do first)

Flip `private` → public in `BoykinDensity.lean` (additive-only change, no
renames) for exactly what the new track imports:

* `axisRotation_powers_dense` (:1593)
* `zpowMatrix_axisRotation` (:1529)
* `standardZAxis` (:1654), `standardZAxis_unit` (:1657),
  `rz_eq_axisRotation_standardZ` (:1665)
* `rational_angle_is_rootOfUnity` (:1052)
* cross-product helpers used by the generalized Euler statement if it lives
  outside the file (`cross_orthogonal_left/right` :2080–2086,
  `cross_orthogonal_unit_is_unit` :2092) — **not needed if A5 is added inside
  `BoykinDensity.lean`** (recommended, see A5).

Everything else the new track consumes is already public.

---

## 3. Phase A — Lemma 12 via the July G₁/G₂ (the reworked core)

New directory `TwoControl/Clifford/Lemma12/G1G2/` (already exists, currently
holding only the archival `HalfAngleRepair.lean`). The Boykin track stays
untouched and compiling until D1 flips the wrapper.

### A1. `G1G2/Generators.lean` — concrete gates and circuits

```lean
/-- Conjugator C = H·T⁴ (note T⁴ = diag(1,−1) = Z). -/
noncomputable def gConj : Square 2 := hadamard2 * phaseT ^ 4

noncomputable def g1 : Square 2 :=
  Complex.exp (-(Complex.I * (3 * Real.pi / 8))) •
    (phaseT * hadamard2 * phaseT * hadamard2 * phaseT)

noncomputable def g2 : Square 2 := gConj * g1 * gConj⁻¹   -- or * star gConj
```

Deliverables:

* `g1_mem_unitaryGroup` (product of unitaries, scalar has norm 1);
  `g2_mem_unitaryGroup` free by conjugation.
* `g1_det = 1`: `det(THTHT) = e^{3iπ/4}·(det H)² = e^{3iπ/4}` and
  `(e^{-3iπ/8})² = e^{-3iπ/4}` (`Complex.exp` arithmetic, no matrices).
  `g2_det = 1` free by conjugation.
* **Squared trace** (see A3 for why the square suffices):
  `g1_trace_sq : (Matrix.trace g1)^2 = 1 + (↑(Real.sqrt 2))⁻¹`.
  Key trick: `(trace g1)² = e^{-3iπ/4} · (trace (THTHT))²`, and
  `e^{-3iπ/4} = -(√2/2) - (√2/2)i` (standard `Complex.exp` evaluation at
  3π/4 — cos/sin of 3π/4 are in Mathlib). Both factors live in `ℚ(i,√2)`,
  so the whole computation is `fin_cases`/`ring_nf`/`norm_num` over matrix
  entries — **no π/8 trigonometry anywhere**. (For the record:
  `trace(THTHT) = −1/(e^{iπ/4}−1)`, `(trace g1)` real `= 1/√(2−√2)`.)
  `g2_trace_sq` free: `trace(C·g1·C⁻¹) = trace g1` by `trace_mul_cycle` +
  unitarity of `gConj`.
* Product traces for A4 (both finite `ℚ(i,√2)` computations; the scalar
  contributes `(e^{-3iπ/8})² = e^{-3iπ/4}` again):
  `g1_g2_trace : Matrix.trace (g1 * g2) = 1/2 + (Real.sqrt 2)/4` and
  `g1_g2dag_trace : Matrix.trace (g1 * g2ᴴ) = 1/2 + (Real.sqrt 2)/4`.
* Circuit realization **up to explicit phase**:

```lean
def g1Word : HTCircuit := [.t, .h, .t, .h, .t]
def g2Word : HTCircuit := [.h, .t, .t, .t, .t] ++ g1Word ++ [.t, .t, .t, .t, .h]

theorem g1Word_eval :
    HTCircuit.eval g1Word = Complex.exp (Complex.I * (3 * Real.pi / 8)) • g1
theorem g2Word_eval :
    HTCircuit.eval g2Word = Complex.exp (Complex.I * (3 * Real.pi / 8)) • g2
```

  (For `g2Word`: `(HT⁴)† = T⁴H` exactly, since `T⁸ = 1`; the conjugators are
  phase-free, so the same `e^{3iπ/8}` factor passes through.) Negative
  powers need no new words: the existing `circuitInverse` +
  `primitiveInvCircuit` machinery produces the paper's `T⁷HT⁷HT⁷` shape
  automatically.

This keeps the old plan's payoff (5- and 14-letter words instead of the
σ-power towers and ~30-letter Boykin words), and drops
`g1_g2_not_commute` from the critical path entirely (orthogonality does its
job; see A4). Optional paper-fidelity extras live in A7.

### A2. `G1G2/SpectralForm.lean` — N&C Exercise 4.8 (unchanged from old plan)

```lean
theorem su2_eq_axisRotation (U : Square 2)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ (n : EuclideanSpace ℝ (Fin 3)) (α : ℝ),
      ‖n‖ = 1 ∧ 0 ≤ α ∧ α ≤ Real.pi ∧ U = axisRotation n α
```

Proof route exactly as in the old plan (elementary, no spectral theorem):
`su2_form` entry computation → read off `su2Pair` coordinates →
`α := Real.arccos t`, normalize the vector part (degenerate `‖x‖ = 0` case:
`U = ±1`, take `standardZAxis`, `α ∈ {0, π}`); conclude via
`axisRotation_closed_form` / `axisRotation_eq_su2Pair`.

### A3. `G1G2/AngleIdentification.lean` — pin the angle by *squared* trace

The July λ:

```lean
noncomputable def gLambda : ℝ :=
  Real.arccos ((1 / 2) * Real.sqrt (1 + 1 / Real.sqrt 2)) / Real.pi
```

**Design decision (new vs old plan): work with squares throughout.** From A2
we get `gᵢ = axisRotation nᵢ αᵢ` with `αᵢ ∈ [0,π]`; the trace gives
`2cos αᵢ`, but pinning the *sign* of `Tr(g1)` would drag in `cos(3π/8)`
half-angle values. Nothing downstream needs the sign:

* `trace_axisRotation : ‖n‖ = 1 → Matrix.trace (axisRotation n α) = 2 * Real.cos α`
  (from `axisRotation_closed_form`; `pauliVec` is traceless). Plus the tiny
  `trace_su2Pair : Matrix.trace (su2Pair t w) = 2 * t` for A4.
* Squared pinning: from `g1_trace_sq` and `trace_axisRotation`,
  `4 * Real.cos α₁ ^ 2 = 1 + 1/√2` — deliverable
  `g1_cos_sq : Real.cos α₁ ^ 2 = (1 + 1/Real.sqrt 2) / 4` (same for g2).
* Strict interior: `cos² αᵢ < 1` (numeric: `(1+1/√2)/4 < 1`), so
  `αᵢ ∈ (0, π)` and `sin αᵢ > 0` — needed by A4 and harmless to prove here.
* **Irrationality in squared-cosine form** (replaces any reuse of
  `boykinLambda_irrational`):

```lean
theorem irrational_angle_of_cos_sq (μ : ℝ)
    (h : (2 * Real.cos (μ * Real.pi)) ^ 2 = 1 + 1 / Real.sqrt 2) :
    Irrational μ
```

  Proof = the July paper's argument, sign-free because only `x²` occurs:
  if `μ = p/q` rational, `ζ := e^{iμπ}` is a root of unity
  (reuse `rational_angle_is_rootOfUnity`), hence `IsIntegral ℤ ζ` and
  `IsIntegral ℤ ζ⁻¹`; `x := ζ + ζ⁻¹ = 2cos(μπ)` is integral (closure under
  `+`); `w := x² − 1 = 1/√2` is integral (closure under `*`, `-`);
  `w² = 1/2` is integral; but `¬ IsIntegral ℤ (1/2 : ℂ)` — clone
  `not_isIntegral_seven_div_four_complex` with `1/2` (same rational-root
  argument). Contradiction. This is *simpler* than the Boykin
  `boykinPolynomial` route (no quartic, no trace-polynomial expansion).
* Corollary used by A6:
  `g_angle_irrational : Irrational (αᵢ / Real.pi)` for both axes, hence
  `Irrational (αᵢ / (2 * Real.pi))` by the `div_ratCast` step copied from
  `boykinA_powers_dense_axis₁`. (`gLambda` itself is then only cosmetic; we
  never need `αᵢ = gLambda·π`, avoiding the sign case-split `αᵢ ∈ {λπ, (1−λ)π}`
  entirely.)

**Payoff unchanged from the old plan, now bigger:** no coordinate-level
identification (`boykinA_is_axisRotation`-style) *and* no half-angle
trigonometry — every matrix computation stays in `ℚ(i,√2)`.

### A4. `G1G2/Orthogonality.lean` — axes orthogonal from two product traces

Replaces old A4 (`Nonparallel.lean`). Let `k := ⟪n₁, n₂⟫_ℝ`.

* Product-trace formulas, from `axisRotation_eq_su2Pair` + `su2Pair_mul` +
  `trace_su2Pair`:
  `Tr(R(n₁,α)·R(n₂,β)) = 2(cos α cos β − sin α sin β · k)` and, via
  `axisRotation_inv` (i.e. `R(n₂,β)ᴴ = R(n₂,−β)`),
  `Tr(R(n₁,α)·R(n₂,β)ᴴ) = 2(cos α cos β + sin α sin β · k)`.
* Subtract: `Tr(g1·g2ᴴ) − Tr(g1·g2) = 4 sin α₁ sin α₂ · k`. By
  `g1_g2_trace` and `g1_g2dag_trace` (A1) the left side is `0`; by A3,
  `sin αᵢ > 0`. Hence:

```lean
theorem g_axes_orthogonal : inner ℝ n₁ n₂ = (0 : ℝ)
```

  No sign of `cos αᵢ` is needed (the difference identity cancels the
  `cos·cos` term), and no case analysis — this is why A1 computes *both*
  product traces.

This formalizes the paper's `A₁A₂ = −A₂A₁` in `axisRotation` language
(anticommuting `pauliVec`s ⟺ orthogonal axes), which is the form
`boykin_euler_product_expansion` already consumes.

### A5. Generalized orthogonal Euler decomposition (was the risky core; now mechanical)

Add to the bottom of `BoykinDensity.lean` (recommended — all `private` cross/
frame helpers are in scope there, so A0 stays minimal):

```lean
theorem axisRotation_orthogonal_euler
    (n₁ n₂ : EuclideanSpace ℝ (Fin 3))
    (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1) (hortho : inner ℝ n₁ n₂ = 0)
    (m : EuclideanSpace ℝ (Fin 3)) (hm : ‖m‖ = 1) (φ : ℝ) :
    ∃ a b c : ℝ,
      axisRotation m φ =
        axisRotation n₁ a * axisRotation n₂ b * axisRotation n₁ c
```

This is `standardZ_axisRotation_boykin_euler` (:2230) with
`boykinAxis₁/₂ → n₁/n₂` and `standardZAxis → m`: inspection confirms its
~175-line proof is already coordinate-free — it builds the orthonormal frame
`(n₁, n₂, cross n₁ n₂)`, decomposes the target axis by inner products
`c₁, c₂, c₃`, and does three `Complex.arg` extractions; it never evaluates a
coordinate of either axis. Re-derive the old Boykin-specific statement as a
one-line corollary (old name kept for compatibility).

There is **no reachability side-condition and no corrected Ex. 4.11**: with
`k = 0` the June obstruction (`t² + ⟪w,n₁⟫² ≥ k²`) is vacuous. The entire
old A5 (`EulerGeneral.lean`, non-orthogonal frames, constrained inversion)
is gone.

### A6. `G1G2/RzApprox.lean` — density + assembly (no splitting)

Mirror the last ~250 lines of the Boykin track
(`boykinA_powers_dense_axis₁` → `boykin_HT_approx_euler_product` →
`HT_Rz_dense`), with the phase absorbed once:

1. **Phase-absorbing density.** `g1Word` evaluates to `e^{3iπ/8}•g1`, so
   power circuits evaluate to `zpowMatrix (e^{3iπ/8}•g1) m
   = e^{3imπ/8} • zpowMatrix g1 m`. Centralize the bookkeeping in one lemma
   (uses C1 and `zpowMatrix` smul-compatibility):

```lean
theorem hsDistance_zpowMatrix_smul (φ : ℝ) (A U : Square 2) (k : ℤ) ... :
    hsDistance A (zpowMatrix (Complex.exp (Complex.I * φ) • U) k)
      = hsDistance A (zpowMatrix U k)
```

   Downstream never sees the scalar (old plan's risk-register mitigation,
   now a named deliverable).
2. **Density wrappers** (clone the 3-line Boykin wrappers):
   `g1_powers_dense : ∀ α, 0 < ε → ∃ k : ℤ, hsDistance (axisRotation n₁ α) (HTCircuit.eval (g1PowerCircuit k)) < ε`
   via `axisRotation_powers_dense` (A0) at `θ := α₁`, irrationality from A3,
   identification `g1 = axisRotation n₁ α₁` from A2/A3, phase erased by
   step 1. Same for `g2`. (`g1PowerCircuit := circuitPower g1Word ·` /
   `circuitInverse` for negatives, exactly like `boykinA_power_circuit`.)
3. **Assembly:**

```lean
theorem HT_rz_dense_g1g2 (θ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : HTCircuit, hsDistance (rz θ) (HTCircuit.eval C) < ε
```

   Proof shape identical to `HT_Rz_dense`:
   `rz θ = axisRotation standardZAxis (−θ/2)`
   (`rz_eq_axisRotation_standardZ`, A0) → A5 with
   `(n₁, n₂, m := standardZAxis)` gives the exact three-factor form → three
   `ε/3` approximations from step 2 → `hsDistance_triple_mul_le`.
   Three factors, not six, not `3N` — the June-era splitting and the
   half-angle repair are both dead.

### A7. Optional paper-fidelity extras (not blocking, separate file if done)

* Signed trace `Matrix.trace g1 = ↑(Real.sqrt (1 + 1/Real.sqrt 2))` — needs
  `Real.cos_pi_div_eight`-family values; only cosmetic given A3's square
  route.
* `g1_g2_not_commute` (paper's Lemma `properties-of-g1-g2` third clause) —
  derivable abstractly from `k = 0`, `sin αᵢ ≠ 0`, or by one matrix entry.
* `gLambda` identification `α₁ = gLambda * Real.pi ∨ α₁ = (1 − gLambda) * Real.pi`.
* The paper's monic-polynomial phrasing of irrationality (we use the
  equivalent `¬IsIntegral ℤ (1/2)` form).

---

## 4. Phase B — Exact synthesis without Lemma 11 (unchanged from old plan)

Carried over verbatim from `UPDATED_CLIFF_LIFT_PLAN.md` §3 — the July paper
did not touch this half. Summary of deliverables (full details in the old
plan, which remains authoritative for this phase):

* **B1** `CliffordRzGate` predicate `{CX, H, S, S†, R_z}` in
  `Universal/GateSets.lean` + constructors + monotonicity into `EasyGate`.
* **B2** One-qubit base case: extract `one_qubit_zyz` from
  `Statements.lean:1046` internals; compose with the ry↔rz bridge
  (`Statements.lean:71–125`) → `one_qubit_clifford_rz_word`
  (promote `oneQubitPlacement1` from `private`,
  `Universal/MainTheorem.lean:264`).
* **B3** Retype recursion interior `EasyGate → CliffordRzGate`; the three
  `of_embedded_two_qubit` sites (`RecursiveDecomposition.lean:1265, 2166,
  2219`); **B3a** SWAP = `CX·(H⊗H)·CX·(H⊗H)·CX` for
  `synthesizes_liftMiddle`. New-predicate lemmas primary, `EasyGate`
  versions recovered via `CircuitOver.mono` so bounds files never notice.
* **B4** Rebase the strong induction at `n = 1`
  (`clifford_rz_universal`); pre-check `general_cosine_sine_step` /
  `general_demultiplexing_step` at `m = 1` in a scratch file first;
  add `synthesizesUpToGlobalPhase_mul` phase plumbing.
* **B5** `clifford_rz_to_clifford_t_rz` via `S = T²`, `S† = T⁶`
  (`phaseT_sq_eq_phaseS`, `phaseT_six_eq_phaseSdagger`) — drop-in
  replacement for `clifford_rz_synthesis_from_lemma1`.

## 5. Phase C — Distance-layer alignment (unchanged from old plan)

All in `Universal/Distance.lean`, extractions only: **C1**
`hsDistance_congr_globalPhase` (promote the private lemma at
`Universal/MainTheorem.lean:19`; needed by A6 step 1 — **do first**);
**C2** `hsDistance_product_rearrange`; **C3** `hsDistance_to_identity`,
`hsDistance_conjTranspose_symm`; **C4** Wang–Zhang in the paper's
`d(U,V) ≤ d(U,I) + d(I,V)` shape; **C5** optional re-derivation of
`hsDistance_mul_le` through C2–C4.

## 6. Phase D — Rewiring, compatibility, verification

* **D1** Re-point `lemma12_rz_approximation_by_ht`
  (`Lemma12/MainTheorem.lean`) at `HT_rz_dense_g1g2`; add the
  `G1G2/*` imports there (this is what puts the new files into the build).
  Statement unchanged; update the module docstring (it currently narrates
  the Boykin route).
* **D2** Rewire `clifford_t_is_universal` exactly as in the old plan
  (single path B4 → B5 → existing
  `clifford_rz_synthesis_approximates_by_clifford_t`; `n = 0` case and
  public statement untouched).
* **D3** Legacy quarantine (unchanged): Lemma 11 chain, `two_qubit_*`
  EasyGate lemmas, and now also the **Boykin identification layer**
  (`boykinA/B_is_axisRotation`, σ-power towers, `HPow_*`,
  `boykinLambda_irrational`, `boykin_zeta_*`) — all stay compiling, module
  docstrings mark them off the main path. Plus the June-erratum archive:
  `HalfAngleRepair.lean` docstring updated to "historical", counterexample
  docs committed with resolution headers.
* **D4** Verification gates:
  1. `lake build` green.
  2. `#print axioms clifford_t_is_universal` and
     `#print axioms lemma12_rz_approximation_by_ht` →
     `[propext, Classical.choice, Quot.sound]` only.
  3. Dependency audit (`Expr.getUsedConstants`, as in
     `HT_RZ_DENSE_PROOF_TREE.md`): the transitive closure of
     `clifford_t_is_universal` must not contain
     `lemma11_two_qubit_synthesis`, `boykinA_is_axisRotation`,
     `boykinB_is_axisRotation`, `standardZ_axisRotation_boykin_euler`
     (the *specialized* one), `boykinLambda_irrational`, or anything from
     `HalfAngleRepair.lean`.
* **D5** Regenerate the proof-tree audit doc for the G₁/G₂ track.
* **D6** (was: draft erratum) Now: commit the erratum record as history;
  optional short follow-up note to the author confirming the July gates
  verify cleanly (numeric check of 2026-07-10) — separate decision, not a
  blocker.

---

## 7. Ordering, parallelism, risk

```
A0 ──┬→ A5 (in BoykinDensity, additive) ──┐
C1 ──┤                                    │
A1 ──┼→ A3 → A4 ──────────────────────────┼→ A6 → D1
A2 ──┘                                    │
                                          │
B1 → B2 ─┐                                │
B3/B3a ──┼→ B4 → B5 → D2 ─────────────────┴→ D3/D4/D5/D6
```

Phase A and Phase B remain fully independent (parallelizable). A5 no longer
depends on A3/A4 (it is axis-generic), so it can start immediately after A0.

Risk register (rework):

| Risk | Likelihood | Mitigation |
|---|---|---|
| ~~A5 non-orthogonal inversion algebra~~ | — | **Eliminated** (orthogonal axes; existing proof generalizes by hypothesis-abstraction). |
| ~~Numeric `k² < cos²(1/2)` discharge~~ | — | **Eliminated** (no splitting). |
| A1 trace computations (`(trace g1)²`, `Tr(g1g2)`, `Tr(g1g2ᴴ)`) fiddly | low–medium | All in `ℚ(i,√2)` by the squared-phase trick; 2×2 `fin_cases` + `ring_nf` + the existing `exp_I_pi_div_four`-family helpers. Verify the target values numerically first (done 2026-07-10). |
| A3 irrationality clone runs into `IsIntegral` API friction | low | Pattern already exists in-file (`not_isIntegral_seven_div_four_complex`, `rational_angle_is_rootOfUnity`); the new instance (`1/2`) is strictly simpler than the old (`7/4` + quartic). |
| Sign of `cos αᵢ` leaks into a proof obligation | low | Square-only discipline: A3 pins `cos²`, A4 uses the trace *difference* (cancels `cos·cos`), A6 needs only irrationality of `αᵢ/π`. Nothing consumes the sign. |
| A2 `su2_form` entry bookkeeping | low | Elementary; unchanged from old plan. |
| B-phase risks | unchanged | As in old plan (retyping churn mitigated by `CircuitOver.mono`; `m = 1` pre-check). |

**Definition of done:** `lake build` green; D4 checks pass; public
statements of `clifford_t_is_universal` and
`lemma12_rz_approximation_by_ht` byte-identical; the main proof path uses
the July-paper G₁/G₂ track (trace-identified abstract axes, orthogonal
Euler, three-factor approximation) and no longer depends on Lemma 11, the
arbitrary-2-qubit `EasyGate` branch, any coordinate-level Boykin axis
lemma, or any splitting/half-angle machinery.

---

## 8. File map (created / modified)

| File | Action |
|---|---|
| `Lemma12/G1G2/Generators.lean` | new (A1) |
| `Lemma12/G1G2/SpectralForm.lean` | new (A2) |
| `Lemma12/G1G2/AngleIdentification.lean` | new (A3) |
| `Lemma12/G1G2/Orthogonality.lean` | new (A4; replaces planned `Nonparallel.lean`) |
| ~~`Lemma12/G1G2/EulerGeneral.lean`~~ | **dropped** — A5 lives in `BoykinDensity.lean` |
| `Lemma12/G1G2/RzApprox.lean` | new (A6) |
| `Lemma12/G1G2/HalfAngleRepair.lean` | keep, archival docstring (D3); not imported by the main chain |
| `Lemma12/Boykin/BoykinDensity.lean` | additive only: A0 `private` flips + A5 general Euler theorem |
| `Lemma12/MainTheorem.lean` | D1: imports + proof re-point + docstring |
| `Universal/GateSets.lean` | B1 |
| `Clifford/Statements.lean` | B2 |
| `Universal/RecursiveDecomposition.lean` | B3/B3a/B4 |
| `Universal/CliffordRz.lean` | B5; Lemma-11 path marked legacy |
| `Universal/Distance.lean` | C1–C4 |
| `Universal/MainTheorem.lean` | D2; promote `oneQubitPlacement1`, `hsDistance_congr_globalPhase` |
| all `*Bounds*`, `Bounded.lean`, `LogPrecision.lean` | untouched |
| `docs/migration/clifford/g1g2_euler_counterexample_*`, `G1G2_HALF_ANGLE_REPAIR_PROOF.md` | commit as historical record with "resolved by universal_new_gates.tex" headers (D3/D6) |

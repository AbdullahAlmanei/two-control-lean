# Email: How the Boykin Lemma 12 Proof Works

**To:** Clifford+T universality collaborators  
**Subject:** Proof logic and dependency boundary for Lemma 12 (`HT_Rz_dense`)

Hi all,

This note explains the proof of Lemma 12 in mathematical terms: why the
Boykin construction works, what each major lemma contributes, what Mathlib
supplies, and where our formal proof differs from the proof in Boykin et al.

The final theorem is:

```lean
theorem HT_Rz_dense (θ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : HTCircuit, hsDistance (rz θ) (HTCircuit.eval C) < ε
```

In words: for every real angle `θ` and every positive tolerance `ε`, there is
a finite circuit containing only `H` and `T` whose matrix is within `ε` of
`Rz(θ)` in Hilbert-Schmidt distance.

## Executive summary

The proof does **not** turn the finite gate alphabet `{H,T}` into a literal
continuously tunable gate. There are only countably many finite H/T circuits.
The point is that a countable set can still be dense, just as the rational
numbers are countable but dense in the real numbers.

The argument has four precise steps.

1. **Find two useful circuits.** Boykin's construction identifies two fixed,
   finite H/T circuits whose matrices satisfy

   ```text
   A = R(n₁, λπ),
   B = R(n₂, λπ),
   ```

   where `n₁` and `n₂` are orthogonal unit axes and `λ` is irrational. These
   are exact matrix equalities, not approximations.

2. **Use repeated applications to approximate any angle about either axis.**
   For every integer `j`,

   ```text
   A^j = R(n₁, jλπ).
   ```

   Because `λ` is irrational, the angles `jλπ`, reduced modulo the rotation
   period, are dense on the circle. Thus, given any target angle `α` and any
   positive error allowance `δ`, some integer `j` satisfies

   ```text
   hsDistance (R(n₁, α)) (A^j) < δ.
   ```

   The same statement holds for `B^k` and rotations `R(n₂, β)`. We have not
   created a continuously parameterized circuit; we have proved that the
   discrete choices `..., A⁻², A⁻¹, I, A, A², ...` come arbitrarily close to
   every rotation about `n₁`.

3. **Rewrite the desired z-rotation using those two axes.** The target matrix
   satisfies

   ```text
   rz(θ) = R(z, -θ/2).
   ```

   Since `n₁` and `n₂` are orthogonal, a two-axis Euler decomposition gives
   real angles `α`, `β`, and `γ` for which

   ```text
   R(z, -θ/2) = R(n₁, α) R(n₂, β) R(n₁, γ).
   ```

   This is again an exact equality. Approximation enters only when the three
   Euler factors are replaced by powers of `A` and `B`.

4. **Approximate the three factors and realize the powers as a circuit.** Use
   the density statements with error allowance `ε/3` to choose integers
   `j`, `k`, and `l` such that

   ```text
   R(n₁, α) ≈ A^j,
   R(n₂, β) ≈ B^k,
   R(n₁, γ) ≈ A^l.
   ```

   A product-distance inequality bounds the error of `A^j B^k A^l` by the
   sum of these three errors, hence by less than `ε`. Finally, because `A`
   and `B` have exact finite H/T implementations, every positive or negative
   integer power also has one. Concatenating those power circuits gives the
   circuit returned by `HT_Rz_dense`.

The complete chain is therefore

```text
rz(θ)
  = R(z, -θ/2)                              exact convention identity
  = R(n₁, α) R(n₂, β) R(n₁, γ)             exact Euler decomposition
  ≈ A^j B^k A^l                             three density choices
  = eval(CA(j) ++ CB(k) ++ CA(l))           exact circuit evaluation
```

with the approximation error in the third line strictly below `ε`.

## Why irrationality is essential

Consider repeatedly applying `A`. The exact power law is

```text
A^j = R(n₁, jλπ).
```

Thus the available angles about `n₁` are the integer multiples of the one
fixed step size `λπ`.

If `λ = p/q` were rational, those angles would eventually repeat modulo
`2π`. The powers of `A` would produce only finitely many matrices and leave
nonzero gaps between the available angles. Choosing a smaller approximation
tolerance could then make some target angles impossible to reach.

When `λ` is irrational, the set

```text
{ jλπ mod 2π | j ∈ ℤ }
```

is dense in the circle. Explicitly, for every target angle `α` and every
angular neighborhood around it, at least one integer multiple `jλπ` lies in
that neighborhood modulo `2π`. Periodicity identifies angles that differ by
a full period, and continuity of `R(n₁,-)` converts closeness of angles into
closeness of matrices:

```text
A^j = R(n₁, jλπ) ≈ R(n₁, α).
```

The same holds for powers of `B` around `n₂`.

Irrationality therefore supplies **dense discrete angle choices**, not a
continuously adjustable gate. This distinction is the heart of the density
argument.

## Why we cannot simply use the `Rz` axis

The gate `T` already acts around the correct axis, up to global phase, but

```text
T^8 = I.
```

Its angle is a rational fraction of a full turn, so its powers form a finite
cycle rather than a dense family.

If we possessed an exactly implementable gate `G = R(z, μπ)` with irrational
`μ`, then powers of `G` would directly approximate every `Rz`, and Euler
decomposition would be unnecessary. Boykin's concrete H/T construction does
not give such a gate. It gives irrational rotations about two oblique axes.

One irrational axis is also insufficient. Every power of `A` has the form
`R(n₁, φ)`, so it remains a rotation about `n₁`. Density lets us choose `φ`
arbitrarily well, but it never changes `n₁` into the standard z-axis.

The second orthogonal axis supplies the missing geometric freedom. Products
of rotations about different axes generally rotate about neither original
axis. The two-axis Euler theorem says, more precisely, that rotations about
`n₁`, then `n₂`, then `n₁` can represent the desired z-axis rotation exactly.
The proof uses density only afterward to approximate each of those three
available-axis rotations by powers of `A` or `B`.

## Proof flow and purpose of each lemma group

### 1. Make axis rotations calculable

We define

```text
R(n, φ) = exp(i φ (n · σ)).
```

The foundational lemmas are:

- `pauliVec_sq_eq_one`: for a unit vector, `(n · σ)^2 = I`.
- `expSeries_even_sq_eq_one` and `expSeries_odd_sq_eq_one`: compute the even
  and odd terms of the matrix exponential series when `A^2 = I`.
- `exp_of_sq_eq_one`: sums those terms into cosine and sine.
- `axisRotation_closed_form`:

  ```text
  R(n,φ) = cos(φ) I + i sin(φ) (n · σ).
  ```

- `axisRotation_mem_unitaryGroup`: proves these rotations are unitary.

Why this chunk exists: the exponential definition is conceptually natural but
too opaque for explicit matrix comparison, periodicity, and Euler algebra.
The closed form turns the problem into trigonometry and three-dimensional
vector algebra.

### 2. Define Boykin's concrete matrices and axes

We formalize the paper's definitions:

```text
A = σz^(-1/4) σx^(1/4),
B = H^(-1/2) A H^(1/2),
```

together with `sigmaZPow`, `sigmaXPow`, `sigmaYPow`, and `HPow`.

The axes are defined from Boykin's coordinate formulas and normalized:

- `boykinN₁_unnorm`, `boykinN₂_unnorm`
- `boykinAxis₁`, `boykinAxis₂`
- `boykin_axes_unit`
- `boykin_axes_orthogonal`

The supporting norm and coordinate lemmas prove that normalization is legal
and that the axes really are orthogonal.

Why this chunk exists: density about two axes is useful only after we know the
matrices are rotations about unit, orthogonal axes.

### 3. Identify `A` and `B` as the required rotations

The key statements are:

```text
boykinA_is_axisRotation:
  A = R(n₁, λπ)

boykinB_is_axisRotation:
  B = R(n₂, λπ).
```

Their helper families compute:

- `cos(λπ)` from the definition of `λ`;
- `sin(λπ)` divided by the two axis norms;
- the coordinates of `sin(λπ)n₁` and `sin(λπ)n₂`;
- the special exponential values at `±π/4` and `±π/2`;
- explicit matrices for `A` and `H^(±1/2)`.

The final proofs compare all four entries of the matrices.

Why this chunk exists: it connects circuit algebra to geometry. After these
equalities, taking a circuit power has the clear meaning of multiplying the
rotation angle around a known axis.

### 4. Prove that `λ` is irrational

Define

```text
ζ = exp(i 2πλ)
P(X) = X^4 + X^3 + (1/4)X^2 + X + 1.
```

The chain is:

1. `rational_angle_is_rootOfUnity`: a rational angle gives a root of unity.
2. `boykinZeta_trace`: computes

   ```text
   ζ + ζ⁻¹ = sqrt(2) - 1/2.
   ```

3. `boykinZeta_satisfies_polynomial`: proves `P(ζ)=0`.
4. `boykinPolynomial_trace_eq`: division by `ζ^2` gives

   ```text
   (ζ + ζ⁻¹)^2 + (ζ + ζ⁻¹) = 7/4.
   ```

5. `not_isIntegral_seven_div_four_complex`: proves `7/4` is not an
   algebraic integer.
6. `boykin_zeta_not_rootOfUnity`: if `ζ` were a root of unity, then `ζ` and
   `ζ⁻¹` would be algebraic integers, forcing `7/4` to be integral, a
   contradiction.
7. `boykinLambda_irrational`: rationality of `λ` would make `ζ` a root of
   unity, contradicting the previous theorem.

Why this chunk exists: it prevents powers of `A` and `B` from cycling through
only finitely many rotations.

### 5. Realize `A`, `B`, and all integer powers by finite H/T words

The exact circuit layer proves:

- `T = σz^(1/4)`;
- `T^2 = σz^(1/2)`;
- `T^6 = σz^(-1/2)`;
- `T^7 = σz^(-1/4)`;
- `H^2 = I` and `T^8 = I`.

From these identities we build and verify circuits for the required
`σx`, `σy`, and `H` powers, followed by:

```text
boykinA_circuit_eval: eval(boykinA_circuit) = A
boykinB_circuit_eval: eval(boykinB_circuit) = B.
```

The density theorem returns integer exponents, which may be negative. The
following machinery handles them:

- `primitiveInvCircuit`: uses `H⁻¹=H` and `T⁻¹=T^7`.
- `circuitInverse_eval`: inverse words evaluate to inverse matrices.
- `circuitPower_eval`: repeated words evaluate to natural powers.
- `eval_boykinA_power_circuit` and `eval_boykinB_power_circuit`: every
  positive or negative integer power is the evaluation of a finite H/T word.

Why this chunk exists: density of abstract matrices is not yet a circuit
existence theorem. These lemmas produce the actual witness required by
`HT_Rz_dense`.

### 6. Turn irrationality into matrix density

The rotation laws establish:

```text
R(n,0) = I
R(n,φ+ψ) = R(n,φ)R(n,ψ)
R(n,φ)⁻¹ = R(n,-φ)
R(n,φ)^k = R(n,kφ)
R(n,φ+2πl) = R(n,φ).
```

The main theorem `axisRotation_powers_dense` then proceeds as follows:

1. Irrationality of `θ/(2π)` implies density of the additive subgroup
   generated by `θ` and `2π`.
2. Choose `k,l ∈ ℤ` such that `kθ + 2πl` is close to the target angle.
3. Remove the full-turn term using periodicity.
4. Identify the remaining rotation with the integer power `R(n,θ)^k`.
5. Use continuity of `axisRotation` and `hsDistance` to convert angular
   closeness into matrix-distance closeness.

Specializing this theorem gives:

```text
boykinA_powers_dense_axis₁:
  A^j approximates R(n₁,α) for arbitrary α

boykinB_powers_dense_axis₂:
  B^k approximates R(n₂,β) for arbitrary β.
```

Why this chunk exists: number theory gives closeness of angles; the target
theorem concerns closeness of matrices. Periodicity and continuity bridge
those two statements.

### 7. Express the target using the two available axes

The scalar/vector representation is

```text
su2Pair(a,u) = aI + i(u · σ).
```

The supporting lemmas are:

- `axisRotation_eq_su2Pair`: represents a rotation as
  `su2Pair(cos φ, sin φ n)`.
- `su2Pair_mul`: gives the multiplication rule involving inner and cross
  products.
- cross-product helper lemmas: bilinearity, anticommutativity,
  orthogonality, and the needed BAC-CAB identity.
- `boykin_euler_product_expansion`: proves Boykin's scalar/vector formula for

  ```text
  R(n₁,α)R(n₂,β)R(n₁,γ).
  ```

The theorem `standardZ_axisRotation_boykin_euler` then:

1. Defines `n₃ = n₁ × n₂`.
2. Proves `n₁,n₂,n₃` form an orthonormal basis.
3. Decomposes the standard `z` axis into coordinates `c₁,c₂,c₃` in that
   basis.
4. Uses Parseval to obtain `c₁²+c₂²+c₃²=1`.
5. Uses `Complex.arg` to construct explicit angles `α,β,γ` satisfying the
   scalar and vector equations from the Euler expansion.
6. Concludes the exact equality

   ```text
   R(z,φ) = R(n₁,α)R(n₂,β)R(n₁,γ).
   ```

Why this chunk exists: dense powers provide arbitrary angles only around
`n₁` and `n₂`. Euler decomposition transfers that angular freedom to the
desired `z` axis.

### 8. Match the project's `Rz` convention

`rz_eq_axisRotation_standardZ` proves the literal equality

```text
rz(θ) = R(z,-θ/2).
```

Why this chunk exists: the Boykin rotation convention uses
`exp(+iφ n·σ)`, while the project's standard `Rz` matrix has diagonal entries
`exp(-iθ/2)` and `exp(+iθ/2)`. The sign and factor of two must be accounted for
exactly.

### 9. Control the total approximation error

The distance layer proves:

- `hsDistance_self`: a unitary has distance zero from itself.
- `trace_inequality`: the projective trace inequality underlying product
  error accumulation.
- `hsDistance_mul_le`:

  ```text
  d(U₁U₂,V₁V₂) ≤ d(U₁,V₁) + d(U₂,V₂).
  ```

- `hsDistance_triple_mul_le`: the corresponding three-factor inequality.

Why this chunk exists: approximating each Euler factor separately is useful
only if those local errors imply a bound on the full product.

### 10. Build the final circuit for a supplied `ε`

Fix arbitrary `θ` and `ε>0`.

1. `standardZ_axisRotation_boykin_euler (-(θ/2))` provides `α,β,γ` and the
   exact target factorization.
2. Since `ε/3>0`, choose integers `j,k,l` with

   ```text
   d(R(n₁,α),A^j) < ε/3,
   d(R(n₂,β),B^k) < ε/3,
   d(R(n₁,γ),A^l) < ε/3.
   ```

3. Define

   ```text
   C = CA(j) ++ CB(k) ++ CA(l).
   ```

4. The circuit-power evaluation lemmas give

   ```text
   eval(C) = A^j B^k A^l.
   ```

5. `hsDistance_triple_mul_le` gives

   ```text
   d(rz(θ),eval(C))
     < ε/3 + ε/3 + ε/3
     = ε.
   ```

This is exactly the conclusion of `HT_Rz_dense`.

## Boundary between our proof and Mathlib

The project-specific mathematical work is ours; the general-purpose analysis,
topology, algebra, and linear algebra APIs are supplied by Mathlib.

### What we prove in this project

We prove or define:

- the concrete Pauli-vector and axis-rotation setup used by this argument;
- the matrix exponential closed form specialized to matrices squaring to one;
- Boykin's concrete `A`, `B`, `λ`, `n₁`, and `n₂`;
- normalization and orthogonality of the Boykin axes;
- the complete matrix identities identifying `A` and `B` as rotations;
- the root-of-unity/algebraic-integer contradiction proving `λ` irrational;
- explicit finite H/T circuits for `A`, `B`, their inverses, and all integer
  powers;
- continuity and periodicity specialized to the axis-rotation family;
- the scalar/vector multiplication and Euler-product formulas;
- an explicit Euler inversion specialized to the standard `z` axis;
- the three-factor error theorem used here;
- the final construction and `ε/3` argument.

### What Mathlib supplies

Mathlib supplies the reusable foundations:

| Area | Main imported facts |
|---|---|
| Matrix exponential | exponential series, summation, and `exp_add_of_commute` |
| Trigonometry | cosine/sine series, addition formulas, special values, and `arccos` facts |
| Dense rotations | density of the subgroup generated by `a,b` iff `a/b` is irrational; integer description of subgroup elements |
| Topology | continuity APIs and selection of points from dense subsets |
| Euclidean geometry | norms, inner products, finite sums, and orthonormal-basis reconstruction |
| Complex polar form | `arg`, `norm*cos(arg)=re`, and `norm*sin(arg)=im` |
| Roots of unity | rational complex phases have finite order |
| Algebraic integrality | roots of monic polynomials are integral and integrality is closed under sums and powers |
| Unitary matrices | unitary-group characterizations and closure under products and powers |
| Hilbert spaces | Cauchy-Schwarz and norm inequalities used in the trace-distance proof |
| Automation | finite-index case splits and normalization of polynomial, field, linear, and integer arithmetic |

The boundary is important: Mathlib does not know Boykin's construction or the
Clifford+T theorem. It provides general theorems from which we prove the
Boykin-specific statements and assemble the final circuit.

## How our proof differs from Boykin's paper

The proof follows Boykin's core construction but not every published
intermediate claim.

### 1. We prove only the target needed for Lemma 12

Boykin proves density in all of `SU(2)`. Our final dependency chain proves the
Euler decomposition only for the standard `z`-axis rotations needed to
approximate `Rz`.

This is logically sufficient for the Clifford+T universality proof and avoids
formalizing an unnecessary generic `SU(2)` parameterization.

### 2. We avoid formalizing the `SO(3)`/`SU(2)` local isomorphism

Boykin motivates the argument using the local isomorphism between real
three-dimensional rotations and `SU(2)`. We instead calculate directly with

```text
aI + i(u · σ)
```

and prove its multiplication and Euler formulas as matrix identities.

### 3. We explicitly invert the Euler equations

The paper says the scalar/vector equations can be inverted. We construct the
angles for the standard `z` axis using an orthonormal frame, Parseval's
identity, and complex polar coordinates.

### 4. We use only the cyclotomic implication actually required

Boykin invokes a theorem about cyclotomic minimal polynomials and states that
the displayed quartic is irreducible and non-cyclotomic.

We do not prove that full generic theorem or the quartic's irreducibility.
Instead, we prove the elementary implication

```text
λ rational -> exp(i2πλ) is a root of unity
```

and contradict root-of-unity integrality using Boykin's polynomial equation
and the nonintegrality of `7/4`.

### 5. We use integer powers and construct their inverse words

The dense additive-subgroup theorem naturally returns integer coefficients.
We explicitly show that negative powers remain finite H/T circuits through
`H⁻¹=H` and `T⁻¹=T^7`.

### 6. We make topology and error accounting explicit

The paper writes phase approximation informally. We prove the continuity that
turns angular density into Hilbert-Schmidt density, and we prove the product
distance inequality that turns three local approximations into the final
`ε` guarantee.

### 7. The final theorem uses a phase-insensitive metric

Hilbert-Schmidt distance identifies globally phase-equivalent unitaries at
distance zero. This matches the physically relevant notion of a quantum gate.
However, the crucial equalities in this particular chain,

```text
rz(θ) = R(z,-θ/2)
```

and the specialized Euler decomposition, are proved as literal matrix
equalities. Global-phase invariance is part of the surrounding distance
framework, not a hidden replacement for those two equalities.

## Final takeaway

The proof works because each chunk solves one precise obstruction:

```text
finite gate set versus continuous target
  solved by an irrational rotation angle;

wrong rotation axes
  solved by a second orthogonal axis and Euler decomposition;

abstract dense powers versus actual circuits
  solved by explicit power and inverse circuit constructions;

three local approximations versus one target approximation
  solved by the Hilbert-Schmidt product inequality.
```

Therefore, for every `θ` and every `ε>0`, the construction produces a finite
H/T circuit `C` with

```text
hsDistance (rz θ) (eval C) < ε.
```

The critical theorem and its public Lemma 12 wrapper are axiom-clean apart
from Mathlib's standard logical axioms (`propext`, `Classical.choice`, and
`Quot.sound`); neither depends on `sorryAx`.

Best,

The Clifford+T formalization team

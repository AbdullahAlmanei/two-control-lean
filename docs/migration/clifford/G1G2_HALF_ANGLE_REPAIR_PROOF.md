# Half-Angle Repair For The `G1,G2` Euler Step

> **HISTORICAL (resolved 2026-07-10).** This note pertains to the June 2026
> `updated_cliff.tex` gates `G1 = e^{-i pi/4} THTH`, `G2 = e^{-i pi/4} HTHT`.
> The July 1, 2026 revision `reference/cliff/universal_new_gates.tex` replaces
> them with `G1 = e^{-3i pi/8} THTHT` and `G2 = (HT^4) G1 (HT^4)^dag`, whose
> axes are orthogonal, so the three-factor Euler step is globally valid and no
> half-angle repair is needed.  The formalization now follows the July paper
> (`TwoControl/Clifford/Lemma12/G1G2/`); the `HalfAngleRepair.lean` file
> mentioned below was removed together with the old Boykin track.

This note records the corrected version of the `G1,G2` argument from
`reference/cliff/updated_cliff.tex`.

The original global claim

```text
every determinant-one one-qubit unitary is G1^a G2^b G1^c
```

is false for the specific gates

```text
G1 = exp(-i*pi/4) T H T H
G2 = exp(-i*pi/4) H T H T.
```

The repair below does not recover a global three-factor statement.  Instead,
it proves that every `Rz(theta)` can be reduced to two small rotations, and
each small rotation has the desired three-factor form.  Thus the corrected
replacement is a six-real-power statement:

```text
Rz(theta) ~ (G1^a G2^b G1^c) (G1^a' G2^b' G1^c').
```

This is still enough for Lemma 12, because the irrational-power approximation
argument applies to each real power separately and the product-distance lemma
adds the errors.

## The Local Three-Factor Criterion

Let `n1` and `n2` be the two unit axes coming from `G1` and `G2`, and write

```text
k = <n1,n2>.
```

After changing basis so that `n1` is the z-axis, we can write

```text
n2 = (sqrt(1-k^2), 0, k).
```

For a rotation

```text
R_n(x) = cos(x) I + i sin(x) n.sigma,
```

a direct multiplication gives

```text
R_n1(a) R_n2(b) R_n1(c)
```

with top-left entry

```text
exp(i(a+c)) (cos(b) + i k sin(b)).
```

Therefore, if

```text
R_n1(a) R_n2(b) R_n1(c) = t I + i w.sigma,
```

then necessarily

```text
t^2 + <w,n1>^2 >= k^2.
```

Conversely, this condition is also sufficient.  Given a target matrix
`t I + i w.sigma`, put it in the basis where `n1` is diagonal.  Its top-left
entry has squared norm `t^2 + <w,n1>^2`, and its off-diagonal entry has squared
norm `1 - (t^2 + <w,n1>^2)`.  If

```text
t^2 + <w,n1>^2 >= k^2,
```

then the off-diagonal norm is at most `sqrt(1-k^2)`.  We can choose `b` so that
the off-diagonal norm of `R_n2(b)` matches the target, then choose `a+c` to
match the phase of the top-left entry and `a-c` to match the phase of the
off-diagonal entry.  Solving these two linear equations gives `a` and `c`.

So the correct local criterion is:

```text
t I + i w.sigma has an ABA form using n1,n2
iff
t^2 + <w,n1>^2 >= k^2.
```

For orthogonal axes, `k = 0`, so the condition is automatic.  That is exactly
why the usual three-factor Euler decomposition works globally in the
orthogonal case.

## The Specific Constants

For the axes obtained from the paper's `G1,G2`, exact calculation gives

```text
(n1_z)^2 = 1 / (5 - 2 sqrt(2))
         = (5 + 2 sqrt(2)) / 17
```

and

```text
k = <n1,n2> = (2 sqrt(2) - 1) / (5 - 2 sqrt(2))
             = (3 + 8 sqrt(2)) / 17.
```

The counterexample `Rz(pi)` fails the criterion because

```text
(n1_z)^2 < k^2.
```

However, a small z-rotation does satisfy the criterion.  For

```text
Rz(phi) = cos(phi/2) I - i sin(phi/2) Z,
```

we have

```text
t^2 + <w,n1>^2
= cos(phi/2)^2 + (n1_z)^2 sin(phi/2)^2.
```

If `|phi| <= pi/2`, then `sin(phi/2)^2 <= 1/2`.  Therefore

```text
cos(phi/2)^2 + (n1_z)^2 sin(phi/2)^2
>= (1 + (n1_z)^2) / 2.
```

For the exact constants above,

```text
(1 + (n1_z)^2) / 2 - k^2
= (50 - 31 sqrt(2)) / 289
> 0.
```

Thus every `Rz(phi)` with `|phi| <= pi/2` has a three-factor form

```text
Rz(phi) = G1^a G2^b G1^c
```

up to global phase.

## The Repaired Lemma 12 Route

Given an arbitrary real angle `theta`, reduce it modulo `2*pi` up to global
phase, so that `|theta0| <= pi` and

```text
Rz(theta) ~ Rz(theta0).
```

Set

```text
phi = theta0 / 2.
```

Then `|phi| <= pi/2`, so the local criterion applies and gives real numbers
`a,b,c` such that

```text
Rz(phi) ~ G1^a G2^b G1^c.
```

Since

```text
Rz(theta0) = Rz(phi)^2,
```

we get the corrected real-power decomposition

```text
Rz(theta)
~ (G1^a G2^b G1^c) (G1^a G2^b G1^c).
```

This is not the original three-factor statement for arbitrary `theta`; that
statement is false.  But it is enough for the density proof.  The irrationality
argument approximates each real power `G1^a`, `G2^b`, and `G1^c` by an integer
power.  Then the product-distance lemma combines the six approximation errors.

The Lean file

```text
TwoControl/Clifford/Lemma12/G1G2/HalfAngleRepair.lean
```

verifies the exact algebraic inequality

```text
(1 + (n1_z)^2) / 2 > k^2
```

for the constants above, and packages it in the form needed for small
`Rz(phi)` rotations.

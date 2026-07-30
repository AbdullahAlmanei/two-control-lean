---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

Useful links:

* [Blueprint](blueprint/)
* [Blueprint as pdf](blueprint.pdf)
* [Dependency graph](blueprint/dep_graph_document.html)
* [API documentation](docs/)
* [GitHub repository](https://github.com/AbdullahAlmanei/two-control-lean)

## What is formalized

This is a Lean 4 formalization covering two results in quantum circuit
synthesis. Every claim below is checked by `lake build` together with an audit
of `#print axioms` for each public declaration; the blueprint marks the status
of every individual statement and proof.

**Complete and `sorry`-free.**

* *Optimal implementation of quantum gates with two controls*, Sections 3–7.
  A doubly-controlled one-qubit gate $CC(U)$ is a product of at most four
  two-control factors exactly when the eigenvalues of $U$ coincide or
  $\det U = 1$.
* *Clifford+T is universal.* For every $n$-qubit unitary $U$ and every
  $\varepsilon > 0$ there is a Clifford+T circuit within Hilbert–Schmidt
  distance $\varepsilon$ of $U$. The axiom closure of the Lean theorem is
  exactly `[propext, Classical.choice, Quot.sound]`.

**In progress.** Closed-form circuit-length bounds. The exact stage is proved;
the logarithmic approximation stage is stated in Lean with proofs pending.
There are 14 `sorry` sites in the built library, all in that track, and every
one is flagged in the blueprint.

A Ross–Selinger optimal-approximation engine also lives in the repository but
is paused and not built.

## A found erratum

The June 2026 draft of the universality paper proved its $R_z$-approximation
lemma using generators $G_1 = e^{-i\pi/4}THTH$ and $G_2 = e^{-i\pi/4}HTHT$
together with a three-factor Euler decomposition. That step is false for those
generators — their rotation axes are not orthogonal, and $R_z(\pi)$ is an
explicit counterexample. This was found during formalization. The July 2026
paper resolves it by changing the generators to
$G_1 = e^{-3i\pi/8}THTHT$ and $G_2 = (HT^4)G_1(HT^4)^\dagger$, whose axes are
orthogonal; the formalization follows the corrected version. See the blueprint
overview for details.

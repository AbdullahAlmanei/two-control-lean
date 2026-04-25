# Clifford Lemma 11 — Dependency Graph

This file records the proof graph that should be considered settled before the Lean stubs are written.

```mermaid
graph TD
  L2["Lemma 2 (2-qubit specialization)\nexisting: TwoControl.CosineSine.cosinesine_exists"]
  L3["Lemma 3\nRy via H,S,S†,Rz"]
  L4["Lemma 4 (2-qubit specialization)\ndemultiplexing"]
  CRZ["Controlled Rz pair synthesis"]
  OQ["One-qubit exact synthesis\nover {H, T, Rz(θ)}"]
  L11["Lemma 11\n2-qubit synthesis over {C(X), H, T, Rz(θ)}"]

  L2 --> L4
  L3 --> L4

  L2 --> L11
  L3 --> L11
  L4 --> L11
  CRZ --> L11
  OQ --> L11
```

## Reading Notes

- `Lemma 2 (2-qubit specialization)` is imported from the existing cosine-sine appendix rather than reproved.
- `Lemma 4 (2-qubit specialization)` is the first genuinely new decomposition node in this track.
- `Controlled Rz pair synthesis` and `One-qubit exact synthesis` are local support propositions introduced because they are required by the planned proof of Lemma 11 even though they are not numbered Clifford-paper lemmas.
- The recursive `n`-qubit Lemma 1 is intentionally outside this first dependency graph.
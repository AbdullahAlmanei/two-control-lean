# Project context

This project is not merely to port one Rocq proof to Lean.
It is a case study in building a reusable methodology for translating large formal proofs from Rocq/Coq to Lean.

## Source layers
1. The paper — official numbering and public proof structure.
2. The Rocq proof — existing formalization, helper lemmas, and decomposition.
3. The theorem-map / packet layer — internal migration ledger.
4. The Blueprint layer — first public-facing target in this pipeline.
5. The Lean layer — not yet created in this pipeline.

## Scope of this pipeline
This pipeline ends at the first Blueprint section files.
It does not create Lean declarations yet.

## Working philosophy
- Use the paper for official numbering and public theorem identity.
- Use Rocq heavily for completeness checking, dependency expansion, and proof-structure discovery.
- Do not treat Rocq names or file organization as the final Lean architecture.
- Do not invent missing objects.
- Surface ambiguity instead of guessing.

## Section structure
The project currently focuses on Sections 3–7 of the paper.
Section 3 contains foundational eigenvalue lemmas.
Section 4 contains key building blocks.
Section 5 contains the first main lemma.
Section 6 contains the second main lemma sequence.
Section 7 contains the wrap-up to the main result.
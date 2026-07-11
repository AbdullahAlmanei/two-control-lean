# Section 6 — Generation Packet

Derived from:
- section6_reconciled_packet.md

## Lemma 6.1

- paper_id: Lemma 6.1
- blueprint_label: lem:s6_1
- blueprint_section_file: blueprint/src/chapters/section6.tex
- blueprint_uses: []
- lean_name: TwoControl.section6_lemma_6_1
- lean_target_file: TwoControl/Section6.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: Three-way disjunction (entangled / z⊗ψ / ψ⊗z). Only dependency is Appendix Lemma A.23, excluded from first Blueprint.
- unresolved_formalization_questions: none

## Lemma 6.2

- paper_id: Lemma 6.2
- blueprint_label: lem:s6_2
- blueprint_section_file: blueprint/src/chapters/section6.tex
- blueprint_uses: [lem:s6_1, lem:s4_4]
- lean_name: TwoControl.section6_lemma_6_2
- lean_target_file: TwoControl/Section6.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: Three-way disjunction via case analysis of V3† using Lemma 6.1. Also depends on Lemma 4.4 from Section 4. Remaining dependencies (Lemmas A.10, A.12, A.17, A.19, A.22, A.25, A.31) are all Appendix, excluded from first Blueprint.
- unresolved_formalization_questions: none

## Lemma 6.3

- paper_id: Lemma 6.3
- blueprint_label: lem:s6_3
- blueprint_section_file: blueprint/src/chapters/section6.tex
- blueprint_uses: [lem:s6_2]
- lean_name: TwoControl.section6_lemma_6_3
- lean_target_file: TwoControl/Section6.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: Derives structured W1–W4 decomposition via Lemma 6.2. Remaining dependencies (Lemmas A.18, A.22, A.26, A.28, A.29, A.30) are all Appendix, excluded from first Blueprint. The longest proof in section 6 (~360 Rocq lines); the Rocq proof explicitly constructs β_perp and verifies Q's unitarity.
- unresolved_formalization_questions: none

## Lemma 6.4

- paper_id: Lemma 6.4
- blueprint_label: lem:s6_4
- blueprint_section_file: blueprint/src/chapters/section6.tex
- blueprint_uses: [lem:s6_1, lem:s6_3, lem:s4_2, lem:s4_3]
- lean_name: TwoControl.section6_lemma_6_4
- lean_target_file: TwoControl/Section6.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: The second main lemma (iff). Forward direction uses Lemma 6.1, 6.3, 4.2, and 4.3. Reverse direction reuses Lemma 4.3 directly. Remaining dependencies (Lemmas A.19, A.28, A.32, A.33) are all Appendix, excluded from first Blueprint. Note: Rocq case B/C ordering is swapped relative to paper case 2/3 (presentational only).
- unresolved_formalization_questions: none

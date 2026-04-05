# Section 7 — Generation Packet

Derived from:
- section7_reconciled_packet.md

## Lemma 7.1

- paper_id: Lemma 7.1
- blueprint_label: lem:s7_1
- blueprint_section_file: blueprint/src/chapters/section7.tex
- blueprint_uses: []
- lean_name: TwoControl.section7_lemma_7_1
- lean_target_file: TwoControl/Section7.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: No paper-numbered dependencies. Appendix and helper dependencies (ccu_diag, diag_control, Diag_diag2, diag2_unitary) are Rocq-only helpers excluded from first-Blueprint uses.
- unresolved_formalization_questions: none

## Lemma 7.2

- paper_id: Lemma 7.2
- blueprint_label: lem:s7_2
- blueprint_section_file: blueprint/src/chapters/section7.tex
- blueprint_uses: [lem:s7_1]
- lean_name: TwoControl.section7_lemma_7_2
- lean_target_file: TwoControl/Section7.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: Paper dependencies include Lemma 7.1 (first-Blueprint node), Lemma A.12, and Lemma A.13. Appendix lemmas A.12 and A.13 are excluded from blueprint_uses under first-Blueprint policy. The paper introduces two unnumbered inline definitions (canonical product, R(u₀, u₁)) at the start of Section 7; these are not separate Blueprint nodes. The Rocq hypothesis is stronger than the paper's (exactly four TwoQubitGate factors vs. "at most four of G₂ \ G₁ and any number of G₁"), bypassing paper Steps 1–2.
- unresolved_formalization_questions: The Lean formalisation will need to decide whether to follow the Rocq's stronger hypothesis (four TwoQubitGate factors) or the paper's original formulation (at most four G₂ \ G₁ plus any G₁). The choice affects whether Steps 1–2 need explicit proofs.

## Lemma 7.3

- paper_id: Lemma 7.3
- blueprint_label: lem:s7_3
- blueprint_section_file: blueprint/src/chapters/section7.tex
- blueprint_uses: []
- lean_name: TwoControl.section7_lemma_7_3
- lean_target_file: TwoControl/Section7.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: Self-contained algebraic lemma with no dependencies on other main lemmas. Uses R(u₀, u₁) definition from the section preamble.
- unresolved_formalization_questions: none

## Theorem 7.4

- paper_id: Theorem 7.4
- blueprint_label: thm:s7_4
- blueprint_section_file: blueprint/src/chapters/section7.tex
- blueprint_uses: [lem:s7_2, lem:s5_1, lem:s6_4, lem:s7_3]
- lean_name: TwoControl.section7_theorem_7_4
- lean_target_file: TwoControl/Section7.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: All four paper dependencies are first-Blueprint nodes. Forward direction uses lem:s7_2 → lem:s5_1/lem:s6_4 → lem:s7_3. Backward direction uses lem:s5_1 (reverse). The Rocq statement inherits the stronger TwoQubitGate hypothesis from m7_2.
- unresolved_formalization_questions: Same hypothesis-form question as Lemma 7.2: whether to use the Rocq's TwoQubitGate formulation or the paper's G₁/G₂ formulation.

## Corollary 7.5

- paper_id: Corollary 7.5
- blueprint_label: cor:s7_5
- blueprint_section_file: blueprint/src/chapters/section7.tex
- blueprint_uses: [thm:s7_4]
- lean_name: TwoControl.section7_corollary_7_5
- lean_target_file: TwoControl/Section7.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: Paper dependency on Theorem A.3 (spectral theorem) is excluded from blueprint_uses under first-Blueprint policy. Only Theorem 7.4 is a first-Blueprint dependency. The Rocq statement form (∃ V D with explicit diagonalisation) differs structurally from the paper's eigenvalue/det form; the Lean formalisation can choose either.
- unresolved_formalization_questions: The Lean statement could follow the paper (eigenvalues equal or det(U) = 1) or the Rocq (∃ V D with conditions). The paper form is more natural for users; the Rocq form avoids needing a separate eigenvalue API. Decision deferred.

# Section 4 — Generation Packet

Derived from:
- section4_reconciled_packet.md

---

## Lemma 4.1

- paper_id: Lemma 4.1
- blueprint_label: lem:s4_1
- blueprint_section_file: blueprint/src/chapters/section4.tex
- blueprint_uses: [lem:s3_2]
- lean_name: TwoControl.section4_lemma_4_1
- lean_target_file: TwoControl/Section4.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: Paper implicit dependency Lemma A.4 excluded from blueprint_uses under first-Blueprint policy (Appendix node). Rocq proof does not invoke a4 directly; content absorbed into algebraic steps.
- unresolved_formalization_questions: none

---

## Lemma 4.2

- paper_id: Lemma 4.2
- blueprint_label: lem:s4_2
- blueprint_section_file: blueprint/src/chapters/section4.tex
- blueprint_uses: []
- lean_name: TwoControl.section4_lemma_4_2
- lean_target_file: TwoControl/Section4.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: Paper claims Lemma 3.2 as explicit dependency but reconciliation found Rocq proof m4_2 does not invoke m3_2; excluded from blueprint_uses. Paper implicit dependency Lemma A.8 excluded under first-Blueprint policy (Appendix node). Rocq uses a8 explicitly for the projector identity Q|0⟩⟨0|Q† + Q|1⟩⟨1|Q† = I.
- unresolved_formalization_questions: Verify whether the paper's claimed dependency on Lemma 3.2 is a citation for context or a genuine proof dependency before Lean formalization.

---

## Lemma 4.3

- paper_id: Lemma 4.3
- blueprint_label: lem:s4_3
- blueprint_section_file: blueprint/src/chapters/section4.tex
- blueprint_uses: [lem:s3_3]
- lean_name: TwoControl.section4_lemma_4_3
- lean_target_file: TwoControl/Section4.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: Paper explicit dependencies Lemma A.27, Theorem A.3 excluded from blueprint_uses under first-Blueprint policy (Appendix nodes). Paper implicit dependencies Lemma A.4, Lemma A.11 also excluded (Appendix). Rocq uses a27, a3, a11 directly. This is the longest Section 4 proof (~360 Rocq lines). Reverse direction parameterises via Cexp(θ/2) and constructs controlled-P witnesses.
- unresolved_formalization_questions: none

---

## Lemma 4.4

- paper_id: Lemma 4.4
- blueprint_label: lem:s4_4
- blueprint_section_file: blueprint/src/chapters/section4.tex
- blueprint_uses: [lem:s4_3]
- lean_name: TwoControl.section4_lemma_4_4
- lean_target_file: TwoControl/Section4.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: Derived from Lemma 4.3 by adjoint/role-exchange. Rocq uses a13_1, a12, acgate_adjoint, swapab_hermitian, swapab_inverse (all Appendix/Helper, excluded from blueprint_uses). Paper gives no independent proof.
- unresolved_formalization_questions: none
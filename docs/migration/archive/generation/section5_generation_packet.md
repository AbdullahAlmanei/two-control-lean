# Section 5 — Generation Packet

Derived from:
- section5_reconciled_packet.md

## Lemma 5.1

- paper_id: Lemma 5.1
- blueprint_label: lem:s5_1
- blueprint_section_file: blueprint/src/chapters/section5.tex
- blueprint_uses: [lem:s3_1, lem:s4_1]
- lean_name: TwoControl.section5_lemma_5_1
- lean_target_file: TwoControl/Section5.lean
- lean_namespace: TwoControl
- statement_generation_status: ready
- stub_generation_notes: The first main lemma (iff). Forward direction uses Lemma 3.1, Lemma A.24, and Lemma 4.1 in sequence. Reverse direction has two explicit witness constructions (u0=u1 case and u0·u1=1 case). Lemma A.24 is an Appendix dependency excluded from the first Blueprint. The Rocq proof also relies on helper infrastructure (block_decomp, block_multiply, block_equalities, diagonal commutativity chain) and uses notc (CNOT) as an explicit witness in the reverse u0·u1=1 case.
- unresolved_formalization_questions: none

# Global Theorem Map

## Section 3

| paper_id | object_type | packet | rocq_decl | generation_packet | blueprint_file | status | ambiguities |
|---|---|---|---|---|---|---|---|
| Lemma 3.1 | lemma | section3_reconciled_packet.md | m3_1 | | | reconciled | none |
| Lemma 3.2 | lemma | section3_reconciled_packet.md | m3_2 | | | reconciled | none |
| Lemma 3.3 | lemma | section3_reconciled_packet.md | m3_3 | | | reconciled | none |

## Section 4

| paper_id | object_type | packet | rocq_decl | generation_packet | blueprint_file | status | ambiguities |
|---|---|---|---|---|---|---|---|
| Lemma 4.1 | lemma | section4_reconciled_packet.md | m4_1 | | | reconciled | none |
| Lemma 4.2 | lemma | section4_reconciled_packet.md | m4_2 | | | reconciled | Paper claims explicit dependency on Lemma 3.2 but Rocq proof does not use m3_2 |
| Lemma 4.3 | lemma | section4_reconciled_packet.md | m4_3 | | | reconciled | none |
| Lemma 4.4 | lemma | section4_reconciled_packet.md | m4_4 | | | reconciled | none |

## Section 5

| paper_id | object_type | packet | rocq_decl | generation_packet | blueprint_file | status | ambiguities |
|---|---|---|---|---|---|---|---|
| Lemma 5.1 | lemma | section5_reconciled_packet.md | m5_1 | section5_generation_packet.md | blueprint/src/chapters/section5.tex | generation-planned | none |

## Section 6

| paper_id | object_type | packet | rocq_decl | generation_packet | blueprint_file | status | ambiguities |
|---|---|---|---|---|---|---|---|
| Lemma 6.1 | lemma | section6_reconciled_packet.md | m6_1 | section6_generation_packet.md | blueprint/src/chapters/section6.tex | generated | none |
| Lemma 6.2 | lemma | section6_reconciled_packet.md | m6_2 | section6_generation_packet.md | blueprint/src/chapters/section6.tex | generated | none |
| Lemma 6.3 | lemma | section6_reconciled_packet.md | m6_3 | section6_generation_packet.md | blueprint/src/chapters/section6.tex | generated | none |
| Lemma 6.4 | lemma | section6_reconciled_packet.md | m6_4 | section6_generation_packet.md | blueprint/src/chapters/section6.tex | generated | Rocq case B/C ordering swapped relative to paper case 2/3 ordering |

## Section 7

| paper_id | object_type | packet | rocq_decl | generation_packet | blueprint_file | status | ambiguities |
|---|---|---|---|---|---|---|---|
| Lemma 7.1 | lemma | section7_reconciled_packet.md | m7_1 | section7_generation_packet.md | blueprint/src/chapters/section7.tex | generation-planned | none |
| Lemma 7.2 | lemma | section7_reconciled_packet.md | m7_2 | section7_generation_packet.md | blueprint/src/chapters/section7.tex | generation-planned | Paper introduces two unnumbered inline definitions (canonical product, R(u₀,u₁)) with no formal labels |
| Lemma 7.3 | lemma | section7_reconciled_packet.md | m7_3 | section7_generation_packet.md | blueprint/src/chapters/section7.tex | generation-planned | none |
| Theorem 7.4 | theorem | section7_reconciled_packet.md | m7_4 | section7_generation_packet.md | blueprint/src/chapters/section7.tex | generation-planned | Rocq quantifies over four TwoQubitGate factors instead of paper's "at most four of G₂\G₁ and any number of G₁" |
| Corollary 7.5 | corollary | section7_reconciled_packet.md | m7_5 | section7_generation_packet.md | blueprint/src/chapters/section7.tex | generation-planned | Rocq statement form (∃ V D with conditions) differs structurally from paper's eigenvalue/det form |
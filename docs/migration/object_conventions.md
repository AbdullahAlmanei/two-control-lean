# Object conventions

These conventions apply to paper packets, Rocq packets, reconciled packets, theorem-map rows, and generation packets.

## Paper identity
Preserve the paper’s numbering exactly.

Examples:
- Lemma 3.1
- Lemma 4.3
- Theorem 7.4
- Corollary 7.5

Never rename paper-numbered objects creatively.

## Object types
Use exactly one of:
- definition
- lemma
- theorem
- corollary
- proposition

Do not invent other type labels.

## Section numbers
Use integer section numbers only:
- 3
- 4
- 5
- 6
- 7

## Source pages
Use `source_pages` to mean the printed page numbers shown in the paper/PDF text, not raw PDF page indices.

Examples:
- `source_pages: [216, 217]`
- `source_pages: [222]`

## Ordering
Within every packet and in the theorem map:
1. order objects by paper section
2. then by paper numbering
3. never reorder for convenience

## Ambiguity handling
If something is uncertain, write it explicitly in `ambiguities`.
Use `none` when there is no ambiguity.

## Dependency handling
In paper packets and reconciled packets:
- `paper_dependencies_explicit` = dependencies explicitly stated or clearly invoked in the paper
- `paper_dependencies_implicit` = dependencies that appear necessary from the proof sketch but are not explicitly cited

In Rocq packets:
- keep Rocq direct dependencies separate from helpers and definitions

## File naming patterns
Per-section packet files:
- `docs/migration/packets/sectionN_paper_packet.md`
- `docs/migration/packets/sectionN_rocq_packet.md`
- `docs/migration/packets/sectionN_reconciled_packet.md`

Per-section generation files:
- `docs/migration/generation/sectionN_generation_packet.md`

## Output discipline
Every packet should be a standalone file with no chatty prose outside the schema.
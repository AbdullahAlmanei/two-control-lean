# Generation naming conventions

These conventions apply only in generation planning and Blueprint generation.

## First-Blueprint policy
For the first Blueprint:
- create nodes only for paper-numbered objects in Sections 3–7
- do not create Blueprint nodes for Appendix lemmas yet
- do not create Blueprint nodes for Rocq-only helper declarations
- Appendix and Rocq-only helper information stays in packets and notes, not as first-Blueprint nodes

## Blueprint labels
Use these exact forms:
- lem:sX_Y
- thm:sX_Y
- cor:sX_Y
- prop:sX_Y
- def:sX_shortname

Examples:
- `lem:s3_1`
- `lem:s4_3`
- `thm:s7_4`
- `cor:s7_5`

If a paper object is numbered, the label must preserve that numbering.

## Blueprint section files
Use:
- `blueprint/src/chapters/section3.tex`
- `blueprint/src/chapters/section4.tex`
- `blueprint/src/chapters/section5.tex`
- `blueprint/src/chapters/section6.tex`
- `blueprint/src/chapters/section7.tex`

## Blueprint uses policy
`blueprint_uses` should list only labels that are first-Blueprint nodes under the policy above.

Therefore:
- include dependencies on other paper-numbered objects in Sections 3–7
- exclude Appendix lemmas from `blueprint_uses` in the first Blueprint
- exclude Rocq-only helper declarations from `blueprint_uses`

Those excluded dependencies should remain documented in the reconciled packet and generation notes.

## Future Lean names
Even though this pipeline does not create Lean files yet, every generation packet should assign a future Lean name.

Use namespace `TwoControl`.

Forms:
- `TwoControl.section3_lemma_3_1`
- `TwoControl.section4_lemma_4_3`
- `TwoControl.section7_theorem_7_4`
- `TwoControl.section7_corollary_7_5`

## Future Lean target files
Plan names only. Do not create these files in this pipeline.

Target file conventions:
- `TwoControl/Definitions.lean`
- `TwoControl/Section3.lean`
- `TwoControl/Section4.lean`
- `TwoControl/Section5.lean`
- `TwoControl/Section6.lean`
- `TwoControl/Section7.lean`

For paper-numbered theorem statements in Sections 3–7, assign them to the matching `TwoControl/SectionN.lean`.

## Blueprint \lean fields
The first Blueprint should still emit `\lean{...}` with the planned future Lean names.

That means `leanblueprint checkdecls` is expected to fail until the later Lean-stub pipeline is run.
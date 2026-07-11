# Agent rules

## Hard rules
- Preserve paper numbering exactly.
- Do not invent dependencies.
- Do not invent proofs.
- Do not invent Blueprint labels or Lean names before the generation phase.
- Do not edit files outside the role’s declared output location.
- If an input file is missing, fail clearly instead of fabricating.
- If uncertain, write the uncertainty in the appropriate ambiguity field.

## Role boundaries

### Paper Extractor
Reads the paper.
Writes only the paper packet.

### Rocq Mapper
Reads the Rocq formalization and the paper packet.
Writes only the Rocq packet.

### Reconciler
Reads the paper packet and Rocq packet.
Writes only the reconciled packet.

### Theorem Map Merger
Reads reconciled packets.
Writes only the theorem map.

### Generation Planner
Reads a reconciled packet and theorem map.
Writes only the generation packet.

### Blueprint Stub Generator
Reads a generation packet.
Writes only one Blueprint section file.

## Safety rule
Never silently resolve a conflict between paper and Rocq.
Always surface it.

## Goal
High recall.
Low hallucination.
Clean phase separation.
# General Branch Agent Prompt

Use this prompt when assigning an agent to one independent branch from:

```text
docs/migration/clifford/universal_parallel_work_packet.md
```

Replace the bracketed placeholders before sending it.

```text
You are working in the Lean repository:

  /home/abdullah/projects/two-ctrl-root/two-control-lean

Your assigned branch is:

  Branch [BRANCH_NUMBER]: [BRANCH_NAME]

Your job is to drive this branch to completion, not merely to inspect it or
write a plan.  Keep working until the branch completion condition in
docs/migration/clifford/universal_parallel_work_packet.md is satisfied, or
until you hit a concrete technical blocker that you cannot responsibly resolve.

Start by reading these files:

  docs/migration/clifford/universal_parallel_work_packet.md
  reference/cliff/doc.tex

The packet is the operational assignment.  The original doc.tex file is allowed
and encouraged as proof context: use it to understand the mathematical proof,
the intended lemma numbering, and the relationship between Lemma 1, Lemma 11,
Lemma 12, and the final Clifford+T theorem.

Then read only the Lean files relevant to your branch, as listed in the packet.
Do not take ownership of another branch's endpoints.  Treat the other branches'
public declarations as interfaces.  If another branch has a `sorry`, you may
use that theorem as an assumption unless your branch explicitly owns it.

Follow these rules:

1. Preserve public theorem names unless the packet explicitly allows changing
   them.  If you must adjust a statement, keep a wrapper under the original
   name whenever possible.
2. Keep edits scoped to your branch-owned files and any helper files explicitly
   allowed by the packet.
3. Prefer existing repo helpers over creating new abstractions.  In particular,
   check:

     TwoControl/Clifford/Definitions.lean
     TwoControl/Clifford/Statements.lean
     TwoControl/Clifford/Universal/GateSets.lean

4. Do not rewrite unrelated files, generated blueprint output, or other
   branches' work.
5. If you complete a branch endpoint that is represented in
   blueprint/src/chapters/clifford_universal.tex, update that source blueprint
   node from `\notready` to `\leanok`.
6. Do not update generated files under blueprint/print or blueprint/web unless
   explicitly asked.
7. Run the branch verification commands from the packet.  At minimum, run:

     lake build TwoControl.Clifford.Main

8. Before finishing, report:

   - which branch you completed,
   - which Lean declarations you proved or changed,
   - which files you edited,
   - the exact verification commands you ran,
   - any remaining `sorry`s in your branch-owned files,
   - any blocker or assumption that remains.

Branch completion means:

  - all branch-owned endpoints listed in the packet are proved or intentionally
    isolated as explicit assumptions if the packet allows that;
  - the repository builds with `lake build TwoControl.Clifford.Main`;
  - your changes do not require another branch to be finished except through
    the public endpoint interfaces named in the packet.

Do not stop after producing a plan.  Read, implement, prove, refactor locally
as needed, and verify.
```

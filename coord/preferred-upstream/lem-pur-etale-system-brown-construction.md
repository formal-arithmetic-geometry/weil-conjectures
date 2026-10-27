Maintenance handoff for Q138, 2026-10-24.

The repeated parent-module ownership blocker has been repaired in live sheaf-dag.
The strict-system definitions formerly in Sheaf.Paper.EtaleCoefficientSystemAdjoint
now live in Sheaf.Paper.StrictEtaleSystemInterfaces, owned by the existing definition
node def-per-strict-etale-system-interfaces. The adjoint module publicly reexports
that module. All 36 moved declarations retain their names, signatures, bodies and
original docstrings; the parent theorem signatures and proof bodies are unchanged.
The parent now cites the definition node in stmt_deps. No reverse prerequisite on
the parent is needed or permitted. The Brown import closure no longer reaches it.

Before the next dry run, fetch/rebase against current sheaf-dag. Keep the sandbox
copies of BOTH dependency node JSON files and BOTH dependency Lean modules exactly
identical to live. In particular retain the parent's newly added stmt_deps and full
record. Identical paths are omitted from the delivery diff, so the parent no longer
needs to be classified as a prerequisite owned by this delivery. These are maintenance
changes already committed to the base; do not deliver an older relocation packet.

The returned Brown repair is STILL INCOMPLETE. C6/H2's module relocation is now
handled in the base, and the saved Brown statement already quantifies over every
S. H4/H3 still requires the level-m comparison to use the recorded coefficient q
from lem-pur-etale-system-coefficient-projection / def-pur-etale-system-projection-data,
or an explicit identification with it. The saved local openProjection/properProjection
word alone does not discharge that return. Finish that mathematical statement repair,
compile, update the worker report, dry-run, and only then deliver. A passing preflight
by itself is not a repaired mathematical delivery. Do not change the item statement
or declare the return resolved merely because the gate passes.

Validation: tools/lean_file.sh one file at a time, 60-second limits: relocated
interfaces 11.3 s; adapted parent 38.6 s; existing ClopenStrictSystemSupport importer
36.2 s, all clean. Relocation has no sorry. No delivery/review/landing/dispatcher
code was changed. Old BLOCKED notes describe the previous base.

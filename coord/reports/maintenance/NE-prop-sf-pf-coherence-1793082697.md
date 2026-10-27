# prop-sf-pf-coherence maintenance, 2026-10-27

The five NE failures were reproducible stage-1 contract conflicts. The
required unchanged inherited parent statement was rejected by B2. The repair
order also requested proof-bearing nodes and new-node `lean` attachments,
whereas stage 1 requires statement-only unsplit nodes and reserves real Lean
attachments for later stages. The retained packet read the six declarations from quarantine. During the
merge-lock wait the server restored the identical source blob at the Lean
library path as well; this restoration does not itself certify a proof or
a separately extracted module. This is not a mathematical failure or a
provider error.

The server owner independently queued corrections while this maintenance
investigated. This maintenance did not edit the protected preflight/landing
tools, commit another process's work, or stop any other process. Its first
queued record-edit command was cancelled (only this maintenance's own flock
process) before it wrote anything, to avoid conflicting with the owner's
corrections.

At this record commit:

- Unchanged-statement gate correction published: True.
  tools/preflight_delivery.py last changed at b62cf53f4e68ffadc16841499f90369aff4cb342.
- Stage-1 repair-order restatement published: True.
  coord/repair-notes/prop-sf-pf-coherence.json last changed at b62cf53f4e68ffadc16841499f90369aff4cb342.

Local maintenance fixes:

- Replaced obsolete N8 stage-2 route note at
  /home/ubuntu/weil-launcher-all/batch2/route-notes/prop-sf-pf-coherence.md
  with the current NE stage-1 handoff.
- Repaired the retained sandbox at
  /home/ubuntu/weil-newtargets-sandbox/NE/prop-sf-pf-coherence:
  removed unsupported new-node `lean` records; preserved each exact theorem
  header, source declaration/module/path/line, proposed separate module and
  sorried status in `lean_candidates`; added the explicit parent
  split_report.lean_declarations mapping; copied the original arguments and
  construction handoffs into each new node's source.note. Nodes remain
  unsplit with no proof/proof_deps. Updated both packet/report generators
  and prepended the current disposition to report.md.
- All changed existing local files have adjacent
  .maint-NE-1793082697.bak backups. No mathematical statement, parent proof
  step, dependency, search record or verbatim retained argument was changed.
  The unchanged parent proof still has four steps totaling 2224 characters.

Validation: all six exact declaration allocations survive the actual
stage-1 packager, generators parse, all old statements/searches/handoffs
match their backups, and all original parent argument texts are preserved.
The first ordinary dry run still refused only inherited-statement B2 before
the owner's publication. The final dry-run evidence and exact commit ids
are recorded in the maintenance workspace REPORT.md. No Lean file was
edited, no compiler or Lake build was required, no packet was pushed, and
dispatch/failure counts were not changed.

Next worker: keep the retained six-node packet and use the current stage-1
brief and ordinary deliver.py --no-push/delivery route. Keep the parent
statement byte-for-byte unchanged and preserve every original argument.
Actual `lean.module`/`lean.declaration` bindings follow separate module
extraction and validation at the later Lean stages. Source presence alone
must not be represented as proof completion or as a validated extracted module.

If the gate correction is not published, its owner must publish the scoped
unchanged-statement warning correction; new/changed statements and all new
nodes must still receive strict form checks. Do not bypass the protected
gate, weaken statements, reset failure counts or pause dispatch.

## Final validation

The normal stage-1 dry run after publication passed (exit 0):

    OK (not pushed) deliver/NE/prop-sf-pf-coherence at 427b2ed0725: preflight passed

It saved the durable stage-1 receipt for the second-reader handoff. Nothing
was pushed. The active sandbox was left at that passing receipt; the next
worker can continue the normal stage-1 delivery path.

The protected fix is b62cf53f4e68ffadc16841499f90369aff4cb342, published by
the server owner. The initial maintenance report commit is
47d9de8d619c20782296c3947e5535ae0b1518d6. This validation record is committed
separately under the merge lock with the required identity.

Final source-tree observation: HEAD contains
lean/Sheaf/Paper/ProjectionFormulaCoherence.lean and its quarantine copy,
both at blob 13929edce12d5ca05c2586b744f63881a5c1f9f4. Exact candidate
references still identify that source. Later workers must check current
ownership and imports before moving declarations. This maintenance changed
no Lean file and ran no compiler or Lake build.

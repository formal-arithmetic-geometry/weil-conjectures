# Q10 small-etale restriction ownership maintenance

The return of immutable head b0ebbc58f14f correctly requires a definition node
owning cartesian small-etale restriction instead of citing the unrelated
quasi-coherator theorem. The retained worker packet performs that extraction,
but tools/stage2_delivery.py:953 excludes the former owner because it is no
longer in the consumer prerequisite closure. The subsequent module-owner check
at line 1234 rejects StackLqcCoherator.lean. Repeating the packet cannot resolve
this mismatch between the requested return and the accepted delivery scope.

This maintenance commit extracts the twelve existing helper declarations into
StackSmallEtaleRestriction and records def-sfb-stack-small-etale-restriction.
StackLqcCoherator publicly imports the new module, retains its other twelve
declarations, and its record inventories only those retained declarations.
Its stmt_deps now includes the actual definition owner. The theorem statement,
proof plan, helper types, bodies and names are unchanged. Extraction was checked
byte for byte, allowing only blueprint ownership tags and the replaced import.
No mathematics was written and no launcher, review or landing tool was edited.

Validation: tools/lean_file.sh, one file at a time with the default 60-second
limit, compiled the new helper in 13.0 s, the coherator sandbox copy in 43.2 s,
and the retained flat-atlas consumer in 26.2 s, all without errors or warnings.
All used a private M-Q10-flat-atlas-1792846533 build mirror. Incremental DAG
checks pass, and each moved declaration has exactly one definition-node owner.

Worker handoff: rebase on this shared-library extraction. Keep the item importing
StackSmallEtaleRestriction and citing def-sfb-stack-small-etale-restriction;
do not reintroduce a dependency on the coherator theorem. Remove the already
committed helper and coherator node/module copies from the delivery packet,
retaining their .bak files. Run the ordinary deliver2.py dry run and delivery.
The maintainer's independent review of the consumer remains outstanding.

Backups: edited existing files have sibling
.maint-Q10-flat-atlas-1792846533.bak preimages. New files have sibling .bak copies
of their initial content because they had no preimage.

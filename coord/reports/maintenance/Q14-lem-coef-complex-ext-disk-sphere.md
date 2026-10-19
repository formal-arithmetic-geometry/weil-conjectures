# Maintenance: lem-coef-complex-ext-disk-sphere (Q14)

The stage-2 worker was launched repeatedly because the target node's `stmt_deps`
omitted `lem-coef-yoneda-derived-ext-comparison`, even though the target statement
uses Yoneda Ext with Baer addition. The worker could discover the missing notion
only after starting, answer `BLOCKED`, and the dispatcher then relaunched it. The
prerequisite has since been split on the server but still has no stage-2 `lean`
record, so the target must remain queued until that statement is landed.

The target DAG record now includes the missing statement dependency. The generated
stage queue was refreshed; the target is consequently withheld by the normal
bottom-up stage-2 rule. A byte-for-byte backup of every changed pre-existing file
is kept beside it with suffix `.bak-maint-Q14-1792154064`.

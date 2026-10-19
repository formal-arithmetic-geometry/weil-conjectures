# Maintenance: lem-pur-torsion-top-trace, 2026-10-16

The stage-2 dispatch repeatedly blocked on the canonical top-degree composition
isomorphism owned by lem-pur-compact-top-localization. This is a statement
prerequisite: the transitivity clause specifies equality under that particular
isomorphism. SGA 4 XVIII 2.7.2 constructs it as the top corner of the composition
spectral sequence, and XVIII 2.9 Variance 3 expressly uses arrow (2.7.2).
The derived-functor comparison in LowerShriekComposition alone does not state
this iterated-top-cohomology comparison.

The prerequisite was present only in proof_deps. Consequently the bottom-up
stage-2 queue offered the trace while the localization node was still unsplit
and had no Lean record. Workers correctly followed the bottom-up brief and
reported the same missing declaration. This was a DAG dependency classification
error, not a compiler, permission, or theorem-proving failure.

Repair: add lem-pur-compact-top-localization to stmt_deps in the authoritative
live node and mirror it in weil-newtargets. Keep its existing proof_deps entry:
Step 1 also uses it for vanishing. The statement, proof plan, statuses and Lean
records are unchanged. The all-dependencies graph is unchanged, so this edge
cannot introduce a dependency cycle. A .bak preserves each edited node.

Refresh the side queue after the mirror. The trace is not a stage-2 task until
this genuine prerequisite has been split/reviewed and stated. The existing
stage-1 delivery deliver/NF/lem-pur-compact-top-localization remains the normal
route; do not duplicate its mathematics in a trace delivery. When stating that
prerequisite, publish its canonical corner arrow, not just an existential or
arbitrary isomorphism. Then the next trace worker can use it in transitivity.

No Lean was changed or compiled, no global build was run, no process was killed,
and no failure counter or failure-based dispatch cutoff was introduced.

Validation in the side project reproduced the premature stage-2 eligibility
from the old metadata, confirmed that the corrected node is not stage-2-open,
confirmed that localization remains stage-1-open, and confirmed in memory that
completing localization makes the trace stage-2-open again. The all-dependency
edge set is identical before/after. The generated queue was refreshed after
backing up queue.tsv, queue.md and blueprint-index.tsv; these generated files
were not included in the maintenance commit.

The stale NA stage-2 claim was retired with a non-abandonment release after the
queue correction (claim and deliveries.log backed up). No process signal was
sent. This is readiness bookkeeping, not a failure-count cutoff: the item will
return to the normal stage-2 queue when its prerequisite is stated. Dispatcher
counters and retry policy were left intact. Authoritative fix: 057345ba3d;
side mirror: ea94c7ce44.

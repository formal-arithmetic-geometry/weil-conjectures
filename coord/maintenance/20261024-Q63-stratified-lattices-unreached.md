# Q63: obsolete stratified-lattices stage-1 assignment

At 2026-10-24T09:50:09Z, under coord/.merge.lock, both node directories resolve to this
repository's dag/nodes. The parent has status split and a historical Q124
review, but stage1_completed=False because the human's 2026-10-22 keep_plan
re-split remains released. There is no side completion to promote.

The item has NO incoming dependency in the entire current DAG, including
proof-step uses and statement dependencies. Its reverse closure is itself,
and it is neither a target nor a preopen root. It is absent from Dag.dist,
Dag.dist1, stage1(), the queue, and claim.queue_stage. This is full loss of
target reach, not a repair hidden behind a completed or assumed ancestor.

History: the human's batch-scoped re-split notes were released in b15ca6d7b0d.
At 97a8704bfe683fb4d54bef92cdd9812cc29a2d25 (2026-10-22), the reviewed Q51
re-split of lem-zl-raw-heart-adic-lisse-stratification replaced its old use
of this item by lem-zl-continuous-constructible-stratified-lattices. The latter
was independently split and reviewed at 1ea9401a177, using the existing
sk-lem-stratified-lattice and embedded-lattice comparison. The old item's
only caller disappeared. The stale Q63 return/claim outlived that pruning.

nt_land_batch.py rejects items absent from stage1() before preparation. Its
notopen fallback falsely calls an existing incomplete queue node an unpromoted
side completion, and the automatic return demands another rebase. Preflight
can pass while this later eligibility gate fails. Repeated sandbox proof
edits cannot restore an obsolete dependency.

The exact packet 87603e09799760317f92ec10384c23083742389d and saved independent FIX verdict are preserved.
FIX requires dropping the duplicate realization child, citing the existing
trace node, and removing an unused encoding clause; the raw sandbox is not
an unqualified PASS. The reviewer explicitly noted the repeated false gate.
No review-service or landing-tool state is rewritten by this maintenance.

Record repair: archive the packet at refs/superseded/Q63/lem-sfb-topological-stratified-lisse-lattices/87603e09799760317f92ec10384c23083742389d with an expected-head ref
transaction; remove only its obsolete Q63 return and claim; append the reason
to the standard delivery and ledger logs. This reconciles current target
eligibility regardless of failure counts. It does not mark a proof complete,
abandon the mathematics, or impose a dispatch limit. Do not add preopen or a
target edge just to revive a pruned fragment.

The released human repair note is retained BYTE FOR BYTE and remains unresolved:
if a future target or explicit preopen assignment reaches this node, its re-split
is still owed. The historical split, Lean module, statements, sandbox, searches,
citations, reviewer fixes and review are preserved. Backups of every changed
record: /home/ubuntu/weil-maint-bak/Q63-stratified-lattices-20261024T095009Z/, relative paths with .bak suffixes; delivery-ref.bak records
the old branch. The new note has an absence backup. A temporary Git index
commits only these five scoped paths and this task's log entries, preserving
unrelated pending writes and index entries.

Protected-owner follow-up, report only: distinguish unreached incomplete
packets from actual completion in nt_land_batch.py; reconcile obsolete
returned assignments against current reach, preserving genuinely reached
released repairs and exact-head review data. The review/landing path should
not demand proof changes for an eligibility failure. There is no need for
failure cutoffs, concurrency caps, throttles, admission limits or pauses.

Next worker: no eligible stage-1 assignment exists now. Keep the archived
packet and sandbox. If authoritative reach returns, reuse the work and the
saved FIX/drop_nodes rather than the raw delivery alone, reread changed cited
statements, refresh quotations/preflight, and use normal delivery and review.
The human repair has not been resolved by maintenance. No Lean was changed,
so no compiler or build ran. No process was signalled and no protected tool,
dispatcher state, provider setting or sandbox was changed.

Unchanged record SHA-256 values:
- dag/nodes/sec-proetale-coefficients/lem-sfb-topological-stratified-lisse-lattices.json: 2b2c18e44004a150be586923007cdc10b641024ce7cf9c44b08391168cc2ac04
- coord/repair-notes/lem-sfb-topological-stratified-lisse-lattices.json: fc28c25e0b6cc4be1d3a2e91983a45805c57b6eef055a1ac29f514b072b9dc59
- local/verdicts/1/87603e09799760317f92ec10384c23083742389d.json: 5c743ffbc6a8256befa2b289d2315fa2e9190a886868aaed5d20ab0efebf799a

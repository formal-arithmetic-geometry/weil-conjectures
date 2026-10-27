# Q127: reconcile an unreached Picard-Cech assignment

At 2026-10-24T08:33:02Z, checked the live records under coord/.merge.lock. The node is
imported and unreviewed, stage1_completed=False. Both nodes_dir and queue_nodes_dir
resolve to this repository's dag/nodes. There is no separate side completion.

The entire reverse dependency closure has exactly four nodes:
det-thm-picard-cech <- det-lem-picard-cech-computes <- det-thm-picard-serre-b
<- det-thm-picard-serre-a. None is a current target or preopen root. Thus no
target reaches this item even without any completion, assumption or unsplit
cuts. Dag.dist, Dag.dist1, stage1(), and claim.queue_stage omit it; no released
stage-1 repair is owed. A stale queue/return/claim assigned this imported
blueprint fragment despite its absence from the active target graph.

Independent verdict bae26c36dfe4089a83375b43c9339483e2208aab is PASS. The failed landing is an eligibility
failure, not failed mathematics: nt_land_batch.py puts every item absent from
stage1() in notopen, then incorrectly labels an existing incomplete queue node
as a completed side copy needing promotion. Its automatic return asks for
rebasing/proof changes. Successful worker preflights (including b7b0e3d82ef)
cannot repair target reach; the held return/claim perpetuates the retries.

Preserved the approved branch at refs/superseded/Q127/det-thm-picard-cech/bae26c36dfe4089a83375b43c9339483e2208aab, deleting the old delivery ref
with an expected-head Git transaction. Removed only this item's Q127 return
and released its obsolete claim. This does not mark the node done, abandon
its mathematics, or impose any dispatch cutoff. It reconciles current target
eligibility regardless of the failure count. The four DAG nodes, independent
review, sandbox, search log and citations are retained.

Backups: /home/ubuntu/weil-maint-bak/Q127-picard-cech-20261024T083302Z/, with original relative paths and .bak suffixes;
delivery-ref.bak records the original ref. The absent new note has an absence
backup. A temporary Git index includes only these five scoped paths and this
maintenance task's own log entries. Other agents' pending appends are kept.

Protected-owner follow-up (report only): fix nt_land_batch.py's notopen
diagnostic to distinguish unreached incomplete items from genuine completion
and side/live disagreement. The review/landing path should reconcile an
obsolete exact-head packet rather than issue a proof-repair return. The
dispatcher should check authoritative eligibility for returned assignments
as well as new claims, preserving explicit released repairs. Do not add
failure cutoffs, concurrency caps, admission limits, throttles or pauses.

Next worker: there is currently no eligible stage-1 task for this item.
If a future target edge or released repair reopens it, reuse the archived PASS
delivery, reread changed dependencies, refresh citations and preflight, then
use normal delivery/review. Do not claim the Lean spectral-sequence theorem
is proved: the earlier ATTACH attempts were rejected because it has sorry.

No Lean code or mathematical split was changed. No compiler or build ran;
no process was killed; no protected tool, dispatcher state or sandbox changed.

Unchanged DAG SHA-256 values:
- dag/nodes/sec-picard-framework/det-lem-picard-cech-computes.json: 9c3d7ed2737ab4a181fc3844ebf3b25ab6f5a5dc7653967368f764f9ac0cb36e
- dag/nodes/sec-picard-framework/det-thm-picard-cech.json: 0ea7aea66c2b1503fcb6cde472e6304d2bf1d6d6d2bb776f153a703b67d99874
- dag/nodes/sec-picard-framework/det-thm-picard-serre-a.json: 0948483ec5255e16b8bbd6b8e3f11520a304f955b7ae64f720e1f1a6081734df
- dag/nodes/sec-picard-framework/det-thm-picard-serre-b.json: 5e3cc8f7898c423fb96f17f5d84ef6d97055458df3edf4c433597620fa265a3e

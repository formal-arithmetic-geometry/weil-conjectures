# NA constant-completion stale stage-1 claim reconciliation

The accepted O3 re-split is commit 468d55e4f7ab8ecc070b678e4ba86c2dfce24f21,
reviewed by NT-cc-O3-d6023006a. coord/deliveries.log records O3's completion
at 2026-10-22T09:31:38Z; coord/ledger.md records the five-node merge at
09:31. NA acquired a new claim at 09:31:48Z, ten seconds after completion.
The live parent is split, its review passes, and both repair notes are resolved.
Its seven proof steps total 2675 characters. NA's sandbox copy is unchanged;
the mandatory preflight refusal of an unchanged node is correct.

Cause: a stale queue row allowed the post-landing claim. tools/claim.py take
follows the human's 2026-10-22 rule to grant listed, unclaimed items. Once the
row disappeared, dispatch_all.py Group.server received no queue stage and
retained cached stage 1. Group.work keeps starting held stage-1 claims without
reconciling the live completion predicate. The route note still described the
old 12087-character/four-node order, which O3's accepted five-node successor
has already discharged. No further split or attachment is appropriate.

Under SHEAF_LEAD=L-only flock coord/.merge.lock, maintenance revalidated:
claim.node_finished(item, "1") true; queue_stage(item) None; both repair orders
resolved; exact NA claim owner/timestamp; no NA return or delivery branch.
Ran tools/claim.py release NA <item> with the reconciliation reason. This
closes only the obsolete assignment. It does not claim a new mathematical
delivery and does not suppress an open queue item or reset failure counts.

Changed paths:
- coord/claims/lem-weil-pbc-constant-completion-equivalence.lock removed.
- coord/deliveries.log appended by claim.py, with the explicit release reason.
- This maintenance record added.
The generated deliveries.log already contains concurrent work; the maintenance
commit includes only the claim deletion and this record. The normal maintainer
snapshot will retain the appended log entry.

Backups:
- coord/claims/lem-weil-pbc-constant-completion-equivalence.lock.maint-NA-constant-completion-1792663889.bak
- coord/deliveries.log.maint-NA-constant-completion-1792663889.bak
- This record's .bak snapshot.

The live parent SHA-256 before and after reconciliation:
ba524a4d99ff3ae1db851c0f6454ab1b3d9fe436788033f11d79c9ab91f6df93.
No DAG node, repair note, Lean source, worker sandbox, launcher code, review
service or landing tool was changed. No compiler or lake build was needed.
No process was killed, and no cap, throttle, admission limit or pause was added.

Protected launcher follow-up: dispatch_all.py's owner should reconcile held
stage-1 assignments after a successful live read establishes no queue row and
stage-1 completion. Preserve explicit returns, released stage-1 repair notes
and the human's listed-item dispatch rule; a failed read is not completion.
Carry the requested stage through claim/start races. This maintenance did not
edit the protected implementation.

Next worker: stage 1 is already accepted at 468d55e4f7a. Reuse the five landed
tasks; do not repeat the resolved four-node or five-node order or manufacture
a diff to bypass preflight. Only a genuinely new released repair order can
reopen this parent. Future Lean work is separate and follows the live queue.

# Closed duplicate: det-thm-sf-ctf-stability-direct-images

Resolved 2026-10-18T06:01:02Z by maintenance, under coord/.merge.lock.

Q18's accepted statement landed at 2026-10-18T04:54:11Z in commit
13fbce91c5 (stage-2 batch d6b9f462de0645f0abbcb2f60619509b).
NM's stale claim was created at 04:54:27Z; its duplicate packet was committed
at 05:05Z as f2906c5e7003f63294d238c75be9bc82e6d3abc6. The 05:17Z A7 return explicitly
requires retirement without another delivery. The delivery branch was already
absent when maintenance inspected it, but the NM claim and open return remained.
The dispatcher therefore repeatedly sent a closed item to the normal repair path.
The repaired sandbox preserves Q18's accepted files; ordinary delivery preflight
correctly refuses Q18 attribution and unchanged node/module for an NM delivery.
The wrapper's no-Lean withdrawal path does not apply to an accepted statement.

Maintenance archived the rejected immutable packet at
refs/superseded/NM/det-thm-sf-ctf-stability-direct-images/f2906c5e7003f63294d238c75be9bc82e6d3abc6, removed only this exact stale return,
closed NM's 04:54:27Z claim as done, and recorded the resolution in the ledger
and deliveries log. This is completion bookkeeping, not an abandonment.
The existing resolved stage-1 repair note stays resolved.

Next worker: stage 2 is complete. Do not re-deliver this packet or reattribute
Q18's statement. Any proposed correction goes through coord/HUMAN.md per A7.
A later stage-3 proof task is separate. No Lean, DAG, launcher, review, landing,
concurrency or admission code was changed by this repair.

Backups: /home/ubuntu/weil-newtargets-maint-bak/NM-det-thm-sf-ctf-stability-direct-images-2026-10-18T060102Z/ (original paths, each ending .bak).
Accepted SHA-256 values: {"dag/nodes/sec-six-functors-basics/det-thm-sf-ctf-stability-direct-images.json": "6d45b7f2878d089a9dc3ffc9c689a28baefa467fb75d5534271ae857f3748bf2", "lean/Sheaf/SixFunctors/CtfStabilityDirectImages.lean": "e5e7231915b90954194abf8711781e30a7b2f89aef0ec424f08d78f612a43b0d"}

Original retired return (historical evidence, not an open return):

## det-thm-sf-ctf-stability-direct-images (2026-10-18 05:17 UTC, branch head f2906c5e70)

L: independent stage-2 immutable head f2906c5e7003: Duplicate re-delivery after Q18's statement of this item already landed (ledger: merged deliver/Q18 at 04:54Z on 2026-10-18; NM commit at 05:05Z on top of it). Diff vs base: (1) lean.by changed Q18->NM, all other lean fields byte-identical, reviewed_lean still records Q18 (H2: misattribution, not a valid change); (2) one line 'This stage-2 statement is maintained by worker NM.' inserted mid-sentence in the theorem docstring, breaking its prose (H8); (3) the report is a copy of Q18's report, still citing 'scompile.py Q18', with a stub Second reading by NM (H11). A7: the item is closed; delete branch deliver/NM/det-thm-sf-ctf-stability-direct-images, no re-delivery needed; route any change through coord/HUMAN.md. Substance checked: statement verbatim equals the file signature, identical to the landed and reviewed Q18 version; proof only sorry; no definitions; snapshot compiles clean via nt_compile --json (54.3 s, exit 0).

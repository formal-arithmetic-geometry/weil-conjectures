# NZ partition-restriction stage transition, 2026-10-22

Item: lem-pe-partition-restriction-ind-zariski.
Maintenance run: NZ-lem-pe-partition-restriction-ind-zariski-1792667786.

## Evidence and cause

Q72's packet a99ef919c99 was accepted with a reviewer FIX in live commit
1dcb9ef9ffaba32ce25b931232a28bfe7e87cfb8, reviewed by NT-cc-Q72-a99ef919c.
coord/deliveries.log records completion at 2026-10-22T09:45:30Z.
NZ's claim records 09:45:50Z, twenty seconds later. There is no released repair
note, NZ return entry, or NZ delivery branch. The sandbox node is an unchanged
copy of the accepted split. The unchanged-item preflight refusal is correct.

The queued-item grant rule can admit a claim from a stale row after completion.
When the item then has no queue row, Group.server keeps its cached stage 1;
Group.work restarts the held claim without reconciling stage-1 completion.
The committed queue snapshots at 7a9fdc9456c, 40b85528e92 and 811122c49c9 do
not list this item. The dispatcher nevertheless repeated stage-1 attempts.
Failure counts are evidence of this stale assignment, not a reason to limit work.

During this investigation the generated queue began listing stage 2.
By 11:20:38Z the dispatcher had updated the cached stage to 2 while the
stage-1 worker started at 11:17:04Z was still finishing. Group.reap uses
s.stage(item), rather than the saved running record's stage, and therefore
logged that stage-1 ending as stage 2 and stamped note_stage=2. At 11:21:04Z it
started a real stage-2 worker with the obsolete stage-1 BLOCKED ending still
in its prompt. The existing note_for stage filter cannot reject a mistagged
note. That worker has begun reading the stage-2 node and dependencies.

## Repair and verification

Added a stage handoff clarification to coord/brief-stage2.md: an accepted split
is stage-2 input; verify current scope and repair notes, and use deliver2.py
for an unstated stage-2 assignment. An inherited stage-1 unchanged-item ending
alone is not a stage-2 blocker. This file records the accepted work and the
protected launcher follow-up.

Revalidated node_finished(item, "1") true and node_finished(item, "2") false,
queue_stage(item) == "2", no repair note, and current NZ claim ownership.
Retained that valid stage-2 claim and its active worker.
No mathematical, DAG, Lean, claim, generated-queue or launcher changes were
needed. No compiler, lake build, process kill or dispatch restriction was used.
The accepted node SHA-256 is:
f92365d49efaedc7633e34180342e98754c3ec566b5be3a073d02e84a0ac5e11.

Backups are adjacent .maint-NZ-partition-restriction-1792667786.bak files
for the standing brief and this new maintenance record. The commit contains
only the brief and this record and is made under coord/.merge.lock.

## Protected launcher follow-up

The owner of dispatch_all.py should use the saved running record's stage in
Group.reap, tag notes with that stage, and compare it with the current stage
before passing notes to a successor. Account for pending starts likewise.
On a successful live read, reconcile a held completed stage-1 assignment that
has no stage-1 queue row, return or released repair note. A live stage-2 claim
must continue with the stage-2 brief. Preserve the human's rule that listed
unclaimed work is dispatched, legitimate repair work, all failure counts and
unrestricted dispatch. Do not infer completion from a failed server read.
This protected code was not edited or restarted.

## Next worker

Stage 1 is accepted at 1dcb9ef9ffab; a99ef919c99 is the delivery packet, not
the live merge commit. Reuse the reviewed eight-step split. The current task
is stage 2: read the live node and dependency records, supply its Lean statement
under coord/brief-stage2.md, compile each file within 60 seconds, and use
deliver2.py for dry run and delivery. The old stage-1 unchanged-item BLOCKED
ending does not reopen or invalidate the split. Only a new released stage-1
repair note would authorize reopening it.

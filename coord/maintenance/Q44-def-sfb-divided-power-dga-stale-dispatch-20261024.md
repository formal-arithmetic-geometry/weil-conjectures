# Q44: completed stage-1 assignment dispatched again

NR delivered def-sfb-divided-power-dga at 0a6d7bbda7a. L merged its independently
reviewed split at 74021ff9815ef23e7b131f7ac00dbb2c8e2e6e2f on
2026-10-24 07:41:38 +08:00. Q44 claimed it at 07:41:50, while the queue still
listed the just-completed item. The current node is split, has a passing review,
and has no released stage-1 repair note. The unchanged-item preflight rejection
is correct. No mathematics or node metadata needs a repair.

The live server queue has removed this item, but the committed queue snapshot
from 711e44332932d2508fcfb69bc1336ca6e08eb0e1 (07:21:32 +08:00) still lists it.
The shared read clone refreshes committed files, not the server's uncommitted
generated queue. dispatch_all.py reads the live queue in Batch.read_queue(), but
Group.work() rechecks held stage-1 claims against the shared clone's queue with
_listed(). start_admitted() also uses that snapshot through _queue_stage().
Consequently the completed claim is repeatedly restarted with a stage-1 brief.

This maintenance commit removes only this obsolete stage-1 row from the
committed queue. All other uncommitted generated queue changes remain local;
the live queue is not rewritten. The unchanged-item gate remains intact.
The obsolete Q44 claim will be released after its active worker exits normally.
Backups are in /home/ubuntu/maintenance-backups/
Q44-def-sfb-divided-power-dga-1792802087/ (*.bak).

The lasting launcher correction belongs in protected dispatch_all.py: use the
already-fetched live server queue consistently when reconciling held claims and
choosing worker stages; account for failed/incomplete queue reads explicitly.
Do not use failure counts, delays, caps, or pauses to suppress valid work. This
file is outside the maintenance agent's edit authorization, so it was not changed.

Next worker: stage 1 is complete. Do not re-split, fabricate a metadata change,
or re-push the accepted node. Work on this item again only if a released repair
note reopens it or a genuine later-stage assignment is issued. The underlying
definition and variable-adjunction dependencies remain separate DAG work.


Cleanup verification: the shared read clone has now removed the stage-1 queue
row. Q44 worker pid 2677404 exited normally before claim cleanup. The obsolete
claim is absent after cleanup; tools/claim.py release records the completion
reason without an abandonment or a fabricated delivery. The accepted node is
unchanged. No worker or pre-existing process was killed by this maintenance session.

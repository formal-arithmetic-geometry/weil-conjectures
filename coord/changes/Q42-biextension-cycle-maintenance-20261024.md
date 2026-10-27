# Q42 biextension dependency cycle (2026-10-24)

The stage-1 candidate for lem-sfb-normal-semiabelian-biextension-extension
uses lem-sfb-normal-symmetric-cubical-extension. Its supporting chain is:

    normal-symmetric-cubical-extension
      -> symmetric-line-power-prolongation (old step 2)
      -> raynaud-generic-ample-symmetrization (step 1)
      -> semiabelian-generic-picard-class-lifting (step 2)
      -> normal-semiabelian-biextension-extension

This is a genuine circular existence argument. The live graph lacked only the
candidate's first edge, so earlier individual deliveries passed their graph
checks. Q35's review already cautioned against downstream existence inputs;
Q73 then introduced the biextension theorem as a new unsplit child. Q42's
preflight exposed the resulting loop and its worker scope forbade supporting
node edits. Failure counts and provider capacity are not the cause.

Maintenance reopens symmetric-line-power-prolongation, withdraws its old proof
and passing review, and removes only its edge to generic ample symmetrization.
Its remaining independent dependency plan is retained under keep_plan. The
statement, statement dependencies, source, searches, blueprint and Lean record
are preserved. The complete old node is in the adjacent .bak and in git history
(8443f13bab1); the released stage-1 repair note explains the independent repair.
This records an outstanding proof obligation; it does not assert that the
power-prolongation theorem has been proved independently.

The alternative symmetrization branch remains reached from
raynaud-generic-ample-power-model. Removing this edge does not prune the Q42
item or create newly unreachable nodes. The ordinary Q42 assembly can now
depend on the reopened supporting theorem without a graph cycle. The next Q42
worker should start with the retained packet's required server dry run, check
the current records, remove obsolete cycle-status prose from its report/proof
after validation, and finish its normal review/delivery. It must not resplit
this supporting item in the Q42 packet. Its own assigned repair worker follows
the released note. A passing dry run is not an independent mathematical review.

No launcher gates, admission settings, landing tools, Lean declarations, or
target statements are changed. No processes are stopped and no dispatch is
paused. No Lean compilation is needed for this JSON/repair-record correction.

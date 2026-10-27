# Superseded Q04 stage-1 assignment

Administrative repair at 2026-10-22T05:26:36Z, maintenance Q04-compact-image-localization-1792646626.

N6 delivered commit 9058b8fc911. Its independent review was accepted in
8825cb79cfde0df6a9e85076dae01f9786dfe037 at 2026-10-22T04:20:16Z,
reviewer NT-cc-N6-9058b8fc9. Q04 acquired a stale stage-1 claim at
2026-10-22T04:20:39Z. The queue subsequently removed the completed item,
but the held-claim retry path kept launching it with its remembered stage 1.
Workers correctly refused to resplit it; their unchanged reference copies
correctly failed preflight. This was a stale claim, not a mathematical failure.

Checked under coord/.merge.lock: the committed live node is split and reviewed
pass by N6, matches the working file, and has no released repair note; the item
has no queue row, Q04 return or Q04 delivery branch. Released only Q04's stale
claim through tools/claim.py. Preserved the accepted node and its five children.
The accepted item blob is 80f59f44bc9eb60bd371c135f090b86ee9e3f371.

Backups: /home/ubuntu/weil-maintenance-bak/Q04-compact-image-localization-1792646626/{claim filename,deliveries.log}.bak.
The claim backup is /home/ubuntu/weil-maintenance-bak/Q04-compact-image-localization-1792646626/lem-sf-weil-compact-image-localization-triangle.lock.bak.

Next worker: stage 1 is complete. Do not resplit, attach the still-sorried
upstream theorem, or push an unchanged copy. A later assignment needs a new
repair record or a legitimately open later stage. Failure counts remain history.

Launcher follow-up (protected file, not edited): dispatch_all.py Group.work()
must reconcile held stage-1 claims with the committed completion and live queue,
including open returns/repair notes and later-stage claims, before restarting
them. This repair changes no queue admission policy or concurrency setting.

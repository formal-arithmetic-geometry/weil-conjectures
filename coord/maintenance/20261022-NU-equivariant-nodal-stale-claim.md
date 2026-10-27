# NU equivariant nodal resolution: stale claim reconciliation

Q19's stage-2 delivery ed1e9b41d45 was independently reviewed PASS by NT-stage2-cc-ed1e9b41d and merged at 432d3cdb809c50f826ce1b634540aa214a977cb5 (2026-10-22 04:52:41 UTC). NU claimed the item at 04:53:12 UTC while the stage-2 queue still offered it. The current live queues no longer list it, but the held claim survived. Group.server reports queue stage '-' and retains the remembered stage 2; Group.work restarts the held item as new work. Repeated workers correctly refuse a duplicate push under coord/delivery-errors.md section A7. This is completed-work bookkeeping.

Under coord/.merge.lock with SHEAF_LEAD=L-only, backed up the NU claim and coord/deliveries.log, then closed only this stale claim through tools/claim.py done NU. No delivery branch, open return in any group, repair note, repairs.txt entry, rework entry, or live queue row exists for the item. The passing review and stage-2 completion were checked again inside the lock. The two landed Lean modules and node keep their hashes. No Lean compilation is needed for this coordination-only repair.

The commit includes only this record and the maintenance-owned deliveries.log line. Other groups' pending log lines and staged changes are preserved. The removed claim was untracked runtime state.

Backups on the server:
- coord/claims/lem-sfb-equivariant-nodal-smooth-pair-resolution.lock.maint-NU-nodal-1792646274.bak
- coord/deliveries.log.maint-NU-nodal-1792646274.bak

Next worker: use AlgebraicGeometry.exists_equivariant_nodal_smooth_pair_resolution in Sheaf.AlgebraicGeometry.EquivariantNodalSmoothPairResolution. Stage 2 is complete; another delivery requires an explicit reopening repair request. Stage-3 proof work is separate.

Launcher follow-up (report only; dispatch_all.py is excluded from edits): reconcile held stage-1/2 claims against live completion after they leave the queue, preserving delivery branches, open returns and released repair notes. Keep the human's rule that listed, unclaimed work is dispatched. Do not add failure-count gates, concurrency caps, throttles, admission limits, or pauses. No launcher, review, or landing tool was edited.

Verified source SHA-256 values:

- /home/ubuntu/weil-conjectures-sheaf/dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-nodal-smooth-pair-resolution.json: 81610a929e76d1da873cca4ab90ec524b88171e737634dc02de437e38327a462
- lean/Sheaf/AlgebraicGeometry/EquivariantNodalSmoothPairResolution.lean: 2480c41d8329c7d95d96613d6bbfa960cbad3733a0038bf1d6aa81c264853ec5
- lean/Sheaf/AlgebraicGeometry/SplitMarkedNodalAction.lean: 82cdffaa33e2ef7076f8a5a3eb99b435da18ae2ba7a3292722c312f10a172975

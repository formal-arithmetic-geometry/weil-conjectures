# Q70 sk-thm-sf-dual-perfect stale claim (2026-10-22)

Q120's accepted stage-1 re-split is commit
`7fdabd9a088ccd54937176aa47315d6ec13fa99a`, recorded at 07:39:39 UTC.
It added the three extracted argument nodes, retained the stage-2 binding,
and resolved the stage-1 repair note. The live split has Q120's passing
independent review. Q70's claim was created at `2026-10-22T07:41:49Z`,
after that landing. The current queue has no row for the item.

The Q70 attempts repeatedly submitted the accepted item unchanged. The
preflight correctly refused "the item's node file is unchanged". At the
maintenance trigger the dispatcher recorded 51 failures; these counts
are evidence of the loop, not a reason to stop eligible work.

Cause: `dispatch_all.py` `Group.server()` receives queue stage `-` for the
held, completed item and leaves its remembered stage `1` in place.
`Group.work()` treats the stale held claim as new work and retries it.
The 2026-10-17 route note predates Q120's accepted re-split. This is a
claim/dispatcher reconciliation fault, not a mathematical defect.

Under `coord/.merge.lock`, checked the resolved repair, passing review,
stage-1 completion, absent queue row, absent Q70 delivery branch and absent
open Q70 return. Backed up the claim and deliveries log, then ran
`tools/claim.py release Q70 sk-thm-sf-dual-perfect` with the reconciliation reason.
The accepted node, Lean module, repair note and review remain unchanged.
No worker process was killed, no Lean file was compiled, and no dispatch
limit, delay, pause or failure-count gate was added.

Backups (on the server, intentionally not staged):

- `coord/claims/sk-thm-sf-dual-perfect.lock.maint-Q70-1792676315.bak`
- `coord/deliveries.log.maint-Q70-1792676315.bak`

Preserved SHA-256 values:

- `dag/nodes/sec-six-functors/sk-thm-sf-dual-perfect.json`: `e33b86953b0309ce8c77ead4f7861c7ebc122cd412f888e61a0ef71eb4d1abc4`
- `lean/Sheaf/Paper/OrientedPerfectDuality.lean`: `97412cf71f26aab9328f7f43230123b530e52f33cf370e7625e0ebd26949d46c`
- `coord/repair-notes/sk-thm-sf-dual-perfect.json`: `90127d5685b146c25f49df74403ac2d39f50d87c04b030dfa6e2d4e71dbf66c3`

Launcher follow-up (report only; this code is protected by the maintenance
brief): reconcile held claims that have left the live queue against the
live completion record before generating new work. Keep explicit repair
returns and released repair notes eligible, and continue dispatching listed
unclaimed items as the human requires. Do not add retry limits, throttles,
admission limits or pauses. No protected launcher or landing code changed.

Next worker: stage 1 is complete. Read the current queue and repair record;
only a new explicit repair or queue assignment authorizes more stage-1 work.
Reuse Q120's accepted split. An outstanding Lean proof belongs to its own
queued work; it is not grounds to repeat this completed stage-1 delivery.

# NZ stale stage-2 claim retirement

At 2026-10-18T07:50:58Z, maintenance retired NZ's obsolete assignment for `det-lem-int-ext-continuity`.
Q48's stage-2 completion was recorded at 2026-10-18T04:04:27Z. NZ's claim
was created at 04:04:40Z; the remaining return for `b484432718e9e973800693ef136fb1542da929ec` explicitly
required retirement and prohibited another push. The dispatcher saw the held
claim and open return and repeatedly assigned a repair with no deliverable.
The unchanged packet's Q48 attribution and unchanged node/module correctly
fail delivery preflight; changing credit or a docstring cannot fix this task.

The merge-lock transaction backed up the claim, NZ returns, ledger and
deliveries log at `/home/ubuntu/weil-newtargets-retire-bak/det-lem-int-ext-continuity-20261018T075058Z` (each file ends in `.bak`), retained the returned
head at `refs/superseded/NZ/det-lem-int-ext-continuity/b484432718e9e973800693ef136fb1542da929ec`, removed only this return entry, and used `claim.py
release` with a maintenance reason to close NZ's claim. This is a superseded
assignment, with no `abandon:` entry and no stage-2 parking. Other NZ returns
are retained byte-for-byte. The node remains attributed to Q48 with its
reviewed completion, and the existing resolved stage-1 repair note is retained.

Do not deliver or reattribute this item again for this return. Stage 2 is
complete; any future work requires a new explicit repair or a stage-3 task.
No Lean file or launcher/landing/review tool was changed. The launcher could
prevent recurrence by routing a retirement-only return to record maintenance
and by rechecking reviewed stage-2 completion before dispatching old claims.
That launcher-owned change is described in the maintenance REPORT.md only.

Preserved SHA256 values:
- `/home/ubuntu/weil-newtargets/dag/nodes/sec-six-functors-basics/det-lem-int-ext-continuity.json`: `a2798b3489580775242f872e7c74fccaa59683fe81ef2f46d2a64311cff36e2c`
- `/home/ubuntu/weil-conjectures-sheaf/dag/nodes/sec-six-functors-basics/det-lem-int-ext-continuity.json`: `a2798b3489580775242f872e7c74fccaa59683fe81ef2f46d2a64311cff36e2c`
- `/home/ubuntu/weil-newtargets/lean/Sheaf/SixFunctors/IntegralExtHomContinuity.lean`: `d739797cefbdfb48590b3ff3725d21463ceaa748ed3c6dd138153359be0d1649`

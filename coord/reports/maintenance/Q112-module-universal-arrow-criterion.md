# Q112 module universal-arrow criterion: maintenance, 2026-10-17

The repeated failures were provider HTTP 429 interruptions, compounded by lost
second-reader state. They were not Lean compilation failures or ten rejected
mathematical attempts. The stage-2 writer in run 1792193047 returned READY after
the dry-run commit 8e89fad177 passed compilation and preflight. Its reader,
1792194998, ended with HTTP 429 and no last.txt. The old dispatcher returned to
`new` instead of retaining the reader role, so fresh writers repeatedly reread
and revalidated the same packet. Twelve consecutive worker logs from 1792194998
through 1792196923 ended with HTTP 429. The original five-failure maintenance
session also ended with HTTP 429. Writer 1792196979 compiled and passed another dry run.

The old Q42 delivery in coord/deliveries.log is stage 1. The item remains a valid
stage-2 obligation; that entry is not evidence its Lean statement has landed.
No Q112 return entry or stage-2 rejection was found during this investigation.

Concurrent maintenance supplied the shared tool repairs while this investigation
was running: 6fb280508f preserves second-reader handoffs and transport retries;
0abb765411 retains interrupted reader reports within the same delivery round;
a1a68055f2 installs the scoped provider retry supervisor through the Codex entry
point. New workers can resume their exact interrupted session without changing
the original budget. Already running Python dispatchers retain loaded code until
their normal restart. This maintenance did not kill or restart any process.

This Q112 change adds:

- tools/launcher/route-notes/lem-coef-module-universal-arrow-criterion.md, deployed
  to /home/ubuntu/weil-launcher-nt/route-notes/ with the same name: recover the
  saved packet, distinguish the old stage-1 delivery, revalidate, and preserve
  independent second reading.
- tools/launcher/test_dispatch_q112_recovery.py: replays the real READY → reader
  → HTTP 429 sequence, checks the retained report and reader brief, checks a
  serialized state with 10,000 failures remains eligible, and checks that a new
  returned head requires author repair. It exercises actual dispatcher methods
  with temporary files and a fake launcher; no server/model/Lean process starts.
- This maintenance report.
- tools/launcher/test_worker_transport.py: import the newly added stage-1 handoff
  helper into its isolated dispatcher fixture. The concurrent receipt change
  otherwise caused NameError in two transport tests despite working in production.

Validation: the three Q112 regressions pass against both the installed launcher
source and the server source. The shared provider supervisor's eleven regressions,
transport wrapper's eight regressions, and compiler classifier's six regressions
also passed on the server after correcting that test fixture. No Lean file was changed by this maintenance, so no
additional compilation was required. The active worker's successful compilation
and dry runs are recorded in its log; they do not replace mathematical review.

Next worker: retain the existing two Lean modules and node records in the Q112
sandbox. Start by reading report.md and validating that packet against current
main. A writer answers READY after successful validation; a separate reader must
finish source comparison, repair findings, and deliver. Never synthesize a final
answer for an interrupted worker or edit the dispatcher's live state.json.

Existing files changed by this maintenance were backed up with a .bak suffix;
new installed files also have backup snapshots. The commit uses the required
Bin Wu identity under SHEAF_LEAD=L-only and coord/.merge.lock. Unrelated work
was not staged.

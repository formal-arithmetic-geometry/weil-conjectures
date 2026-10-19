# Current handoff: prop-sf-pf-coherence, stage 2 (2026-10-20)

For the N8 stage-2 assignment, follow the stage-2 worker brief. This note
supersedes the old Q79 stage-1 maintenance handoff and the previous BLOCKED
notes about its missing sandbox. Those notes describe an obsolete route,
not an outstanding stage-1 repair or a stage-2 delivery-tool failure.

## Verified server state

The stage-1 re-split landed through Q75 on 2026-10-17 at 12:24:59 UTC in
live-project commit 697b9ab6aa7cc1deb30740a051c1223faa5f6856. The live item is
`split`, with `reviewed.result = pass`, group Q75, reviewer
`NT-cc-Q75-09de50e71`. Its three extracted lemmas landed with it:
`lem-sf-pf-open-factor-coherence`, `lem-sf-pf-compactification-pasting`, and
`lem-sf-pf-coefficient-realization-transport`. The repair record
`coord/repair-notes/prop-sf-pf-coherence.json` is resolved. Evidence is in
`coord/reports/Q75/prop-sf-pf-coherence.md` and
`coord/deliveries-newtargets.log` in the live project. The current Q79 returns
file has no return for this item. At this maintenance check, the item had no
`lean` record or `reviewed_lean` record; its stage-2 statement remains to do.

## Continue the current assignment

Use the current live node and its statement dependencies, as directed by the
stage-2 brief. Work in the authorized N8 stage-2 sandbox:
`/home/ubuntu/weil-newtargets-stage2-sandbox/N8/prop-sf-pf-coherence`.
Its retained `report.md` describes the obsolete route failures; it is not a
stage-2 packet or a new mathematical return. Preserve that history and add the
required stage-2 Worker report when the statement packet is ready.

The old Q79 sandbox is retired. Do not recreate it, restore an older rejected
split, repeat its stage-1 dry run, or use the stage-1 delivery wrapper. Stage 1
is complete for this item. The normal stage-2 brief governs searches, dependency
interfaces, statement corrections, compilation, preflight, and delivery:

- Compile each delivered Lean file with
  `python3 /home/ubuntu/weil-launcher-all/batch2/scompile.py N8 prop-sf-pf-coherence <path.lean>`.
  The wrapper uses the server single-file compiler, 60 seconds per file; no Lake build.
- Dry run the completed stage-2 packet with
  `python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py N8 prop-sf-pf-coherence --no-push`.
- Deliver with
  `python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py N8 prop-sf-pf-coherence`.

Check current server state before publishing, since another delivery can land
meanwhile. Repair concrete diagnostics under the stage-2 contract. This handoff
does not certify any Lean statement or bypass preflight or independent review.

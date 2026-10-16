# SchemeDerivedBaseChangeMap pipeline repair, 2026-10-16

The V3 return at bee6a8e503 requests a canonical-data construction repair. The
published module and rejected delivery contain no textual `sorry`. Treating it as
an ordinary proof item caused false tool refusals and repeated no-op repairs.

Evidence is retained in the launcher's old `weil-launcher/dispatch.log`:
V3 reported the zero-hole `nothing is proved` rejection at 14:08, 14:21, 15:27,
15:35, 16:09 and 16:17 on October 14 (launcher local time). Workers also reported
that the forced-adaptation rule prevented consistent downstream normalization.
Six other attempts ended without an answer; their original worker logs have been
removed, so their individual causes cannot be reconstructed. The imported counter
of 11 is not evidence of eleven failed mathematical proofs.

The old gate defect is already repaired in `weil-launcher/deliver3.py`: a matching
group return is a repair even without a `coord/repairs.txt` entry or XR reservation.
The retained source-only regressions confirm acceptance of this returned zero-hole
repair and rejection of an unrelated zero-hole delivery. No check was weakened.

The server's standing brief and stage document still required claims/forced edits
for every consumer, contradicting the October 14 rule implemented by
`stage3_delivery.check_changes` and the launcher's worker/reader briefs. They now
say explicitly that unclaimed modules can be changed like the item's module;
another group's held modules retain the strict forced-adaptation restrictions.
The return addendum gives the current scope and requires one coherent delivery.

The unified dispatcher introduced an additional retry regression: unlike the older
stage-3 dispatcher, it overwrote existing stage-3 repair sandboxes with the rejected
branch. A temporary sandbox regression reproduced overwritten Lean, node and report
content. The launcher source now seeds only an empty sandbox and includes the last
worker note in repair prompts. All six regression tests pass, including stages 1,
2 and 3 as subcases. This new regression did not cause the historical October 14
counter; it would have erased the next repair attempt under the unified dispatcher.

Launcher deployment artifacts and tests are retained in
`tools/maintenance/20261016-scheme-base-change/`. The dispatcher patch is installed
in the launcher source; it becomes active on that process's next start. The running
dispatcher and its current V3 worker were not stopped. The worker brief and route
note are read from disk on future dispatches and are already installed. No Lean
source, live sandbox, delivery branch, claim, failure count or target was edited by
maintenance. No Lean compilation was needed for these pipeline/document changes.

The next worker should read the addendum in `coord/returns/V3.md`, retain/rebase its
sandbox, use the original fixed derived-pullback counit consistently in composition,
adjunction and downstream definitions, and resolve the helper-node omission. Check
claim holders again. Report zero holes honestly; require the usual independent
reader and compile each affected file separately within 60 seconds.

Backups of every edited pre-existing file are retained alongside it with a
`scheme-base-change-20261016.bak` suffix. The maintenance work directory also retains
the test, source diffs and REPORT.md with the final server commit and validation.

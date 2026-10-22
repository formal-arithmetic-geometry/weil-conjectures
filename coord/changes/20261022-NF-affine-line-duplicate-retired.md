# NF duplicate stage-2 claim retired (2026-10-22 02:46 UTC)

`def-pur-affine-line-purity-comparison` was landed by NI at 2026-10-21T22:46:43Z
(landing commit b0742fd8f9; ledger: merged deliver/NI/def-pur-affine-line-purity-comparison).
The live lean record belongs to NI and reviewed_lean is PASS under NI.
NF's claim was acquired at 22:46:54Z, after that landing, and its duplicate
head faac82d4846 was returned at 22:53 UTC with an instruction to retire it.
No delivery branch remains. The item is absent from the current queue.

Maintenance closed only NF's stale claim and removed its resolved return from
coord/returns/NF.md. This is completion of duplicate bookkeeping, not an
abandonment, a new NF statement delivery, or a new mathematical review.
NI's node, attribution, review and Lean source retain their exact bytes.
Every pre-existing changed file has an adjacent .maint-NF-affine-line-1792637037.bak backup.

The repeated workers were trapped by contradictory deliver2.py withdrawal
checks: withdrawal requires no dictionary-valued lean record, then compares
the full node to live, whose lean record is NI's. Normal delivery instead
rejects NI attribution and unchanged files. A verified withdrawal currently
prints DELIVERED without closing a claim or return, so changing that gate
alone would not finish the bookkeeping. The worker brief also unconditionally
requires a delivery although this return explicitly forbids redelivery.
Launcher and landing tools were not modified; their needed change is detailed
in the maintenance REPORT.md. No Lean files changed or needed recompilation.

Next worker: this stage-2 item is complete. Do not reattribute or redeliver NI's
statement. A substantive objection belongs in coord/HUMAN.md. Do not add a
retry limit, admission restriction or dispatch pause for this item.

## Archived resolved return

## def-pur-affine-line-purity-comparison (2026-10-21 22:53 UTC, branch head faac82d4846)

L: independent stage-2 immutable head faac82d4846f: No-op re-delivery of an item NI already landed (ledger 22:46 'merged deliver/NI/def-pur-affine-line-purity-comparison', reviewer PASS; svc.log LAND 06:46:46, before this review started at 06:50). Diff of the snapshot against the live tree: the Lean module differs only by an added docstring sentence ('This packet records the already reviewed statement for the NF worker delivery.'), and the node record differs only by lean.by NI->NF and lean.date; statement, stmt_deps, lean.statement and reviewed_lean are identical. A7: push after the merge, item closed. H2: overwrites another group's landed lean record, misattributing it. H8: the docstring line is bookkeeping, not source content. F: the 'Second reading by NF' section checks nothing, and the report wrongly says the lean record was not altered. Correction: do not redeliver; retire NF's claim and keep NI's landed record; raise any substantive objection via coord/HUMAN.md. Nothing compiled, no file changed by the reviewer.

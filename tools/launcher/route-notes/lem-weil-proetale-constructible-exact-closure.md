## Superseded re-split resolved (maintenance, 2026-10-21)

The old 6292-character re-split request is resolved by E1's stage-3 proof landing
20261021T061009-L-1683218, commit 8a6738c4ddcde9268f7070ca43108b7f8353b8a9. The live node has a
1473-character, two-step proof citing lem-weil-pbc-proetale-constant-module-constructibility
and lem-weil-constructible-coefficient-serre; its Lean module has no proof holes.
The maintainer's 06:29 UTC return explicitly rejected the proposed helper nodes as
duplicates and said the re-split was resolved. Maintenance reconciled the repair
note, return, claim and queue with that decision and archived the rejected packet.

This item is completed for stage 1. A worker holding an older brief should reread
coord/repair-notes/lem-weil-proetale-constructible-exact-closure.json and the maintenance report
coord/reports/NP/lem-weil-proetale-constructible-exact-closure-maintenance-20261021.md.
Preserve the live proof; the two withdrawn helper nodes must not be restored to
satisfy the obsolete numerical requirement. A new defect requires a new specific
repair record. The old delivery is retained at
refs/superseded/NP/lem-weil-proetale-constructible-exact-closure/e0185ab3cae665aab1e731cdb91f252caf186a1d.

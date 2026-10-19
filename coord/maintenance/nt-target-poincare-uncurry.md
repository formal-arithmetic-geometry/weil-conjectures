# Maintenance: nt-target-poincare-uncurry

2026-10-18 06:27 UTC: NJ's stale stage-2 claim and superseded return were retired. NX's lean and reviewed_lean records and the landed module are unchanged.

NX landed at 2026-10-18T04:50:58Z, stage-2 batch 41eed0285fd54433aede36e1b05012bb, commit 1b9c5d2d89. NJ's claim still dated 04:51:10Z even though this item is absent from the queue and claim.node_finished(item, '2') is true. The dispatcher treated the return as a repair without reconciling the already completed item. Dry runs accepted changes to authorship/docstrings/lean.note, causing repeated duplicate pushes and then BLOCKED retries. The worker running when maintenance began pushed one further duplicate; its immutable head was archived before removing the branch.

Archived ref: refs/superseded/NJ/nt-target-poincare-uncurry/1b25d06b276afa3fd9696c463d81ad25ea222d64

The return entry below is resolved by record retirement, not by a new Lean delivery. NJ must push nothing more. Future stage-3 proof work is separate.

Protected-tool changes needed: dispatch_all.py must reconcile stage-2 held claims/returns with current reviewed completion; its saved-packet instruction must honor a return forbidding pushes. deliver2.py and server stage-2 preflight/landing checks must reject superseded items against the current reviewed record, while allowing an explicit authorized repair of a faulty landed statement. These protected tools were not edited.

Preserved side-project blob IDs:

- dag/nodes/sec-poincare-duality/nt-target-poincare-uncurry.json: 7d18943aa956bf833afc43dd98971d5299ad6a1c
- lean/Sheaf/Targets/PoincareUncurry.lean: df4bb183068973ae02554731256653d59be24907

## Resolved return (verbatim)

## nt-target-poincare-uncurry (2026-10-18 06:13 UTC, branch head 2e96e94755)

L: independent stage-2 immutable head 2e96e9475531: delivery-errors A6 + A7. nt-target-poincare-uncurry was merged from NX at 04:50 (ledger 39615); NJ heads ca831765ef21, 00279a410884 and eadfab8540af were already returned (ledger 39690/39740/39796). diff -rq against eadfab8540af: PoincareUncurry.lean and the node JSON are byte-identical; only coord/blueprint-index.tsv and the report differ (new section 'Returned duplicate: retirement blocked'). Against the live tree the delivery only changes Authors and lean.by NX->NJ, the docstring source lines and the lean.note wording, and keeps NX's reviewed_lean. Substance correct: the binders match every node clause, including the explicit SmoothOfRelativeDimension that upstream uncurry_poincareMap omits; the conclusion uses the published poincareMap/cupProduct/trace; d=0, identity and empty schemes allowed; one universe u; no definitions; sorry only; docstrings OK. nt_compile --json clean (exit 0, 6.1 s). Correction: NJ pushes nothing more and the branch deliver/NJ/nt-target-poincare-uncurry is deleted. Lead/maintainer: retire NJ's claim (fourth return of identical content), keep NX's landed record, and fix the preflight gap NJ reports (it accepts items the ledger records as merged).

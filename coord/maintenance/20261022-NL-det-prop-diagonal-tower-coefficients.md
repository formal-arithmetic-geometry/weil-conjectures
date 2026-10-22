# NL duplicate-claim retirement: det-prop-diagonal-tower-coefficients

At 2026-10-22T02:20:47Z, retired NL's already reviewed duplicate rather than submitting another
statement. N8's reviewed stage-2 delivery cf03d617d was landed in 3bf6ff24494;
the live item records lean.by N8, existing:false and reviewed_lean.result pass.

The return for immutable NL head 15ec878f97899c085b4d11edccb75c3e8025e35d explicitly ordered retirement,
no re-push and preservation of N8's records. It nevertheless remained an open
repair attached to NL's claim. The worker correctly restored the active sandbox
to live and archived its rejected changes, but deliver2.py only selects withdrawal
when every lean value is non-dictionary, then requires the node to equal live.
The accepted live lean record is a dictionary. This routes the correct retirement
packet into normal preflight, which rejects N8 attribution and unchanged files.

The dispatcher reads the server claim and return to schedule repairs; its failure
count is irrelevant to retirement. Both obsolete records are now closed. The
rejected head is preserved at refs/superseded/NL/det-prop-diagonal-tower-coefficients/15ec878f97899c085b4d11edccb75c3e8025e35d. Its delivery branch was already absent
at inspection. No replacement delivery was pushed and no mathematical record or
Lean source was edited. The original return is preserved below and in backups.

Changed existing paths (all backed up first): coord/returns/NL.md (only this return
removed), coord/claims/det-prop-diagonal-tower-coefficients.lock (only NL's claim removed), coord/ledger.md
(one retirement entry). Backup directory: /home/ubuntu/weil-maintenance-bak/20261022T022047Z-NL-det-prop-diagonal-tower-coefficients.

The protected launcher delivery/landing tools were left unchanged. Their needed
follow-up is a real retirement completion path that recognizes preserved live
dictionary records, checks them against live, and closes the claim/return rather
than merely printing DELIVERED. A DELIVERED answer alone does not remove a headed
server return or its claim from dispatcher eligibility.

No Lean compilation is required for this bookkeeping-only change. SHA-256 hashes
were checked before and after the transaction to preserve both nodes and modules:

- `dag/nodes/sec-six-functors-basics/det-prop-diagonal-tower-coefficients.json`: `b13d111f076ae74caa4e18fed68edbc36081b4efb26ad8f9d8b0f45e74f7e4b4`
- `dag/nodes/sec-six-functors-basics/def-sfb-diagonal-trace-models.json`: `665d847c2fe3054e92ed7865b4e1a3d4d5005328d0013eab15a0986f2c8eab57`
- `lean/Sheaf/Paper/DiagonalTowerCoefficients.lean`: `f4f145322f17bd376d47946af33229c1dde77f1ea502d5c6288f581421fe5fc3`
- `lean/Sheaf/Paper/DiagonalTowerTraceModels.lean`: `c26ba536030a0945d4f7d92936674b8b184f2ba0b35749fcd1afdfe7f383270c`

Future workers: this stage-2 item is already accepted from N8. Do not re-submit NL's
rejected packet, reattribute N8's record, add the rejected dependency edge or edit
the accepted modules. There is no remaining NL repair claim.

## Original reviewed return (closed)

## det-prop-diagonal-tower-coefficients (2026-10-21 22:39 UTC, branch head 15ec878f978)

L: independent stage-2 immutable head 15ec878f9789: A6/A7/H13: N8's delivery of this item was PASSed (cf03d617d), landed at 06:22 (ledger l.23883), and the module is authored by N8. NL's head changes only records: item lean record switched to existing:true with file dropped and by N8->NL (statement verbatim the landed one), spurious stmt_dep def-sfb-diagonal-trace-models added, N8's landed §1(B) trace-models record rewritten (by N8->NL, new note blaming an 'unknown identifier' that comes from the published build lagging live; ExactSquareOfUniverses is in live TraceModels line 304), plus one docstring line in DiagonalTowerTraceModels.lean. No mathematical fault; a FIX cannot touch stmt_deps or undo the record overwrite. Correction: retire the NL claim, do not re-push; keep N8's live records.

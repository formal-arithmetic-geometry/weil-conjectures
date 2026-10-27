# O2 primitive comparison shift: stale stage-1 claim reconciliation

Q128's stage-1 re-split was independently reviewed by NT-cc-Q128-ba2be8565
and accepted at ba639d76aaf50075e82c01bd8aba4287f1a76cc0 on 2026-10-22
at 11:05:12 UTC (coord/deliveries.log:52126; coord/ledger.md:27361).
The parent is split with a passing review; the stage-1 repair note is resolved.
Its three assembly steps total 2442 characters and cite the two landed model
nodes. O2's replacement claim was created at 11:05:26 UTC, fourteen seconds
after the accepted delivery, while a stale queue still permitted the claim.
The current queue has no row for this item.

Cause: the obsolete server claim survived queue refresh. In the protected
launcher, Group.server reports queue stage '-' for the held item and retains
the cached stage 1. Group.work schedules claimed, never-delivered items as
new work without reconciling stage-1 completion. Workers correctly followed
the live-wins rule and declined duplicate splitting. Failure counts are
historical evidence, not an eligibility rule. Historical recovered HTTP 429s
are unrelated to these substantive answers; no provider fix was attempted.

Maintenance backed up the exact claim and deliveries.log, then released only
this superseded O2 assignment with tools/claim.py release under coord/.merge.lock.
The release was not an abandonment and does not claim a mathematical delivery.
The commit contains the claim deletion, the exact O2 audit line, and this note;
unrelated pending delivery-log entries are retained in the working tree.

Validation under SHEAF_LEAD=L-only and coord/.merge.lock: stage-1 completion
is true; queue_stage is None; repair state is resolved; O2 has no item return,
delivery branch, claim or held assignment. The accepted node, Lean module and
repair-note SHA-256 values are unchanged:

- parent: 80fe394ae1a8843dd9057e6edc8e9bf4b4a1d76a0e70a9069cb02b5dec8f381b
- Lean: 6cd9aa14d3f3c158b941cbc3d11efabfdc14822b20718f304c626c7a5cfdd3f0
- repair: 9c63e794845eb4712c1219c66e9ded1f8798c260b4378fcece42a51969cb01e4

Existing-file backups are adjacent, ending
.maint-O2-primitive-comparison-stale.bak. This new note has an empty .md.bak
snapshot recording its prior absence. No DAG, Lean, brief, worker sandbox,
launcher-owned file, review service or landing tool changed. No Lean compile
or global build was required. No process was killed and no concurrency cap,
throttle, admission limit or pause was introduced.

Launcher-owner follow-up (report only): reconcile held stage-1 assignments
when a successful authoritative read establishes current-stage completion,
no current queue row, no active delivery or current return, and no released
repair order. Preserve listed-item dispatch policy and all genuinely open
or reopened work regardless of failure counts. An absent/failed queue read
alone does not establish completion. Carry the requested stage through the
claim/start race. Protected dispatch_all.py was read, not edited.

Next worker: stage 1 is accepted. Reuse lem-pur-diagram-pullback-monoidal-shift-models
and lem-pur-diagram-open-clopen-shift-models; do not manufacture a diff or
repeat this resolved split. Only a new released stage-1 repair can reopen it.
Future Lean proof work on SystemPrimitiveComparisonShift is separate and
must follow an eligible live assignment; its existing sorry is not a stage-1 failure.

# N5 obsolete claim reconciliation, 2026-10-22

Item: `lem-sfb-proper-ultrametric-scalar-extension`; dispatcher key `lem-sfb-proper-ultrametric-scalar-extension@new`.

Q139's reviewed split is live in `4708feac8a000f85d2c71fbe87d3d8e06591b55b`, recorded at 11:23:22Z in
coord/deliveries.log, with passing review NT-cc-Q139-176d00e1a. The parent
has three assembly steps and cites the two live children
lem-sfb-ultrametric-one-vector-extension and lem-sfb-bounded-extension-zorn.
The stage-1 repair note is resolved and the stage-2 Lean interface exists.
This does not assert that the Lean theorem has been proved.

N5 acquired its claim at 11:25:53Z. The original admitting queue snapshot
was not established. At maintenance time the authoritative queue no longer
lists the item, but N5 still holds it. claim.node_finished returns True for
stages 1 and 2; there is no N5 delivery branch or open return for the item.
Repeated workers correctly obeyed the live-wins rule and declined duplicate
stage-1 deliveries. Failure counts are history and do not retire work.

Protected launcher code dispatch_all.py retains the saved stage when a held
claim has no queue stage. Group.work restarts held stage-1/2 assignments
without completion reconciliation. This surviving obsolete claim caused
the repeated stale dispatch.

Under SHEAF_LEAD=L-only and coord/.merge.lock, maintenance rechecked the
authoritative completion, queue, repair, review, branch and return records,
backed up every changed existing file, and used tools/claim.py release N5
with a maintenance reconciliation reason. This commit removes that obsolete
claim, records its release and adds this note. Unrelated uncommitted log
appends are preserved; only the new release line is staged.

Backups: `local/maintenance/N5-proper-ultrametric-1792676313/coord/claims/lem-sfb-proper-ultrametric-scalar-extension.lock.bak` and
`local/maintenance/N5-proper-ultrametric-1792676313/coord/deliveries.log.bak`.
Parent SHA-256: 01abc55c0ae4912ae1e39d3c8263340f57eddd3e91e10418ff466fe07a3fe166.
Repair SHA-256: d8093241bf4a9d87d1c1c08dbe0db427977f76fe41b1124918c8572abcb49fc2.
The accepted node, child nodes and repair note are unchanged.

No Lean, mathematical statement, launcher code/state/counter, provider
handling, review service or landing tool was changed. No compiler or Lake
build was run. No process was signalled by this maintenance session. No
concurrency, admission, throttle, pause or retry restriction was introduced.

Next worker: no stage-1 split or duplicate delivery is owed for this parent.
Preserve Q139's accepted assembly and both extracted children. Follow the
normal queue for the children and later proof work. Only an explicitly
released new repair reopens this accepted stage-1 work.

Launcher-owner follow-up: dispatch_all.py is protected; before relaunching
an off-queue held stage-1/2 claim, reconcile authoritative completion for its
assigned stage, repair state, open returns and delivery branches. Preserve
listed work, released repairs and pending deliveries. Queue absence alone
does not establish completion. Make this independent of failure counts.

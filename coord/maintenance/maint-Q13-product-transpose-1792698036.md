# Q13 stage-1 stale-claim repair

Recorded 2026-10-22T19:45:13Z for `lem-pur-finite-proper-product-transpose`.

The accepted split landed at `83b9df79ee2` on 2026-10-22T06:52:01Z,
from Q119 delivery `e476ac73a08`, reviewed PASS by
`NT-cc-Q119-e476ac73a`. Its stage-1 repair is resolved. Q13 then acquired
a claim at 2026-10-22T06:52:12Z, while the landing/queue state was changing.
The dispatcher retained stage 1 in its private state and repeatedly restarted
the held claim as `@new`, even after the item disappeared from the server queue.
All 75 retained worker final answers report the accepted/superseded split or
unchanged-item rejection; the requested maintenance snapshot counted 70 failures.

The dry-run rejection is correct. The standing brief forbids re-splitting a
reviewed live split without a released stage-1 repair. No mathematical change
is required. There is no Q13 delivery branch or open return for this item.

Under the merge lock, backed up the obsolete claim and deliveries log to
`<path>.maint-Q13-product-transpose-1792698036.bak`, then released only this claim through `tools/claim.py`.
The accepted DAG node, resolved repair, Lean module, worker sandbox and failure
counters are retained. Node SHA256: `69845cf25ff78c0f85943f0cb387a75f6b56f0fb57d5c412b05ff3e07fd78a0b`.

The launcher owner should add completion reconciliation for held stage-1 claims
in `dispatch_all.py` (`Group.work`): before restarting an off-queue held item,
check the live stage-1 completion predicate, released repair and matching open
return/delivery. Retire a completed obsolete claim instead of starting another
worker. Preserve queued work and released repairs, and keep failure counts
diagnostic only. The protected launcher file was not edited by this maintenance.

A future worker must reuse Q119's accepted split. Reopen stage 1 only if a new
released repair explicitly requires it; follow that repair rather than rerun an
unchanged stage-1 delivery.

# Q04 stale stage-1 claim reconciliation

Item: `lem-cbc-strict-tower-proper-open-calculus`.

Q65 delivery `2b396c645b7` landed as `9577c1376765110b2fdd603f53ca79d3a71cd075`
at 2026-10-22T07:16:11Z with reviewer `NT-cc-Q65-2b396c645` PASS, seven new nodes,
and a resolved stage-1 repair note. Q04 acquired its claim at 07:16:50Z.
The current live queues have no row for the parent; `dag_queue.stage1_completed`
and `claim.node_finished(item, "1")` both return true. Q04 has no return or
pending delivery for it. The claim was the stale input causing repeated work.

The launcher reads held claims in `Group.server`; when `claim.queue_stage` is
absent it retains the cached stage. `Group.work` restarts held stage-1 work
without checking stage-1 completion. Its off-queue reconciliation is specific
to stage 3. Repeated workers correctly obeyed the live-wins rule and answered
BLOCKED instead of delivering Q65's reviewed work a second time.

Under `SHEAF_LEAD=L-only flock coord/.merge.lock`, released only this stale
claim using `tools/claim.py release Q04`, with an explanatory deliveries.log
entry. Original claim and deliveries.log were backed up beside their paths as
`.Q04-maint-1792658743.bak`. The node, resolved repair note, Lean module,
worker sandboxes, dispatcher state, counters, and protected tools were untouched.

For the launcher owner: reconcile held stage-1 claims against current live
completion when there is no queue row, return, delivery, or active repair;
do not fall back indefinitely to a cached stage. Keep the explicit rule that
listed work continues to dispatch and that failure counts never stop work.
This requires reviewing `dispatch_all.py`, which this maintenance task prohibits
editing; no launcher or landing tool was patched here.

There is no next stage-1 repair for this parent. Any next worker must read
current server state and avoid duplicate delivery; children and genuinely new
stage-2/3 obligations continue through their normal queues. No mathematics,
Lean compilation, Lake build, process termination, concurrency limit or pause
was part of this repair.

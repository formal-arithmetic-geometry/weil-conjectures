# N9 completed stage-1 claim reconciliation, 2026-10-22

Item: `lem-pur-finite-open-product-swap`; dispatcher key `lem-pur-finite-open-product-swap@new`.

Q117's re-split merged as `c3d6fd7a614847a6d2c2d027a1ec2c971659afaa` (delivery log 06:50:20Z), with
independent passing review NT-cc-Q117-3acba5cc0. Its stage-1 repair is resolved.
N9 acquired a claim at 06:51:03Z and continued receiving stage-1 assignments
after the item left the live queue. At maintenance time, node_finished for
stages 1 and 2 was true; queue_stage was None; N9 had neither a delivery branch
nor an open return for this item. The unchanged sandbox node correctly failed
preflight with "the item's node file is unchanged".

The dispatcher's Group.server retains its saved stage when a held claim has
no queue row. Group.work restarts held stage-1/2 claims without reconciling
their completion. This obsolete claim kept those retries active; failure
counts were diagnostic history and did not retire it.

Under SHEAF_LEAD=L-only and coord/.merge.lock, maintenance backed up the claim
and deliveries.log, then ran the existing tools/claim.py release N9 API with
a reconciliation reason. This commit removes only the obsolete claim and
adds that release event and this note. Other pending log entries are retained
in the working tree. Backups are under `local/maintenance/N9-finite-open-product-swap-1792665471` with .bak
extensions. The accepted node and repair record remain byte-identical:
node SHA-256 8d226836ca07878ae65238abd05c79add56bba44bb20beb09b1503c7f0d00deb;
repair SHA-256 a14be055a65b6145561132738d5937da7a3d0ec5f0dbae44b27a43cfb07c6e18.

No mathematical or Lean change is required. No compiler or Lake build was
run, no process was signalled, and launcher code/state/counters were not
edited. No concurrency, throttle, admission, pause or retry restriction was
introduced. A fresh stage-1 claim must be refused as completed by the normal
claim tool unless a genuine new repair reopens the item.

Next worker: preserve Q117's reviewed split and the two extracted lemmas,
lem-pur-two-open-tensor-chain-normalization and
lem-pur-supported-tensor-isomorphism-transport. Both helper nodes are now
split. Preserve the existing Sheaf.Paper.FiniteOpenProductSwap Lean binding.
Do not manufacture a node diff or repeat an unchanged stage-1 delivery.

Launcher-owner follow-up (dispatch_all.py is protected and was not edited):
reconcile off-queue held stage-1/2 claims against authoritative completion,
repair state, open returns and delivery branches before resuming them.
Preserve listed work and genuinely released repairs or pending deliveries.
This is completion reconciliation, independent of failure counts.

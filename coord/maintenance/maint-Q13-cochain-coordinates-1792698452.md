# Q13 maintenance: superseded homogeneous-coordinate stage-1 claim

The stage-1 assignment was obsolete, while the unchanged-item preflight rejection
was correct. Q144's reviewed re-split landed at 2026-10-22T11:26:07Z in
a81748c43914660f222f827e9baea498490b23c9 (reviewer NT-cc-Q144-d9a303100).
The repair note is resolved. The live parent has four assembly steps and cites
the three joint-continuous coordinate equivalence, differential and naturality
nodes, plus the derived-category definition. Preserve that accepted work.

Q13's surviving claim was acquired at 2026-10-22T11:27:38Z, 91 seconds after
landing. No intervening queue snapshot was retained to establish exactly how it
was admitted. At diagnosis it had no row in any live queue, no Q13 delivery
branch and no Q13 return. The launcher retained stage 1 when queue_stage returned
None and generated @new work from the held claim without reconciling stage-1
completion. All thirteen retained worker answers describe the superseded split
or unchanged-item rejection; state-batch2.json counted eight failures. Failure
counts were diagnostic and have not been used to suppress work.

Under the merge lock, revalidated ownership, completion, resolved repair, queue
absence, branch/return absence and node/repair hashes. Backed up the claim and
deliveries.log with suffix .maint-Q13-cochain-coordinates-1792698452.bak, then
used tools/claim.py release Q13 to remove only this completed assignment and
append its release reason. This is a completion reconciliation, not abandonment.
No node, repair, Lean source, failure history, launcher code, review or landing
tool was edited, and no concurrency limit, throttle or pause was introduced.
No Lean compilation was needed because no Lean file changed.

Node SHA256: 962b2ac8b92759345f0ee7b9aeb2f4a0f92e5db3d4e2f23eb2c00238654ff426.
Repair SHA256: 27e4e66bce3c6ac59f8c5ac5a57a5e064742461588b0f6c94812d0472e1cca6e.
The retained sandbox and shared-clone nodes had the same node hash.

Launcher-owner follow-up (protected dispatch_all.py; not edited): reconcile a
held stage-1 claim against authoritative live completion, queue presence and
the repair state before scheduling cached or pending work. Release a completed
off-queue claim only after revalidating that no released stage-1 repair, current
return or delivery still requires work. Preserve the human's queue-first rule
for listed assignments and preserve failure counts. Do not weaken preflight or
add retry cutoffs, concurrency limits or pauses.

There is no remaining stage-1 work for the next worker. Do not resubmit the
unchanged packet, invent a metadata edit, or reopen the resolved repair to pass
preflight. A fresh released repair can reopen stage 1 normally. This maintenance
does not certify the Lean theorem as proved; other stages remain separate work.
Full local report and preserved evidence:
/home/ubuntu/weil-launcher-all/maint/Q13-lem-sfb-topological-homogeneous-cochain-coordinates-1792698452/REPORT.md.

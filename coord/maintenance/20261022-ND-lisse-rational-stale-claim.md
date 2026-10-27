# ND lisse rational realization: stale assignment reconciliation

Q130's six-node stage-1 split was independently reviewed PASS by
NT-cc-Q130-8a948a714 and merged at 2f068049e421acabec31384e576dbe4f146703cb
on 2026-10-22 at 10:38:45 UTC. The stage-1 repair note is resolved.
ND acquired a claim eight seconds later, at 10:38:53 UTC, while queue data
still permitted it. The item subsequently left coord/queue.tsv, but the
claim survived. Group.server in the launcher reports queue stage '-' and
keeps remembered stage 1; Group.work treats the held claim with no branch
or return as new work without reconciling stage-1 completion. Thirteen
worker attempts then correctly refused duplicate splitting under
coord/brief-stage1.md:109, and preflight rejected the unchanged item.
Maintenance was launched with eight counted failures. Counts did not
cause or justify stopping work; there is no remaining stage-1 task here.

Under SHEAF_LEAD=L-only flock coord/.merge.lock, rechecked live completion,
Q130 PASS, resolved repair, no queue row or delivery branch, and no ND
return. Backed up the claim, deliveries.log and Q146 returns, then used
tools/claim.py release ND to close the superseded assignment. Removed only
Q146's 2026-10-17 return for c1c6617fdd66, superseded by Q12's accepted
stage-2 delivery at 0ad0306c4f31e5d89160adcd098c0b347fedf2a8 on
2026-10-21 at 16:22:46 UTC. Q146's other return entries are byte-preserved.
Both reconciliations are recorded in coord/deliveries.log. Unrelated
uncommitted delivery-log appends are excluded from this commit.

Node, Lean module and resolved repair-note SHA-256 hashes are unchanged.
No mathematical work, Lean edit, compile or global build was needed.
No launcher-owned code, review service, landing tool or brief changed.
Backups are next to the three edited/deleted existing files, with suffix
.maint-ND-1792669646.bak. Worker sandbox and retry evidence were archived
in the local maintenance directory before closing the claim.

Launcher-owner follow-up (report only; dispatch_all.py is protected):
reconcile held stage-1/2 claims that have left the live queue against
authoritative completion. Preserve active delivery branches, current
returns and released repair orders. A missing queue row alone does not
prove completion. Keep the human's rule that listed, unclaimed work is
dispatched; do not add failure-count gates, caps, throttles, limits or pauses.

The next worker should use the accepted six-node split and the existing
Sheaf.Paper.LisseRationalRealization statement suite. Re-split only if a
new released stage-1 repair explicitly reopens it. Any future stage-3
proof work on the module is separate from this closed stage-1 assignment.

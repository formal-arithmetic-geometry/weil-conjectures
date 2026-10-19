# Q32 relative-cone delivery recovery

The maintenance run recovered `lem-coef-infinity-relative-cone-equivalence`
without doing new mathematics. Server delivery branch
`deliver/Q32/lem-coef-infinity-relative-cone-equivalence` now points to
`f97001ff608e1fcd4218ce4cdec6a02dd02c5065`.

Before starting more item work, check that branch and the current node's `lean`
record. This is a repaired delivery awaiting the normal server reviewer, not a
new request to restate the theorem. Never restore returned head `6e6f58150f56`.

The recovered module and node were byte-identical to independently read,
dry-run-approved local commit `862bc0e8f0`. The recovery takes only `lean` and
`stmt_deps` from that node and preserves current server-owned metadata. It
retains the genuine Worker report and Second reading by Q32 in the commit.

The old return is already repaired: no `KanMappingRestriction` import or
`kanSlice`; the module uses upstream `rightVertexSlice` and defines the real-data
`firstVertexCoslice`. The upstream isofibration and slice nodes are included in
`stmt_deps`. No theorem statement or proof was changed in maintenance.

Fresh server validation: `tools/lean_file.sh` on the identical sandbox source
exited 0. Its target took 2.8 seconds; 46 files were checked sequentially,
each with the tool's own 60-second limit, nice 19 and two threads. Server
`tools/nt_preflight2.py Q32 lem-coef-infinity-relative-cone-equivalence` accepted
the recovery bundle. `tools/review_class.py` recognizes it as a repaired return
for CODEX review. These are compile/preflight receipts, not mathematical approval.

The repeated empty answers were fatal Codex HTTP 429 errors, including
request `a3b780e4-d5dc-4a8d-ad51-86fb8d815500` in run `1792196895`.
Before them, the author and second reader lost their 45-minute budgets to
worktree queues (276 and 266 requests ahead were logged). The second reader
had already finished its reading and passed dry-run commit `862bc0e8f0`, but
was killed waiting for another worktree for the actual push. The dispatcher
then restarted it as `repair`, removing `.check` and losing the review phase.

Concurrent maintenance committed the shared transport/reader fixes as
`6fb280508f` and `0abb765411`; provider-admission/session-resume integration is
also being maintained in the deployed launcher. Do not overwrite those sources
with a stale copy. The dispatcher PID observed during this maintenance was
2532170, started before those changes. It was left running, as required by the
no-killing-other-processes rule. New source code takes effect on its next normal
start; this item's published recovery is already visible to the current process.

Server evidence and recovery repository: `/tmp/q32-maint-1792196920/`.
Original node backup in the private repository:
`delivery-repo/dag/nodes/sec-six-functors/lem-coef-infinity-relative-cone-equivalence.json.maint-Q32-1792196920.bak`.
The original worker sandbox remains available and its running worker was not stopped.

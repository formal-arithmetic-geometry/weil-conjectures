# Q114 critical coset infimum calculus: retain the approved assignment

The repeated failure is a queue eligibility/coordination error. At inspection,
lem-trf-critical-coset-infimum-calculus was unsplit and unreviewed, and both
stage1_completed(node) and stage1_completed(queue_node(item)) were false.
nodes_dir and queue_nodes_dir resolve to this repository's dag/nodes. There is
no side completion to promote. Full reach sees the item at distance 21; cut
reach sees it at 38, but queue_dist1 and stage1() exclude it.

The shortest full route crosses sk-thm-trace-transport, which the current batch
assumes. The shortest cut route crosses withdrawn
lem-per-gabber-absolute-equivariant-modification and
lem-per-complete-local-rigidification-comparison. The item itself is neither
withdrawn, assumed nor complete. Its direct citers are
lem-trf-analytic-critical-polynomial-minimum and
lem-trf-analytic-special-coset-leading-bound.

tools/nt_land_batch.py checks stage1() before applying the delivery. Its notopen
fallback labels any incomplete queue node as an unpromoted side completion,
without establishing a completion in the project DAG. The resulting worker
instruction to rebase cannot repair this gate. The unchanged delivery is
independently approved, and the worker's dry runs pass.

Preserve exactly this explicit assignment through the supported
coord/preopen.txt retained-work roots, following the Q103 and N6 maintenance
repairs. The real stage1() simulation adds only this item and removes none
(31 to 32 at initial inspection). Retain this root after landing so the approved
new child remains reachable. No withdrawal, assumption, mathematical statement,
proof or dispatcher failure count changes.

The delivery head 9f71b8c3c505d72bb6e206d3cf81368d949dd0f9 has independent PASS
in local/verdicts/1/9f71b8c3c505d72bb6e206d3cf81368d949dd0f9.json and the
full review beside it. Replay that exact PASS and original note through unchanged
tools/nt_land.py, using its own merge lock and normal citation, review_split and
DAG validation. No new mathematical review is performed by maintenance.

Before-state backups of every existing coordination/landing-scope file are at
/home/ubuntu/weil-maint-bak/Q114-critical-coset-infimum-1792861800/, with relative
paths ending .bak, checksums in before.json and empty .bak placeholders for
absent files. The independent PASS is preserved as evidence. No Lean file,
launcher-owned file, review service, landing tool or concurrency setting changes.

Tool follow-up (report only): distinguish an incomplete item excluded from active
queue reach from actual side/live completion divergence. Report the reach cut
and maintainer-owned coordination record, rather than instructing a worker to
rebase unchanged approved content. Preserve explicitly approved assignments
through their landing handoff. Failure counts must never suppress dispatch.

Next worker: after normal landing succeeds, use the live reviewed node and landing
commit as completion evidence; do not re-split or re-push this parent for the old
refusal. Continue lem-trf-binomial-root-correction only if assigned. Preserve the
preopen root while that child work remains active. REPORT.md and after.json in
the backup directory record the final outcome. The historical review-service
receipt is retained unchanged.

Outcome (2026-10-25): reach correction committed as
1bcb3001038c476505de3a0961505bc0bcb749c3. The locked recheck added exactly the
item (32 to 33), removing none. Normal landing replay exited 0:
MERGED 247e0092978088ded6ca8086efdd2a0b673ab42c, PROMOTED files 0 collisions 0.
Both commits use Bin Wu <844524296@qq.com> as author and committer and hold
coord/.merge.lock.

Post-landing verification under the merge lock passed: parent split, reviewed
PASS, completed in both DAG views and absent from stage1(); child
lem-trf-binomial-root-correction unchanged from the approved delivery, unsplit,
with no proof, and open in stage1(). The parent's statement and dependency
interface match its original node; its proof and split-owned fields match the
approved delivery. The saved author report matches exactly. The stale return,
claim and delivery branch are absent. All 19 before-state backups passed checksum
verification. The historical independent-review receipt is unchanged. Evidence:
landing.log, landing-result.json and after.json in the backup directory.
The normal background queue refresh was requested. No Lean file changed or
compiled. Dispatcher failure counts and local worker sandbox were preserved.

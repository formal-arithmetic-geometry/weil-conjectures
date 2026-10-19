# NZ pointwise Yoneda pipeline maintenance, 2026-10-17

Item: lem-coef-infinity-pointwise-yoneda-evaluation, returned stage-2 delivery.
Returned immutable head: 79ac2a009860.
Dispatcher key: lem-coef-infinity-pointwise-yoneda-evaluation@79ac2a009.

## Cause

Seven completed repair attempts (1792195862, 1792196230, 1792196280,
1792196564, 1792196673, 1792196712, 1792196923) ended on terminal HTTP 429
Too Many Requests errors. Their final-answer files were absent, and the old
dispatcher recorded empty NOANSWER notes. The logs contain distinct request
IDs. These were interrupted worker sessions, not seven unsuccessful proofs.

There is also a valid delivery defect. The original base has only
def-cbc-enhanced-diagrams-cones in this item's stmt_deps. The stage-2 delivery
adds lem-coef-coherent-nerve-comparison and chooses the evaluator's comparison
from coherent_nerve_comparison. The dependency returns through
lem-coef-model-colimit-localization-comparison,
lem-coef-small-diagram-model-rectification, and
lem-coef-infinity-pointwise-adjoint-criterion to this item.

The dry run previously called stage2_delivery.read_delivery without the
node-local DAG validation that nt_parallel2 invokes at landing. Replaying
79ac2a009860 with the production reader gives fails=[]; applying the new
graph check to that reader's effective delta finds the exact returned cycle.
Removing only the added edge in an in-memory control yields no graph findings.
This control diagnoses the tool gap; it is not a proposed mathematical fix.

## Repair

- tools/nt_incremental2.py: extract local_findings from the existing landing
  check. Landing still runs its global before/after checks unchanged.
- tools/nt_preflight2.py: construct the effective landing delta on the current
  server DAG and invoke that same local_findings function before reporting OK.
  Preserve current metadata for existing nodes, apply only the item's owned
  fields and lean-only prerequisite repairs, and include new definition nodes.
- tools/test_nt_preflight2_graph.py: 12 regression cases cover this return path,
  acyclic infrastructure, source-based corrections, current server edges,
  stale item/dependency copies, new helpers, missing nodes, and unrelated cycles.
- tools/launcher/route-notes/lem-coef-infinity-pointwise-yoneda-evaluation.md:
  persistent handoff naming the evidence, cycle, and preserved worker repair.

Every replaced file has an adjacent .maint-NZ-1792196919.bak. No project Lean
or DAG record is edited by this maintenance change. The active worker owns its
mathematical repair and must complete its ordinary second reading and landing.

Concurrent maintenance already installed provider transport handling in
tools/launcher/worker_transport.py and dispatch_all.py (6fb280508f), and
subsequent provider-capacity work is in progress. Reuse those fixes instead of
introducing a second retry policy or imposing an item failure-count cutoff.

## Validation and handoff

The 12 regression cases pass locally and on the server. The immutable-head
replay uses the real production delivery reader and the current 17,210-node
server DAG; the original reader reports no failures, the shared graph check
reports this cycle, and its in-memory acyclic control passes.

Concurrent Q09 maintenance commit d570b4f82c reopened this item's stage 1 after
finding that its old proof reduced to lem-coef-infinity-yoneda-evaluation while
that theorem's repaired foundations depend on this pointwise item. Authoritative
live commit 92b762d1db makes the same change. The old proof and review are
archived at coord/reports/maintenance/Q09-pointwise-yoneda-before.json. The queue
now lists stage 1; the node is honestly unsplit with no proof or Lean binding.
The persistent route note retains Q09's entire independent-foundation guidance.

Worker run 1792196952 was already active on the stage-2 infrastructure repair.
Maintenance leaves its sandbox and claim intact. Preserve its statement work,
but complete and review the independent stage-1 split before landing stage 2.
Then retain the full characterization of its comparison, compile each file
through the prescribed wrapper with the 60-second limit, pass the improved
dry run, and obtain a fresh independent second reading. A JSON-only removal
of the cyclic edge while retaining the old Lean theorem choice is insufficient.

Local investigation and replay evidence:
/home/ubuntu/weil-launcher-all/maint/NZ-lem-coef-infinity-pointwise-yoneda-evaluation-1792196919/.

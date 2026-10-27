# NS: retire a pruned stage-1 coefficient-defect handoff

The failure is stale dispatch data plus an incorrect landing diagnostic. At 2026-10-24T21:10:55Z,
the item is unsplit, stage1_completed is false, and no released stage-1 repair is owed.
nodes_dir and queue_nodes_dir resolve to the same directory. It is at distance
11 in queue_dist1, but outside progress_open and Dag.stage1().
There is no side completion to promote.

The progress walk stops at written ancestor proofs, including
Sheaf.Paper.QcqsProperSerreHeartBound and
Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryVanishing (own_open=False).
The two closest paths and their per-batch classifications are recorded below.
The progress-based queue filter was introduced by e927f8276ec on 2026-10-24
17:36 UTC. The recorded source proofs landed before the 19:27 UTC return.

nt_land_batch.py puts every item absent from stage1() into notopen. When
retire_completed rejects this unsplit node, the fallback infers a side/live
disagreement merely from the existence of an incomplete queue_node. The return
then asks a sandbox worker to rebase. dispatch_all.py prioritizes returns without
the queue-eligibility check used for ordinary held work. Repeated successful
preflights cannot repair reachability; the 18 failures were evidence of this
stale handoff, not a reason to stop dispatching legitimate work.

The exact head 151073eb0bd80a2b85540a3cae2f0a2abfd43045 has an independent PASS with status returned in
local/verdicts/1/151073eb0bd80a2b85540a3cae2f0a2abfd43045.json and the accompanying review.md directory.
The review's promotion inference followed the incorrect landing diagnostic.

This record repair archives that exact packet at refs/superseded/NS/lem-sfb-supported-coefficient-topology-defect-rigidity/151073eb0bd80a2b85540a3cae2f0a2abfd43045, removes only its
headed NS return and stale NS claim, and records release without mathematical
abandonment or completion. Other return sections are byte-identical. The item,
its parent, Lean files, sandbox, searches, citations, and historical verdict
remain available. The commit uses a private index so unrelated uncommitted
delivery-log appends are preserved and excluded from this maintenance commit.
Every changed file has a .bak under /home/ubuntu/weil-maint-bak/NS-coefficient-defect-20261024T211055Z; the new note has a prior-absence
backup, and delivery-ref.bak preserves the original branch. No compiler is
needed because only administrative records change.

Protected-tool follow-up: nt_land_batch.py must distinguish completion from
loss of progress reach, and retire obsolete packets instead of returning them
for proof repairs. dispatch_all.py must reconcile returned stage-1 handoffs
against current eligibility, respecting active repairs and in-flight deliveries.
Their owners must add regression coverage for an unsplit node below a written
ancestor whose transitive audit is still open. No launcher, review-service, or
landing-tool code was edited here; no concurrency or admission policy changes.

Next worker: no stage-1 work is currently owed. If a route or released repair
makes the node eligible again, recover the archived approved split, rebase,
reread changed citations, and preflight normally. Do not mark this unsplit node
done, invent a promotion, or add dependencies to force eligibility.

## Progress evidence

```json
[
  {
    "path": [
      "lem-sfb-supported-coefficient-topology-defect-rigidity",
      "lem-sfb-supported-norm-algcl-model-rigidity-transfer",
      "lem-sfb-supported-finite-model-scalar-rigidity",
      "lem-sfb-supported-three-term-scalar-rigidity",
      "lem-sfb-closed-torsion-rigidity-serre-transfer",
      "lem-sfb-proper-wcontractible-closed-fibre-rigidity",
      "lem-sfb-qcqs-proper-serre-heart-bound"
    ],
    "classes": {
      "3": "done",
      "4": "done"
    },
    "module": "Sheaf.Paper.QcqsProperSerreHeartBound",
    "own_open": false
  },
  {
    "path": [
      "lem-sfb-supported-coefficient-topology-defect-rigidity",
      "lem-sfb-supported-norm-algcl-model-rigidity-transfer",
      "lem-sfb-supported-finite-model-scalar-rigidity",
      "lem-sfb-supported-three-term-scalar-rigidity",
      "lem-sfb-closed-torsion-rigidity-serre-transfer",
      "lem-sfb-proper-wcontractible-closed-fibre-rigidity",
      "lem-sfb-proper-constructible-closed-exchange-heart",
      "lem-sfb-qcqs-proper-constructible-closed-base-change",
      "lem-sfb-qcqs-proper-open-boundary-vanishing"
    ],
    "classes": {
      "3": "done",
      "4": "done",
      "5": "done"
    },
    "module": "Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryVanishing",
    "own_open": false
  }
]
```

## Retained source hashes

```json
{
  "dag/nodes/sec-six-functors-basics/lem-sfb-supported-coefficient-topology-defect-rigidity.json": "bdd6c03888c4633f802790915a5114e992701cf1d7b8d943c1745f66b7031191",
  "dag/nodes/sec-six-functors-basics/lem-sfb-supported-norm-algcl-model-rigidity-transfer.json": "db8edfa4e8fbe6d16305c05905b98a8051808da7a7353f7f26cc5317850672aa",
  "lean/Sheaf/AlgebraicGeometry/QcqsProperOpenBoundaryVanishing.lean": "c63a277dabfd86e8f76dc5162826a1cba1ec985158e256833c68f54c4b202ee5",
  "lean/Sheaf/Paper/QcqsProperSerreHeartBound.lean": "42315b80dfae440afffeabd22ea95fbbb3eba7e3459d22d46ef19b51166c1d8e"
}
```

## Removed stale return

## lem-sfb-supported-coefficient-topology-defect-rigidity (2026-10-24 19:27 UTC, branch head 151073eb0bd)

L: approved by the reader, but the landing refused it: NOT MERGED lem-sfb-supported-coefficient-topology-defect-rigidity: lem-sfb-supported-coefficient-topology-defect-rigidity: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.


# Q02 maintenance: dg derived Quillen calculus

2026-10-16. Item: `lem-coef-dg-derived-quillen-calculus`.

The repeated BLOCKED responses came from incomplete statement dependencies.
The statement needs enhanced localization, mapping complexes and coherent
transformation interfaces. The localization and dg model mapping-comparison
nodes were listed only in proof_deps and have no Lean binding. The two listed
statement prerequisites gave only ordinary derived categories and mates, so
the bottom-up queue incorrectly offered this consumer. Q05's stage-1 delivery
d8d06994e8 is not a landed stage-2 declaration.

The side queue reads the authoritative DAG at
`/home/ubuntu/weil-conjectures-sheaf/dag/nodes` through SHEAF_DAG. As documented
in coord/dag-sync.md, a side-only record edit cannot fix queue eligibility and
can be overwritten. Added both existing prerequisites to stmt_deps under the
authoritative merge lock in commit `a6aeac60b1399df539bea9711af3b6e86d396623`, then made the same correction
in the side project under its merge lock. Held the stage-2 promotion guard
across these steps. Regenerated queue.tsv, queue.md and blueprint-index.tsv.
Author and committer: Bin Wu <844524296@qq.com>; SHEAF_LEAD=L-only.

Only stmt_deps changes in the node. The mathematical statement, proof,
proof_deps, reviewed split and Lean bindings are preserved. Both edges were
already proof edges, so the union dependency graph and its two pre-existing
cycles are unchanged. No Lean source or published artifact changed; no Lean
compile or lake build was run. Changed existing files have sibling backups
ending `.maint-Q02-1792140693.bak`; the report is new.

Validation used the actual production graph and queue: consumer admitted
before repair, excluded after repair, still excluded after only localization
is supplied in memory, re-admitted after both interfaces are supplied in
memory. No simulated binding was written. Regenerated queue excludes the
consumer and leaves its prerequisites to the normal stage-1/2 path.

Operational follow-up: release Q02's stale claim after its worker exits
naturally. The dispatcher retries already held items even after queue
eligibility changes. Do not abandon or permanently park this item, reset
failure counters, kill workers, or relax the bottom-up rule.

Next worker: when the queue re-offers this node, read the current recorded
declarations of `lem-coef-enhanced-localization-universal` and
`lem-coef-dg-model-mapping-comparison`, including signatures and docstrings,
and import their owning modules. Old sandbox reports are historical.
Do not replace the required enhancement by ordinary DerivedCategory, invent a
convention/Lean binding for admission, or redeclare those genuine DAG nodes
in the consumer delivery. Resume the ordinary stage-2 statement, 60-second
per-file compilation, delivery dry-run and independent second reading.


## Operational resolution (2026-10-16, 09:04 UTC)

The background synchronizer retired the obsolete Q02 claim at 09:01:32 UTC;
coord/ledger.md records that retirement. The dispatcher subsequently stopped
its own worker at 09:04:29 UTC because the claim was gone. Maintenance sent no
signals and made no manual claim change: the release observer found the claim
already absent. No active worker or claim remains, and the item is absent
from the production queue. Both corrected node copies survived the real sync.
Failure history remains intact (tries 6, blocked 5, no give-up entry).

The last worker left an unfinished sandbox draft at
lean/Sheaf/Paper/DGDerivedQuillenCalculus.lean. It is preserved; maintenance did
not compile, endorse or deliver it. A future worker must compare every notion
in that draft with the genuine prerequisite interfaces before reusing it.
The worker handoff in the launcher's route-notes is automatically included
when this item becomes eligible again.

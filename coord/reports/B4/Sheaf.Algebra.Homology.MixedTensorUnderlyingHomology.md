## What changed

Withdraw the unused duplicate `Sheaf.Algebra.Homology.MixedTensorUnderlyingHomology`
using `deleted.txt`. Attach `new-lem-pc-mixed-tensor-underlying-homology` to the
existing, fully proved public theorem in
`WeilConjectures.Algebra.Homology.MixedTensorUnderlyingHomology`. Its signature,
proof, scalar compatibility, generator naturality and universe are identical.
Remove the public Sheaf composition helper from the node declaration inventory:
its source counterpart is private and its source consumer already uses `import all`.
No upstream source file changes; no consumer adaptation is needed.

Validation: `lcompile.py --all` compiled read-only sandbox copies of the retained
source module and both source consumers, followed by an import/axiom probe.
The consumers compiled in 8.4 and 8.8 seconds; the probe compiled in 1.9 seconds.
`#print axioms` for the retained main theorem and private composition helper
reported exactly `propext`, `Classical.choice` and `Quot.sound`.

Change record: `coord/changes/B4-retire-mixed-tensor-underlying-homology.md`.

## Proved and sorry left

Actual starting holes: zero. Holes closed: zero. Holes added: zero. Split off: zero.
No sorry remains in the withdrawn file, and no new theorem is introduced.
The retained `RingTensorCohomology.exists_mixedTensorUnderlyingHomology` is already
fully proved, as is its private source composition helper. This is duplicate
retirement and DAG repair, not newly proved mathematical progress.

## No longer needed

Pruned module: `Sheaf.Algebra.Homology.MixedTensorUnderlyingHomology`, including
its duplicate definitions, private helpers, public main theorem and public
`RingTensorCohomology.mapHomologyIso_hom_comp`. Its six imports leave that empty
module. Their source counterparts remain needed by the unchanged source proof;
no dependency node or source module is claimed as pruned. No imports are removed
from any consumer. The node and its proof dependencies remain, now attached to
the source theorem. The unit realization has no statement or proof-step attachment
to this node, and the retained source proof is identical, so no unit route changes.

## Where the brief, the DAG or earlier work was wrong

The item is already proved with zero holes and is no longer imported. The stale
DAG attachment points to a duplicate Sheaf module even though its source counterpart
is present and both source consumers already import the source. The two files
differ only in copyright/header formatting and the helper's visibility. Keep the
source boundary intact and withdraw only the Sheaf duplicate. The existing twin
retirement list had deferred this module because of a pending consumer landing;
current whole-library searches find zero remaining Sheaf importers.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

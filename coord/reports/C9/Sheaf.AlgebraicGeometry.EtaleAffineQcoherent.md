## What changed

Retired the unused Sheaf.AlgebraicGeometry.EtaleAffineQcoherent module, as assigned
by coord/queue.tsv and coord/retire-items.tsv. The adopted source module
WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherent already proves the arbitrary
positive-degree theorem. Its specialization at n + 1 proves the removed successor
wrapper. Reattached lem-sc-etale-affine-qcoherent-succ to the source theorem and
recorded that specialization in its proof. No source-library files were changed.

Change record: coord/changes/retire-etale-affine-qcoherent-C9.md.

## Proved and sorry left

Original holes: 0. Holes closed: 0. Holes added: 0. Split off: 0.
There are no remaining sorry declarations in this delivery.
The removed declarations were AlgebraicGeometry.Etale.etale_affine_qcoherent_succ
and the duplicate AlgebraicGeometry.Etale.etale_affine_qcoherent.
The source positive-degree theorem is preserved. A scratch compilation verifies
both its successor specialization and its use with the removed wrapper's signature.
The remote compile passed in 5.4 seconds; #print axioms reports only propext,
Classical.choice, and Quot.sound for the preserved source theorem.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.EtaleAffineQcoherent.
No module imports it; whole-library searches also found no external references
to either removed declaration. There are no consumer adaptations.

The retirement removes the item's two public imports:
WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance and
WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf;
and its three proof imports:
WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift,
WeilConjectures.AlgebraicGeometry.EtaleULiftInjectiveResolution, and
WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation.
These dependencies remain needed by the preserved source proof; this delivery
claims no pruning of those modules or their nodes. No DAG node is deleted.
The unit sk-prop-h2 and its realized route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with holes or an assigned repair.
The actual queue classifies this zero-hole item as retire, with zero consumers.
The Sheaf successor wrapper is absent upstream, but is an immediate specialization
of the source positive-degree theorem, so that difference does not require keeping
the duplicate module. The DAG formerly attached to the unused wrapper now attaches
to that source theorem without changing its mathematical statement.

Mathlib searches via msearch.py found no relevant exact theorem: LeanFinder returned
unrelated affine-limit and formally-etale cotangent results; Loogle reported that
Sheaf.H was unknown; grep returned no Mathlib hit. Local library search found the
adopted theorem, so no new mathematics or node was needed.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

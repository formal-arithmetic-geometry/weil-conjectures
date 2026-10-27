## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/NeighbourhoodGeometry.lean`
from the quarantine path recorded in `coord/rework.tsv`, retaining all five declarations.
Repaired the four references to the removed `Scheme.smallStrictHenselizationDiagram`
inside the proof of `StrictLocalNeighbourhoodGeometry.smallModelFirst`: the canonical
comparison now uses `Scheme.strictHenselizationDiagram`, exactly as its definition in
`WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension` and the proved
`Scheme.smallStrictHenselizationColimitIso_toBase` do. The source diagram in the
coprojection identity is the full affine-neighbourhood diagram; its representative
whiskering is `Scheme.strictHenselizationAffineDiagram`.

The repaired module compiled cleanly through lcompile.py (11.1 seconds). An unchanged
quarantined direct consumer, `StrictLocalSmallModel.EtaleInjectiveSectionsComparison`,
also compiled cleanly against it (14.4 seconds); that verification copy is not delivered.
The definitions, signatures, public imports and docstrings are byte-for-byte unchanged.
This is a proof-only compatibility repair, so no definition/interface change record or
consumer adaptation is necessary.

Reviewed the node `lem-weil-pbc-strict-local-small-model-geometry-transport`, its three
proof dependencies, their current Lean declarations, and unit `sk-prop-h2`. Its existing
three-step proof still describes the implementation: pullback isomorphism, cone transport,
and the inverse final-colimit coprojection identity after applying Spec. No DAG field
needs changing. The source is Stacks Tag 03Q9, the first proof paragraph of
`theorem-higher-direct-images` in `literature/stacks-project/etale-cohomology.tex`.
Loogle and LeanFinder both recovered `Functor.Final.ι_colimitIso_inv`; msearch grep
located it in Mathlib/CategoryTheory/Limits/Final.lean:359. The existing proof already
uses that shortest generic route. No extra geometric hypotheses are introduced.

## Proved and sorry left

This assigned compatibility repair starts with zero holes and ends with zero holes.
Holes closed: none (0). Holes added: none (0). Split off: none (0).

All five declarations remain complete: `AlgebraicGeometry.Etale.strictLocalSmallModelPullbackIso`,
`AlgebraicGeometry.Etale.StrictLocalNeighbourhoodGeometry.smallModelLegs`,
`AlgebraicGeometry.Etale.StrictLocalNeighbourhoodGeometry.smallModelIsLimit`,
`AlgebraicGeometry.Etale.StrictLocalNeighbourhoodGeometry.smallModelOver`, and
`AlgebraicGeometry.Etale.StrictLocalNeighbourhoodGeometry.smallModelFirst`.
Every declaration retains node `lem-weil-pbc-strict-local-small-model-geometry-transport`.
No sorry remains in the delivered module; no new module is added.

## No longer needed

None. Both existing public imports remain necessary for the geometry definitions and
canonical comparison. No node, module, dependency or unit step is pruned or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The quarantine compile error in rework row 75 is reproducible from the archived proof:
it names a removed diagram. The current full diagram is `Scheme.strictHenselizationDiagram`;
the small diagram remains `Scheme.strictHenselizationAffineDiagram`. Replacing the stale
references restores the existing canonical coprojection argument, without changing any
mathematical statement or construction. The item is a genuine zero-hole repair rather
than a new proof or a decomposition. No other brief or DAG error was found.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

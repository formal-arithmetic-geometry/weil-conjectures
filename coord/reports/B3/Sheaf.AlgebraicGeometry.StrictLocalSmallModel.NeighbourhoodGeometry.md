## What changed

Restored the assigned quarantined module
`Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry`, preserving all five
public declarations, signatures, definitions and imports. In the proof of
`AlgebraicGeometry.Etale.StrictLocalNeighbourhoodGeometry.smallModelFirst`, replaced the
four references to the removed upstream name `Scheme.smallStrictHenselizationDiagram`
with its current name `Scheme.strictHenselizationDiagram`. The current upstream
`smallStrictHenselizationColimitIso` is defined by precisely the same final-functor colimit
comparison for this diagram, so the existing inverse-coprojection argument applies.

The restored module compiled through `lcompile.py` with exit code 0 in 10.3 seconds and
no Lean warnings. This is a proof repair only; no definition or statement changes, consumer
adaptations, new nodes or change records are required. The existing node and its three
proof steps still describe the argument exactly.

## Proved and sorry left

The archived module had zero `sorry`s; the repaired module has zero `sorry`s. Holes closed:
0 of 0. Holes added: 0. Split off: 0.

The proofs of `AlgebraicGeometry.Etale.StrictLocalNeighbourhoodGeometry.smallModelOver`
and `AlgebraicGeometry.Etale.StrictLocalNeighbourhoodGeometry.smallModelFirst` are complete.
The constructions `AlgebraicGeometry.Etale.strictLocalSmallModelPullbackIso`,
`AlgebraicGeometry.Etale.StrictLocalNeighbourhoodGeometry.smallModelLegs` and
`AlgebraicGeometry.Etale.StrictLocalNeighbourhoodGeometry.smallModelIsLimit` remain
unchanged and compile. All realize node
`lem-weil-pbc-strict-local-small-model-geometry-transport`.

## No longer needed

None. Both public imports and all stated dependencies are retained. The quarantined
module is restored, not withdrawn; its existing Lean attachment and downstream geometric
and cohomological uses are preserved. No DAG or module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The upstream sync removed the old diagram name used in four lines of the archived proof.
The current `WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension` defines the
canonical colimit comparison using `strictHenselizationDiagram`; the repaired proof now
uses that same diagram. The rework record's unknown-constant error is thereby repaired.
This assignment is a zero-hole compile repair, not a fresh proof decomposition.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

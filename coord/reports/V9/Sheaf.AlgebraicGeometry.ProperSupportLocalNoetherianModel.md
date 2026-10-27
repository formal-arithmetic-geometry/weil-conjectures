## What changed

Restored lean/Sheaf/AlgebraicGeometry/ProperSupportLocalNoetherianModel.lean from its
quarantine archive. Redirected the public DerivedPullback import and the private
DerivedPullbackComposition import from the withdrawn Sheaf modules to their actual
WeilConjectures owners. The existing theorem signature, docstring and complete proof
are verbatim. Server compilation succeeded in 25.1 seconds with no errors or warnings.

Change record: coord/changes/V9-ProperSupportLocalNoetherianModel-restoration.md.

## Proved and sorry left

AlgebraicGeometry.properSupport_local_noetherian_model is restored with its complete
proof from affine restriction, Noetherian approximation, cartesian tensor comparison,
perfect-implies-quasi-coherent, and composition of derived pullbacks. This is an assigned
quarantine repair with zero existing holes: 0 holes closed, 0 holes added, 0 split off,
0 holes left. No new theorem or definition is introduced.

## No longer needed

Removed imports of Sheaf.AlgebraicGeometry.DerivedPullback and
Sheaf.AlgebraicGeometry.DerivedPullbackComposition, which are withdrawn empty modules;
the corresponding declarations are imported from their adopted owners instead.
No mathematical dependency, DAG node or nonempty module is pruned. All five stated
proof dependencies and the unit route remain needed and unchanged.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because it was quarantined after the global build failed;
its absence does not withdraw its theorem. The preserved source has zero sorrys and
uses pre-migration import paths. The repair restores it with current owner imports.
There is no current numbered V9 return for this item. Its existing node attachment and
proof route already describe the restored theorem correctly, so no node edit is needed.
The sole quarantined parent still calls the theorem with exactly its existing signature;
no consumer adaptation or target statement change is necessary.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Restored Sheaf.AlgebraicGeometry.CounitStalkConditionFromLocalizedComparison from
its quarantine assignment as a public re-export of its adopted upstream twin.
The archive mixed old Sheaf definitions with upstream proof imports and failed
with a duplicate BaseDerivedTensorCohomologyModel._sizeOf_inst declaration.
The canonical upstream module already proves the identical public theorem, so
re-exporting it removes that mixed environment and the duplicate implementation.

Repointed lem-pc-counit-stalk-condition-from-localized-comparison's lean record to
AlgebraicGeometry.SingleComplexBaseChange.counit_stalkCondition_of_localizedComparison
in the upstream file, with existing=true. The node's statement and all proof
steps and dependencies are preserved. The historical module path remains usable;
no file is withdrawn and no upstream file is changed.

Change record: coord/changes/G4-counit-stalk-canonical-upstream-reexport.md.
The import-direction check permits the new import. The restored module compiles.
A scratch theorem with the archived full signature compiles by exact application
of the re-exported theorem. Its axiom check reports only propext, Classical.choice
and Quot.sound. The archived and upstream theorem signatures are textually equal.

## Proved and sorry left

This is an assigned zero-hole sync repair: 0 of 0 local sorries closed, 0 added,
0 split off, 0 remaining. The public theorem
AlgebraicGeometry.SingleComplexBaseChange.counit_stalkCondition_of_localizedComparison
is already proved upstream, with only the three permitted axioms, and is now
available through the restored historical module path. The archived private
resolution_counit_isIso helper was also proved and is superseded by the upstream
private helper. No proof or definition is replaced by sorry.

## No longer needed

Removed the archived direct imports of
Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition,
Sheaf.Algebra.Homology.KFlatResolution,
WeilConjectures.AlgebraicGeometry.LocalizedComparisonQuasiIsoSquare, and
WeilConjectures.AlgebraicGeometry.StalkComparisonCoordinateInvariance from the shim.
They are replaced by the public import of
WeilConjectures.AlgebraicGeometry.CounitStalkConditionFromLocalizedComparison.
The canonical implementation still uses the resolution, quasi-isomorphism square
and coordinate-invariance route. No mathematical dependency node is pruned,
no module is withdrawn, and neither quarantined parent is declared unnecessary.
The unit route remains unchanged.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined sync repair with no local sorry, rather than a new
proof obligation. The required theorem is already in the adopted source library.
Restoring the archive unchanged reproduces the duplicate-declaration import error.
The correct repair reuses that proved theorem and its coherent upstream definition
environment, while retaining the node and its dependencies.

The source-only live downstream query returns zero consumers because both direct
parents, RelativelyFlatDerivedBaseChangeComplex and StandardFlatSingleBaseChangeMono,
are also quarantined. Their archive imports and DAG dependencies were checked;
this delivery does not withdraw them or erase the archive. Their old definition
environments need their own assigned sync repairs.

The two archived consumers were also compiled as unchanged scratch files.
RelativelyFlatDerivedBaseChangeComplex fails importing the two derivedPullback
copies; StandardFlatSingleBaseChangeMono fails importing the two
BaseDerivedTensorCohomologyModel copies. These are independent quarantined-parent
repairs, not successful consumer checks. A further compiled-cache check imports
the upstream RelativelyFlatDerivedBaseChangeComplex alone successfully, but loading
that cached parent together with the restored shim exposes a derivedPullback
Sheaf/upstream clash. Its current source imports the upstream theorem already;
the published cached parent's wider definition environment is not coherent with
the canonical module loaded separately. No live source imports the restored shim,
and this packet does not claim to repair either parent's wider environment.
The standalone shim and full-signature application do compile successfully.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

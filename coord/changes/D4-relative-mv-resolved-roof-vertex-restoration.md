# AlgebraicGeometry.relativeMV_resolved_roof_vertex_normalization

## Reason

Restore the complete module preserved in the quarantine path recorded in
`coord/rework.tsv`. The source file is absent from the library after the failed
cluster restore. Its public theorem and all eight private helpers already have
complete proofs. The local irreducibility entry for `derivedPullback` is
redundant with its current `irreducible_def` declaration, as in the repaired
mate-comparison dependency.

## Old

```lean
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  derivedPullback DerivedCategory.Qh
```

The complete original source is archived at
`quarantine/Sheaf/AlgebraicGeometry/RelativeMVResolvedRoofVertexNormalization.lean`.

## New

```lean
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh RingedSpace.moduleDirectImage
```

Restore the module with this redundant local entry removed and keep the
ordinary direct-image functors folded. Concrete row and functor comparisons are expensive to elaborate. A proved
private helper `row_roof_vertices_isIso` performs the three-vertex isomorphism
composition for arbitrary row functors. It takes the three vertex proofs
explicitly, avoiding instance search through the concrete row projections.
A second proved private helper `combine_vertex_comparisons` inserts the three
denominator witnesses into the six comparison witnesses from the existing
mate-comparison theorem, without repeated concrete type comparisons.
The public proof reduces its statement aliases once with projection reduction
disabled, binds only the aliases it uses and applies these helpers.
The complete repaired module compiled in 39.7 seconds with no errors or warnings.
A first preflight timed out before the witness-assembly helper was added;
the single-file limit remains 60 seconds.
Its public theorem statement, docstring, proof route, all six imports and the
eight archived private helper signatures are unchanged. No definition or
target changes.

## Users

`tools/downstream.py` reports the item as unknown because it is quarantined.
Direct searches of both library roots and the quarantine archive find the sole
archived direct importer below. It applies the identical theorem with the same
arguments and consumes the same six comparison isomorphisms, three denominator
isomorphism proofs and three equations. No consumer adaptation is needed.
The archive is preserved, with all dependencies retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofVertexNormalization | D4 | Restore complete proof. |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRowRoofComparisons | unclaimed in shared snapshot (quarantined) | Same public signature; no adaptation. |

## Status

landed 20261021T002930-L-1579642 2026-10-21 (merge of deliver/D4/Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofVertexNormalization)

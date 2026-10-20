# AlgebraicGeometry.Scheme.derived_fiber_open_factorization

## Reason

Restore the quarantined module assigned by coord/rework.tsv. Its proof imported
private helpers from the retired Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde,
which is now an empty module. The canonical upstream module still proves both
pullbackOpenIso and pullbackCompIso with the required signatures. Import its
implementation with Lean's existing `import all` mechanism. No source-library
file is modified.

## Old

```lean
import all Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
```

The complete previous module is preserved at
quarantine/Sheaf/AlgebraicGeometry/DerivedFiberOpenFactorization.lean.

## New

```lean
import all WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
```

All other source text is identical to the quarantined module, including every
public import, declaration, definition body, attribute and proof. The four
public declarations and their types are preserved:
AlgebraicGeometry.Scheme.openResiduePoint,
AlgebraicGeometry.Scheme.localDerivedFiberCohomologyFunctor,
AlgebraicGeometry.Scheme.localDerivedFiberCohomologyFunctor_eq, and
AlgebraicGeometry.Scheme.derived_fiber_open_factorization.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedFiberOpenFactorization | N4 | Restored and compiled; private proof import repaired. |
| Sheaf.AlgebraicGeometry.AffinePerfectResidueModelNaturality | unclaimed | Quarantined direct importer; public interface and definition bodies unchanged; no adaptation required by this repair. |
| Sheaf.AlgebraicGeometry.AffineResidueModelNaturality | unclaimed | Quarantined consumer through AffinePerfectResidueModelNaturality; theorem type and local functor unchanged. |

The consumer inventory includes quarantined files: AffinePerfectResidueModelNaturality
imports this module and uses openResiduePoint and the local fibre functor;
AffineResidueModelNaturality applies derived_fiber_open_factorization. Their
existing independent quarantine errors are outside this repair. There are no
live importers of the absent module. No target statement or definition meaning
changes, and no consumer edit is forced.

## Status

landed 20261020T162316-L-3588809 2026-10-20 (merge of deliver/N4/Sheaf.AlgebraicGeometry.DerivedFiberOpenFactorization)

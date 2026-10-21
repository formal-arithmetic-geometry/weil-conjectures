# AlgebraicGeometry.exists_flat_derived_structure_unit

## Reason

Restore the quarantined module listed in `coord/rework.tsv`. The archived module's
public signature uses `derivedPullback`, but `Sheaf.AlgebraicGeometry.DerivedPullback`
is now a withdrawn compatibility stub. The adopted source implementation must be
publicly imported so that the theorem's public type elaborates and downstream modules
see the same declaration.

## Old

The quarantined module had this public import:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

The restored module uses the adopted implementation:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

The theorem signature, declaration visibility, docstring, and proof body are otherwise
unchanged from the quarantined source. This preserves the existing statement exactly;
only the source of the already-defined `derivedPullback` API is migrated.

## Users

The item module itself is restored from quarantine and compiles with the migrated
public import. Its parent node retains the existing explicit canonical-map proof and
fibre-properties dependency. The restored `FlatDerivedStructureUnitProperties` module
already makes the same source import migration in its landed restoration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit | D3 | Restored with the required public source import; theorem signature and proof unchanged. |
| Sheaf.AlgebraicGeometry.FlatDerivedStructureUnitProperties | C1 | Existing landed restoration uses the same source `DerivedPullback` import; no adaptation. |

## Status

landed 20261021T011015-L-2028095 2026-10-21 (merge of deliver/D3/Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit)

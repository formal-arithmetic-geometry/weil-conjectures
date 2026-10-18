# AlgebraicGeometry.ProEtale.isIso_compactSupportComparisonUnit

## Reason

Prove the canonical fixed-module comparison unit directly from the existing
injective-acyclicity criterion. The realized-coefficient derived comparison theorem
is unnecessary for this proof. Its reexport was used by one direct consumer, which
now imports that interface explicitly. All declaration signatures and definitions
are unchanged, including the specified unit and the asIso construction.

## Old

In `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
```lean
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
```
In `Sheaf.Paper.PurityComparisonUnitInjectiveModel`:
```lean
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
```

## New

In `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
```lean
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
```
In `Sheaf.Paper.PurityComparisonUnitInjectiveModel`:
```lean
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit | E4 | Proof completed; unused realized-coefficient public import removed. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | Compiles unchanged. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Compiles unchanged. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Compiles unchanged. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Compiles unchanged. |
| Sheaf.Paper.BoundedSiteAdjunctionTranspose | unclaimed | Compiles unchanged. |
| Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange | F7 | Transitive consumer; no changed declarations or definitions. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Compiles unchanged. |
| Sheaf.Paper.ExceptionalMateSiteComparison | unclaimed | Compiles unchanged. |
| Sheaf.Paper.GlobalFiniteLevelCompactSupportBaseChange | unclaimed | Compiles unchanged. |
| Sheaf.Paper.PurityComparisonUnitInjectiveModel | unclaimed | Add direct public import for definitions in its existing public signature. Original fails with unknown identifiers finiteCoefficientDirectImage, finiteCoefficientDerivedComparisonAdjunction and finiteCoefficientComparisonAdjunction. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Compiles unchanged. |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | Compiles unchanged. |

No target statement or definition changes meaning. The comparison unit remains the
unit of derivedComparisonAdjunctionPlus, and compactSupportComparisonUnit remains
asIso of that same natural transformation. No target statement review is reopened.

## Status

landed 20261018T145057-L-3637724 2026-10-18 (merge of deliver/E4/Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit)

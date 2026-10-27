# Module.localization_commutes_with_embedded_point_removal

## Reason

The completed proof uses only Mathlib and the two maximality hypotheses in the
unchanged theorem signature. It does not use the existence theorem in
Sheaf.RingTheory.RemoveEmbeddedPrimes. Replace that public import by the Mathlib
imports that the public statement actually needs. This removes the unnecessary
proof dependency without changing any declaration signature or definition.

## Old

```lean
public import Mathlib.RingTheory.Localization.Module
public import Sheaf.RingTheory.RemoveEmbeddedPrimes
```

## New

```lean
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.LocalAtTarget
import Mathlib.RingTheory.Localization.Submodule
```

## Users

`tools/downstream.py Sheaf.RingTheory.LocalizationEmbeddedPoints` lists the ten
modules below. With `--uses Module.localization_commutes_with_embedded_point_removal`,
it finds no direct theorem use outside the item itself. The sole direct importer,
Sheaf.AlgebraicGeometry.RemoveEmbeddedPoints, already independently imports
Sheaf.RingTheory.RemoveEmbeddedPrimes, so its visible environment retains the
removed dependency and all downstream environments retain it as well. Nothing
needs adaptation and no statement changes meaning. No targets change type.
The local coord/claims snapshot records T1 for RemoveEmbeddedPoints and X8 for
SnapperNumericalPolynomial; the other consumer modules have no holder record.
Neither held module is modified.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.LocalizationEmbeddedPoints | P1 | proved theorem; import replacement above |
| Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality | unclaimed in snapshot | unchanged; inherited dependency retained |
| Sheaf.AlgebraicGeometry.GenericRankLeadingDegree | unclaimed in snapshot | unchanged; inherited dependency retained |
| Sheaf.AlgebraicGeometry.HilbertUniformSectionBound | unclaimed in snapshot | unchanged; inherited dependency retained |
| Sheaf.AlgebraicGeometry.IntersectionEffectiveCartier | unclaimed in snapshot | unchanged; inherited dependency retained |
| Sheaf.AlgebraicGeometry.IntersectionNumber | unclaimed in snapshot | unchanged; inherited dependency retained |
| Sheaf.AlgebraicGeometry.NumericalPolynomialLeadingTerm | unclaimed in snapshot | unchanged; inherited dependency retained |
| Sheaf.AlgebraicGeometry.RemoveEmbeddedPoints | T1 | unchanged; explicit independent import retained |
| Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial | X8 | unchanged; inherited dependency retained |
| Sheaf.AlgebraicGeometry.TenCanonicalHilbertParameter | unclaimed in snapshot | unchanged; inherited dependency retained |
| Sheaf.AlgebraicGeometry.TopDimensionalReductionIntersection | unclaimed in snapshot | unchanged; inherited dependency retained |

## Status

landed 20261023T123927-L-1296647 2026-10-23 (merge of deliver/P1/Sheaf.RingTheory.LocalizationEmbeddedPoints)

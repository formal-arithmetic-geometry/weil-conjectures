# LowerStarAcyclic proof-import visibility

## Reason

These dependencies are used only by proof terms. Stage 3 requires ordinary imports for
proof dependencies. The previous explanation citing only the line-length limit was inadequate.
`CohomologyContinuity` remains public because `Etale.sectionsFunctor` appears in a signature.
No statement, definition, declaration visibility or target type is changed.

## Old

```lean
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Injective
```

## New

```lean
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Injective
```

## Users

The source-only downstream check lists these seven direct importers. Their public theorem
and definition signatures are unchanged; each proof dependency remains imported for elaboration
inside the item. The shared global build verifies downstream re-elaboration.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison` | unclaimed | Declaration signatures and bodies remain available; proof dependencies are no longer re-exported. No adaptation delivered. |
| `Sheaf.AlgebraicGeometry.ComparisonDirectImage` | unclaimed | Declaration signatures and bodies remain available; proof dependencies are no longer re-exported. No adaptation delivered. |
| `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel` | unclaimed | Declaration signatures and bodies remain available; proof dependencies are no longer re-exported. No adaptation delivered. |
| `WeilConjectures` | unclaimed | Declaration signatures and bodies remain available; proof dependencies are no longer re-exported. No adaptation delivered. |
| `WeilConjectures.SixFunctors.ProEtale.Comparison` | unclaimed | Declaration signatures and bodies remain available; proof dependencies are no longer re-exported. No adaptation delivered. |
| `WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal` | unclaimed | Declaration signatures and bodies remain available; proof dependencies are no longer re-exported. No adaptation delivered. |
| `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf` | unclaimed | Declaration signatures and bodies remain available; proof dependencies are no longer re-exported. No adaptation delivered. |

## Status

landed 20261016T054838-L-158175 2026-10-16 (merge of deliver/V2/WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic)

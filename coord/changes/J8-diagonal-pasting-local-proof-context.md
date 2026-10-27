# PurityFiniteSetting.DiagonalPasting local proof context

## Reason

Complete thirteen existing helper proofs without changing any declaration signature,
public import, visibility, definition body or target meaning. Local elaboration controls
avoid expanding the large concrete monoidal structures. Local simp attributes provide
pullback projection equations; none of these commands is exported. No other module is edited.

## Old

```lean
set_option autoImplicit false
```

No local monoidal instance priorities, irreducibility attributes or pullback simp
attributes were set by this file.

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
  HomologicalComplex.monoidalCategory
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
```

Within the existing DiagonalPasting namespace:

```lean
attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc
```

These select the existing canonical monoidal instances and keep their large
implementations folded. All old definition texts and public signatures are preserved.
The added proof-only import is Sheaf.SixFunctors.SmoothDualityBaseChangeCompat.
The report lists the unused proof imports removed. No exported instance, attribute,
notation or option changes, and no consumer needs adaptation.

## Users

All transitive importers returned by tools/downstream.py are listed below. Holders
come from the current shared claim snapshot; none is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineDifferenceTowerFactorization | E3 | Identical public interface and data; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | Identical public interface and data; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Identical public interface and data; no adaptation. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed | Identical public interface and data; no adaptation. |
| Sheaf.Paper.DoubleDiagonalSectionIdentifications | unclaimed | Identical public interface and data; no adaptation. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed | Identical public interface and data; no adaptation. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed | Identical public interface and data; no adaptation. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed | Identical public interface and data; no adaptation. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed | Identical public interface and data; no adaptation. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed | Identical public interface and data; no adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | T2 | Identical public interface and data; no adaptation. |

## Status

landed 20261025T163757-L-827831 2026-10-25 (merge of deliver/J8/Sheaf.Paper.PurityDiagonalSectionPasting)

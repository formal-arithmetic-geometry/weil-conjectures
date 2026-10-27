# AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedTensorComparison

## Reason

The published internal-module tensor comparison is the same unique normalized map.
Using its canonical construction directly keeps its large choice term folded in the
projection mate. The existing leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison
and the already proved generic summand/counit normalization verify the same predicate.
The uniqueness theorem then identifies this map with the former selected witness.
No tensor map, counit mate, or target assertion changes mathematically. The changed
construction and all target statements depending on it require independent review.

## Old

```lean
noncomputable def moduleObjectDerivedTensorComparison :
    Functor.leftDerivedDerivedTensor (upperStar Λ f) ⟶
      Functor.derivedTensorLeftDerived (upperStar Λ f) :=
  (existsUnique_moduleObjectDerivedTensorComparison Λ f).exists.choose
```

## New

```lean
noncomputable def moduleObjectDerivedTensorComparison :
    Functor.leftDerivedDerivedTensor (upperStar Λ f) ⟶
      Functor.derivedTensorLeftDerived (upperStar Λ f) :=
  leftDerivedUpperStarTensor Λ f
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalLocalizingProjectionFormula | P5 | Same normalized map, now constructed directly; mate equals the adopted projectionMap. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed in shared claim records | Its IsIso witness explicitly refers to the old choice. Replace only that proof by (moduleObjectDerivedTensorComparison_normalized Λ f).2. |

These are exactly the textual users returned by tools/downstream.py with
--uses moduleObjectDerivedTensorComparison. The four direct importers are
RationalP1DiagonalTensor, ProEtaleProjectionExchangeMaps, RationalP1UnitCounit and
TateTwistedProjection. All retain their public signatures and mathematical meanings.
Compile and forced-adaptation results are recorded in report.md.

## Status

landed 20261025T143725-L-1079163 2026-10-25 (merge of deliver/P5/Sheaf.Paper.RationalLocalizingProjectionFormula)

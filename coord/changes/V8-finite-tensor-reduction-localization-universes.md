# WeilConjectures.PurityFiniteSetting.FiniteTensorLineComparisonNormalized

## Reason

Restore the quarantined module for the build-2026-10-25 rework assignment.
The recorded compiler failure at the restriction single-complex comparison is
`failed to solve universe constraint: u + 2 =?= u + 1`. The unconstrained
localization universes of `mapDerivedCategorySingleFunctor` were inferred at the
larger level. The fixed scalar adjunction uses localization Hom universes `u + 1`.
Specify those two universes and the outer singleFunctor localization universe
explicitly. Also pin sfFixedRestriction’s two coefficient-lift universes at u + 1,
as its inferred signature otherwise permits independent lifts. Keep the same comparison, inverse,
object, adjunction Hom equivalence and heterogeneous equality.

## Old

```lean
def FiniteTensorLineComparisonNormalized (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) (c : P.FiniteTensorLineMaps m hm hmn T)
    (b : ∀ r : ℤ, (P.finiteTensorReduction m hm hmn T).obj (P.finiteTensorFixedLine T r) ≅
      (P.finiteReductionSetting m hm).finiteTensorFixedLine T r) : Prop :=
  ∀ r : ℤ,
    HEq ((P.finiteTensorAdjunction m hm hmn T).homEquiv _ _ (b r).hom)
    ((_root_.DerivedCategory.singleFunctor _ 0).map
      (P.finiteTensorFixedLineMap m hm hmn T c r) ≫
    ((sfFixedRestriction T (P.finiteReductionRingHom m hm hmn)).mapDerivedCategorySingleFunctor
      0).inv.app
      ((sfIntrinsicModuleEquivalence T (P.finiteReductionSetting m hm).Ring).inverse.obj
        ((P.finiteReductionSetting m hm).finiteTensorLine T r)))
```

## New

```lean
def FiniteTensorLineComparisonNormalized (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) (c : P.FiniteTensorLineMaps m hm hmn T)
    (b : ∀ r : ℤ, (P.finiteTensorReduction m hm hmn T).obj (P.finiteTensorFixedLine T r) ≅
      (P.finiteReductionSetting m hm).finiteTensorFixedLine T r) : Prop :=
  ∀ r : ℤ,
    HEq ((P.finiteTensorAdjunction m hm hmn T).homEquiv _ _ (b r).hom)
    ((_root_.DerivedCategory.singleFunctor.{u + 1} _ 0).map
      (P.finiteTensorFixedLineMap m hm hmn T c r) ≫
    (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1}
      (sfFixedRestriction.{u, u + 1, u + 1} T
        (P.finiteReductionRingHom m hm hmn)) 0).inv.app
      ((sfIntrinsicModuleEquivalence T (P.finiteReductionSetting m hm).Ring).inverse.obj
        ((P.finiteReductionSetting m hm).finiteTensorLine T r)))
```

## Users

`tools/downstream.py --allow-missing` reports zero live consumers because the
whole family is quarantined. The archived import graph and DAG citations instead
give the following eight consumers. None requires an adaptation: the definition's
binders and meaning are unchanged. In particular, the signed-reduction existence
statement still applies the same predicate to the semilinear and derived maps.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteFirstRootChart | unclaimed | Unchanged; public signatures and constructions retained. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | Unchanged; public signatures and constructions retained. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Unchanged; public signatures and constructions retained. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | Unchanged; public signatures and constructions retained. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed | Unchanged; public signatures and constructions retained. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Unchanged; public signatures and constructions retained. |
| Sheaf.Paper.FiniteTensorPresentationReduction | unclaimed | Unchanged; public signatures and constructions retained. |
| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed | Unchanged; normalization predicate is used with the same arguments. |

This is an elaboration repair of the recorded definition, not a change to the
mathematical statement or the unit route. No target signature or target meaning
changes. The node's Lean attachment and all statement dependencies are retained.

## Status

landed 20261025T050940-L-3884574 2026-10-25 (merge of deliver/V8/Sheaf.Paper.FiniteTensorReductionData)

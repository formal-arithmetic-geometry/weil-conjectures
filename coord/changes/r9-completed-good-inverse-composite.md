# WeilConjectures.FrobeniusCoefficientTwists.completedToOrdinaryOnGood

## Reason

Express the normalized inverse comparison as the symmetry of a single composite
isomorphism. Its inverse law then follows from that composite's `hom_inv_id`,
without repeatedly unfolding the concrete sheaf data in three cancellation steps.
This is definitionally the same isomorphism: `Iso.trans_symm` is `rfl`, and applying
it twice to the explicitly left-associated forward composite gives the previous
right-associated composite of inverse isomorphisms. The double symmetry also
reduces definitionally. The signature and the representative normalization are
unchanged.

## Old

```lean
def completedToOrdinaryOnGood (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (C : CochainComplex (integralTowerModules l E Y) ℤ)
    (hC : integralOperationsGoodComplex l E Y C)
    (hK : sfIntegralConstructible l E Y
      (DerivedCategory.Q.obj C)) :
    (integralDerivedPullback l E g).obj
        (DerivedCategory.Q.obj C) ≅
      (PurCompactSupport.pull (PurCompactSupport.completed l E)
        g).obj (DerivedCategory.Q.obj C) :=
  (integralDerivedPullbackComparison l E g).app ⟨C, hC⟩ ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map ((pullbackAugmentation l E g).app C))
      (pullbackAugmentation_isIso l E g C hC hK)).symm ≪≫
    ((modulePull l E g).mapDerivedCategoryFactors.app C).symm
```

## New

```lean
def completedToOrdinaryOnGood (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (C : CochainComplex (integralTowerModules l E Y) ℤ)
    (hC : integralOperationsGoodComplex l E Y C)
    (hK : sfIntegralConstructible l E Y
      (DerivedCategory.Q.obj C)) :
    (integralDerivedPullback l E g).obj
        (DerivedCategory.Q.obj C) ≅
      (PurCompactSupport.pull (PurCompactSupport.completed l E)
        g).obj (DerivedCategory.Q.obj C) :=
  ((((modulePull l E g).mapDerivedCategoryFactors.app C ≪≫
      @asIso _ _ _ _ (DerivedCategory.Q.map ((pullbackAugmentation l E g).app C))
        (pullbackAugmentation_isIso l E g C hC hK)) ≪≫
      ((integralDerivedPullbackComparison l E g).app ⟨C, hC⟩).symm)).symm
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | R9 | Uses the inverse law of the same composite in its generic normalized descent proof. |
| Sheaf.Paper.CanonicalTateComparisons | P7 | Its reductionSquareSource uses the same isomorphism; no adaptation is needed because the definitions are equal by reduction. |

The library-wide search finds no other direct consumer. No consumer module is
adapted, and no target statement changes.

## Status

landed 20261026T070903-L-3686575 2026-10-26 (merge of deliver/R9/Sheaf.Paper.FrobeniusCoefficientTwistsCanonical)

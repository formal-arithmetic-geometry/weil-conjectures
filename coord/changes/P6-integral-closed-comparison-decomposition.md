# Closed integral comparison decomposition

## Reason

Make the two remaining map-normalization steps independently provable while assembling
the existing ClosedSupport theorem from its declared dependencies. Restore the quarantined
source and preserve every existing public declaration.

## Old

The two new theorem declarations were absent. The existing closedSupportNormalization
statement and ClosedSupport structure are unchanged.

## New

Two new theorem signatures in new modules:

```lean
theorem closedReduction_isIso {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (C : SfOrdinaryIntegralComparison l E i) :
    IsIso (closedReduction l E i C)

theorem closedAlpha_normalization {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (C : SfOrdinaryIntegralComparison l E i)
    [IsIso (closedReduction l E i C)] :
    NatTrans.CommShift (closedAlpha l E i C) ℤ ∧
    ∀ (K : sfIntegralConstructibleCategory l E Z) (n : ℕ),
      (closedAlpha l E i C).app K ≫
        (coefficientSequenceProjection l E X n).app
          ((FrobeniusExchange.systemDirect l E i).obj
            ((FrobeniusExchange.reduction l E Z).obj K.obj)) =
      (sfCompletedDerivedDirectImage l E i).map
        (((FrobeniusExchange.models l E).system Z).adjunction.unit.app K.obj ≫
          (coefficientSequenceProjection l E Z n).app
            ((FrobeniusExchange.reduction l E Z).obj K.obj)) ≫
        (sfDerivedRestrictionComparison l E i n).hom.app
          ((coefficientSequenceDerivedEvaluation l E Z n).obj
            ((FrobeniusExchange.reduction l E Z).obj K.obj)) ≫
        (scalarReductionDerivedRestriction l E X n).map
          ((directEvaluationIso l E i n).inv.app
            ((FrobeniusExchange.reduction l E Z).obj K.obj))
```

Both use exactly the existing comparison maps. Each is strictly a part of the old proof;
neither restates the existence of ClosedSupport. Existing statements and definitions,
including all target statements, retain their meaning.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralClosedSupportNormalization | P6 | Proof imports and applies both new theorems. Existing interface unchanged. |

No existing module imported either previously absent module. Existing consumers of the
item require no adaptation because its public interface is unchanged.

## Status

landed 20261027T180728-L-3895944 2026-10-27 (merge of deliver/P6/Sheaf.Paper.IntegralClosedSupportNormalization)

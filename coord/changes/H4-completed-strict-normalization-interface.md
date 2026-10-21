# AlgebraicGeometry.Scheme.CbcStrictExchangeNormalization

## Reason

The fully instantiated normalization equation caused kernel checking of the final
existence proof to exceed the 60-second single-file limit. Factoring that equation
as CategoryTheory.DerivedPairExchangeNormalization preserves its literal meaning
and keeps specialization small. The prototype main module compiles in 26.9 seconds;
the new definition compiles in 3.0 seconds. No proof is moved to a different module:
the new module contains only the generic predicate, and the descent proof stays
in CompletedStrictOpenExchange.

This is an implementation repair, not a statement correction. No binder,
hypothesis, conclusion or existing declaration signature changes. The unchanged
statement of def-cbc-completed-strict-open-exchange still displays the same equation;
the generic predicate is recorded among the proof-interface dependencies.

## Old

```lean
def CbcStrictExchangeNormalization
    (b : cbcStrictOpen d j sq.isOpenImmersion ⋙ completedTowerPullback g d ≅
      completedTowerPullback gU d ⋙ cbcStrictOpen d j' sq.isOpenImmersion') : Prop :=
  ∀ P : CochainComplex (pbcTowers U (pbcAdicCompletion U d)) ℤ,
    (∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := pbcAdicCompletion U d)
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules U (pbcAdicCompletion U d))).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj P)) →
    HEq
      (b.inv.app (DerivedCategory.Q.obj P) ≫
      (completedTowerPullback g d).map
        ((cbcStrictOpenModule d j sq.isOpenImmersion).mapDerivedCategoryFactors.hom.app P) ≫
      completedTowerPullbackComplexCounit g d
        (((cbcStrictOpenModule d j sq.isOpenImmersion).mapHomologicalComplex (.up ℤ)).obj P))
      ((cbcStrictOpen d j' sq.isOpenImmersion').map
      (completedTowerPullbackComplexCounit gU d P) ≫
      (cbcStrictOpenModule d j' sq.isOpenImmersion').mapDerivedCategoryFactors.hom.app
        (((completedTowerModulePullback gU d).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        (((cbcStrictInverseModule d sq).mapHomologicalComplex (.up ℤ)).app P))
```

## New

```lean
def CbcStrictExchangeNormalization
    (b : cbcStrictOpen d j sq.isOpenImmersion ⋙ completedTowerPullback g d ≅
      completedTowerPullback gU d ⋙ cbcStrictOpen d j' sq.isOpenImmersion') : Prop :=
  DerivedPairExchangeNormalization
    (completedTowerModulePullback gU d) (completedTowerModulePullback g d)
    (cbcStrictOpenModule d j sq.isOpenImmersion)
    (cbcStrictOpenModule d j' sq.isOpenImmersion')
    (completedTowerPullback gU d) (completedTowerPullback g d)
    (completedTowerPullbackCounit gU d) (completedTowerPullbackCounit g d)
    (cbcStrictInverseModule d sq)
    (fun P ↦ ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := pbcAdicCompletion U d)
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules U (pbcAdicCompletion U d))).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj P)) b
```

The new generic predicate expands to the original equation, including the same
HEq, resolving class, ordinary inverse map, comparison factors and universal
counits. The meaning check uses the old equation verbatim and Iff.rfl (compiled in 46.9 seconds). The unchanged direct consumer compiled
in 13.3 seconds. The identity check covers
an arbitrary square and arbitrary candidate isomorphism, including empty opens,
unbounded complexes and an empty resolving class in the generic predicate.

## Users

`tools/downstream.py Sheaf.Paper.CompletedStrictOpenExchange --uses
CbcStrictExchangeNormalization` lists the following transitive consumers and the
two modules that mention the predicate. No other module is modified. Definitional
identity preserves their statements. Targets depending on the definition are
submitted for renewed statement review, with the identity check as evidence.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.CompletedFiniteComparisonModels | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.CompletedFiniteExchangeCoordinates | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.CompletedOpenFiniteEtaleOrigins | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.CompletedRingStrictFiniteExchange | M3 | Only direct external use; unchanged original compiled against the new interface in 13.3 seconds. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.NormalizedFiniteComparisonExistence | R4 | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.RationalRealizationScalarCoherence | G7 | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Transitive consumer; definitional identity preserves every statement and chosen normalized exchange. |
| Sheaf.Paper.CompletedStrictOpenExchange | H4 | Specializes the generic predicate; declaration signature and representative equation unchanged. |

## Status

landed 20261021T233724-L-853970 2026-10-21 (merge of deliver/H4/Sheaf.Paper.CompletedStrictOpenExchange)

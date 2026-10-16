# Cached derived coefficient and square interfaces

## Reason

Specializing threeStepComparison at the concrete derived functors elaborated, but its
kernel check normalized exposed square projections and exhausted diagnostic heartbeat
budgets and the 60-second file limit. Keep the same internal coefficient adjunction,
internal square and etale square behind no_expose, with their unchanged signatures
and bodies. The item now compiles in about twelve seconds using the existing
categorical comparison and proved restriction formulas. No timer, kernel check,
axiom policy or proof assumption changes.

These three definitions have exactly their old mathematical values. No target statement
or mathematical construction changes, so semantic target review is not reopened.
Both provider modules and both adapted consumers are unclaimed in the shared
coordination snapshot; the item is held by B2.

## Old

```lean
@[irreducible] noncomputable def coefficientDerivedAdjunction :
    coefficientDerivedUpperStar Λ h ⊣ coefficientDerivedLowerStar Λ h :=
  derivedUpperStarLowerStarAdjunction Λ h

@[irreducible] noncomputable def coefficientAmbientSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    coefficientDerivedUpperStar Λ g ⋙
        coefficientDerivedUpperStar Λ f' ≅
      coefficientDerivedUpperStar Λ f ⋙
        coefficientDerivedUpperStar Λ g' :=
  (leftDerivedUpperStarComp Λ f' g).symm ≪≫
    eqToIso (by rw [← sq.w]) ≪≫
    leftDerivedUpperStarComp Λ g' f

noncomputable def Etale.pullbackSquareComparison (sq : CommSq g' f' f g) :
    D+((g)^*[A]) ⋙ D+((f')^*[A]) ≅ D+((f)^*[A]) ⋙ D+((g')^*[A]) :=
  (Etale.upperStarPlusComp A f' g).symm ≪≫
    eqToIso (by rw [← sq.w]) ≪≫ Etale.upperStarPlusComp A g' f
```

## New

```lean
@[no_expose, irreducible] noncomputable def coefficientDerivedAdjunction :
    coefficientDerivedUpperStar Λ h ⊣ coefficientDerivedLowerStar Λ h :=
  derivedUpperStarLowerStarAdjunction Λ h

@[no_expose, irreducible] noncomputable def coefficientAmbientSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    coefficientDerivedUpperStar Λ g ⋙
        coefficientDerivedUpperStar Λ f' ≅
      coefficientDerivedUpperStar Λ f ⋙
        coefficientDerivedUpperStar Λ g' :=
  (leftDerivedUpperStarComp Λ f' g).symm ≪≫
    eqToIso (by rw [← sq.w]) ≪≫
    leftDerivedUpperStarComp Λ g' f

@[no_expose]
noncomputable def Etale.pullbackSquareComparison (sq : CommSq g' f' f g) :
    D+((g)^*[A]) ⋙ D+((f')^*[A]) ≅ D+((f)^*[A]) ⋙ D+((g')^*[A]) :=
  (Etale.upperStarPlusComp A f' g).symm ≪≫
    eqToIso (by rw [← sq.w]) ≪≫ Etale.upperStarPlusComp A g' f
```

The provider modules add three proved equations: coefficientDerivedAdjunction_eq,
coefficientAmbientSquare_app and Etale.pullbackSquareComparison_def. The first and
third unfold the same construction and prove reflexivity inside its defining module.
The square component formula uses the existing Mathlib NatIso.trans_app theorem
twice before projecting morphisms, avoiding normalization of concrete derived
functors. The returned duplicate private triple_app helper is removed. These are APIs for the existing data, with no new mathematical obligation.

The two consumer proof adaptations replace explicit square unfolding with
pullbackSquareComparison_def. Every existing signature, hypothesis, universe,
visibility and conclusion remains identical. Their original compiler errors and
changed lines are recorded in report.md.

## Users

The table includes the union of the textual users returned by downstream.py --uses
for the three changed names, the item and provider modules. All transitive users
retain exactly the same definitions, because no construction body changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianDerivedExchangePlusCompatibility | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeAdjunction | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeCore | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeSource | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeTransport | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.DerivedSquareIsoCommShift | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsExchange | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsPullbackSquare | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparisonFactorization | unclaimed | Replace explicit unfolding by the equation lemma; signature unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.StrictHenselizationRestriction | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.StrictLocalComplexSectionsMate | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.StrictLocalDerivedExchangeGlobalSections | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.StrictLocalDerivedExchangeLeray | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.StrictLocalDerivedMateSectionsFactorization | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceDerivedRestriction | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceRestriction | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceSections | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.AlgebraicGeometry.StrictLocalMateProjectionData | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Hide the unchanged body; add proved equation APIs. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | B2 | Prove the original theorem, preserving its signature. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | claimed, unchanged | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquare | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareTransport | claimed, unchanged | Unchanged mathematical definitions and source; consumer validation in report.md. |
| WeilConjectures.SixFunctors.BaseChange.DerivedComparison | unclaimed | Replace explicit unfolding by the equation lemma; signature unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs | unclaimed | Hide the unchanged body; add proved equation APIs. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Unchanged; user of the cached pullback comparison interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen | unclaimed | Unchanged; both baseline and overlay reach the file time limit. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged mathematical definitions and source; consumer validation in report.md. |

## Status

landed 20261016T221554-L-1611092 2026-10-16 (merge of deliver/B2/Sheaf.Paper.CoefficientExchangeFromComparisons)

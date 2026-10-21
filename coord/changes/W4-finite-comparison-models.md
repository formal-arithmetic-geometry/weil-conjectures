# AlgebraicGeometry.Scheme finite comparison representative models

## Reason

Move the five representative-model declarations to a dependency module so the new
existence lemma can use exactly the original normalization without importing its parent.
The item proves uniqueness from that existence result. This is an interface-preserving
move under Sheaf; no adopted source module changes.

## Old

In Sheaf.Paper.CompletedRingStrictFiniteExchange:

```lean
/-- The finite reduction's universal comparison, retaining its own finite action.
Source: Stacks 06YY (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
def cbcFiniteReductionModelMap (T : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    (cbcFiniteReduction d T n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((cbcFiniteReductionModule d T n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (pbcDerivedRestrict (pbcLevelConstantComparison T d n).hom).map
      (pbcComplexCounit (pbcAdicProjection T d n) P) ≫
    (pbcRestrict (pbcLevelConstantComparison T d n).hom).mapDerivedCategoryFactors.hom.app
      (((reductionChange T (pbcAdicProjection T d n)).mapHomologicalComplex (.up ℤ)).obj P)

/-- Finite source comparison on representatives.
Source: Stacks 06YY (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
def cbcFiniteSourceModelMap (n : ℕ)
    (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ) :
    (cbcFiniteReduction d U n ⋙ (cbcFiniteSource d sq n).mapDerivedCategory).obj
      (DerivedCategory.Q.obj P) ⟶
    DerivedCategory.Q.obj
      (((cbcFiniteSource d sq n).mapHomologicalComplex (.up ℤ)).obj
        (((cbcFiniteReductionModule d U n).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (cbcFiniteSource d sq n).mapDerivedCategory.map (cbcFiniteReductionModelMap d U n P) ≫
    (cbcFiniteSource d sq n).mapDerivedCategoryFactors.hom.app
      (((cbcFiniteReductionModule d U n).mapHomologicalComplex (.up ℤ)).obj P)

/-- Finite target comparison on representatives.
Source: Stacks 06YY (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
def cbcFiniteTargetModelMap (n : ℕ)
    (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ) :
    (cbcFiniteReduction d U n ⋙ (cbcFiniteTarget d sq n).mapDerivedCategory).obj
      (DerivedCategory.Q.obj P) ⟶
    DerivedCategory.Q.obj
      (((cbcFiniteTarget d sq n).mapHomologicalComplex (.up ℤ)).obj
        (((cbcFiniteReductionModule d U n).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (cbcFiniteTarget d sq n).mapDerivedCategory.map (cbcFiniteReductionModelMap d U n P) ≫
    (cbcFiniteTarget d sq n).mapDerivedCategoryFactors.hom.app
      (((cbcFiniteReductionModule d U n).mapHomologicalComplex (.up ℤ)).obj P)

/-- Normalization of the finite source comparison on every K-flat representative.
Source: Stacks 099N, 06XN (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
def CbcSourceFiniteNormalization (n : ℕ)
    (e : completedReductionTower U d ⋙ cbcStrictOpen d j sq.isOpenImmersion ⋙
        completedTowerPullback g d ⋙ pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
      cbcFiniteReduction d U n ⋙ (cbcFiniteSource d sq n).mapDerivedCategory) : Prop :=
  ∀ P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P →
    HEq
      ((pbcTowerEvaluation X' (pbcAdicCompletion X' d) n).map (cbcSourceModelMap d sq P) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj
        (op n)).mapDerivedCategoryFactors.hom.app
          (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
            (((cbcStrictOpenModule d j sq.isOpenImmersion).mapHomologicalComplex (.up ℤ)).obj
              (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj
                P))) ≫
      DerivedCategory.Q.map ((@NatTrans.mapHomologicalComplex _ _ _ _ _ _ _ _ _
        (cbcSourceLevel_preservesZeroMorphisms d sq n)
        (cbcFiniteSourceModel_preservesZeroMorphisms d sq n)
        (cbcSourceLevel d sq n).hom (.up ℤ)).app P))
      (e.hom.app (DerivedCategory.Q.obj P) ≫ cbcFiniteSourceModelMap d sq n P)

/-- Normalization of the finite target comparison on the identical representative class.
Source: Stacks 099N, 06XN (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
def CbcTargetFiniteNormalization (n : ℕ)
    (e : completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
        cbcStrictOpen d j' sq.isOpenImmersion' ⋙
          pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
      cbcFiniteReduction d U n ⋙ (cbcFiniteTarget d sq n).mapDerivedCategory) : Prop :=
  ∀ P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P →
    HEq
      ((pbcTowerEvaluation X' (pbcAdicCompletion X' d) n).map (cbcTargetModelMap d sq P) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj
        (op n)).mapDerivedCategoryFactors.hom.app
          (((cbcStrictOpenModule d j' sq.isOpenImmersion').mapHomologicalComplex (.up ℤ)).obj
            (((completedTowerModulePullback gU d).mapHomologicalComplex (.up ℤ)).obj
              (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj
                P))) ≫
      DerivedCategory.Q.map ((@NatTrans.mapHomologicalComplex _ _ _ _ _ _ _ _ _
        (cbcTargetLevel_preservesZeroMorphisms d sq n)
        (cbcFiniteTargetModel_preservesZeroMorphisms d sq n)
        (cbcTargetLevel d sq n).hom (.up ℤ)).app P))
      (e.hom.app (DerivedCategory.Q.obj P) ≫ cbcFiniteTargetModelMap d sq n P)

```

## New

The five declarations above, with verbatim signatures, attributes and bodies, are in
Sheaf.Paper.CompletedFiniteComparisonModels. The original module publicly imports it,
so all old importers continue to see the same declarations. No target, mathematical
definition or public signature changes. The new existence module privately imported
by the item uses this common dependency, avoiding an import cycle.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedRingStrictFiniteExchange | W4 | Publicly imports the model module; proves finite-comparison uniqueness. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Existing import continues to expose identical declarations; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Existing import continues to expose identical declarations; no adaptation. |
| Sheaf.Paper.NormalizedFiniteComparisonExistence | new, W4 | Imports model definitions in its public statement. |

The downstream scan finds only the item itself using cbcFiniteSourceModelMap by name.
The two downstream modules listed above are the entire module closure reported by
`tools/downstream.py Sheaf.Paper.CompletedRingStrictFiniteExchange --uses cbcFiniteSourceModelMap`.

## Status

landed 20261021T183353-L-1610710 2026-10-21 (merge of deliver/W4/Sheaf.Paper.CompletedRingStrictFiniteExchange)

# WeilConjectures.PrimitiveCounit.RoosRealization

## Reason

The original record repeats long derived-limit types in generated declarations. Full-file
compilation repeatedly exceeded 60 seconds after adding the proofs. Name the comparison
type and its two original predicates, and keep them locally folded while the record is
elaborated. The field types are definitionally equal to the originals: no hypothesis,
normalization equation, projection equation or quantifier changes. The total-limit
K-injective formula still uses the actual inclusion with zero shifted coordinate.

The local unfolding settings also require explicit presentations in finiteTensorBridge
and explicit functor arguments in inverseComplexEvaluation. These are definitionally
the original identity bridge and the original composite comparison. No data is chosen
from a new theorem, and no theorem signature changes.

## Old

```lean
structure RoosRealization (W : Scheme.{t}) where
  comparison : (roosF (A := scalarReductionSource l E W)) ⋙ DerivedCategory.Q ≅
    DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W
  projection : ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ),
    comparison.hom.app Z ≫
        (coefficientConstantTowerProjection l E W n).app (DerivedCategory.Q.obj Z) ≫
        (coefficientConstantTowerEvaluationFactors l E W n).hom.app Z =
      DerivedCategory.Q.map (roosEval Z n)
  resolution : ∀ (Z I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (q : Z ⟶ I) [QuasiIso q] [I.IsKInjective],
    ∃ ι : DerivedCategory.Q.obj (limit I.asFunctor) ≅ DerivedCategory.Q.obj (roosF.obj I),
      ι.hom = DerivedCategory.Q.map (roosι I) ∧
      comparison.hom.app Z ≫
          (coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map q) =
        DerivedCategory.Q.map (roosF.map q) ≫ ι.inv ≫
          DerivedCategory.Q.map (limitComplexIso l E W I).hom ≫
          (Functor.rightDerivedFunctorObjQIso
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) I).inv
```

```lean
def finiteTensorBridge (W : Scheme.{t}) (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op n) :=
  Iso.refl _
```

```lean
def inverseComplexEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    (inverse l E f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ) ≅
    (coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ) ⋙
      (integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ) :=
  by
    letI : (integralOperationsLevelPullback l E f n).Additive :=
      integralOperationsLevelPullback_additive l E f n
    exact (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)) ≪≫
      NatIso.mapHomologicalComplex (inverseEvaluation l E f n) (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm
```

## New

```lean
def RoosComparison (W : Scheme.{t}) :=
  (roosF (A := scalarReductionSource l E W)) ⋙ DerivedCategory.Q ≅
    DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W
```

```lean
def RoosResolution (W : Scheme.{t})
    (comparison : RoosComparison l E W) : Prop :=
  ∀ (Z I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (q : Z ⟶ I) [QuasiIso q] [I.IsKInjective],
    ∃ ι : DerivedCategory.Q.obj (limit I.asFunctor) ≅ DerivedCategory.Q.obj (roosF.obj I),
      ι.hom = DerivedCategory.Q.map (roosι I) ∧
      comparison.hom.app Z ≫
          (coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map q) =
        DerivedCategory.Q.map (roosF.map q) ≫ ι.inv ≫
          DerivedCategory.Q.map (limitComplexIso l E W I).hom ≫
          (Functor.rightDerivedFunctorObjQIso
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) I).inv
```

```lean
def RoosProjection (W : Scheme.{t}) (comparison : RoosComparison l E W) : Prop :=
  ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ),
    comparison.hom.app Z ≫
        (coefficientConstantTowerProjection l E W n).app (DerivedCategory.Q.obj Z) ≫
        (coefficientConstantTowerEvaluationFactors l E W n).hom.app Z =
      DerivedCategory.Q.map (roosEval Z n)
```

```lean
structure RoosRealization (W : Scheme.{t}) where
  comparison : RoosComparison l E W
  projection : RoosProjection l E W comparison
  resolution : RoosResolution l E W comparison
```

```lean
def finiteTensorBridge (W : Scheme.{t}) (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op n) :=
  by
    change ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).obj
          (((unrestrictedIntegralReductionFunctor l E W n).mapHomologicalComplex
            (.up ℤ)).obj P,
            ((unrestrictedIntegralReductionFunctor l E W n).mapHomologicalComplex
              (.up ℤ)).obj Q))
    unfold scalarReductionExtension unrestrictedIntegralReductionFunctor
    unfold scalarReductionExistence unrestrictedIntegralReductionExistence
    exact Iso.refl _
```

```lean
def inverseComplexEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    (inverse l E f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ) ≅
    (coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ) ⋙
      (integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ) :=
  by
    letI : (integralOperationsLevelPullback l E f n).Additive :=
      integralOperationsLevelPullback_additive l E f n
    exact (Functor.mapHomologicalComplexCompIso
      (F := inverse l E f) (G := coefficientSequenceEvaluation l E X n)
      (Iso.refl _) (.up ℤ)) ≪≫
      NatIso.mapHomologicalComplex (inverseEvaluation l E f n) (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (F := coefficientSequenceEvaluation l E Y n)
          (G := integralOperationsLevelPullback l E f n) (Iso.refl _) (.up ℤ)).symm
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedPrimitiveCounitComparison | S3 | Own item; five proofs and definitionally equal record presentation. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Unchanged; all equations and field types retain their meaning. |
| Sheaf.Paper.CompletedComparisonQuotientRealization | unclaimed | Unchanged; all equations and field types retain their meaning. |
| Sheaf.Paper.CompletedUnitPullbackTower | unclaimed | Unchanged; all equations and field types retain their meaning. |
| Sheaf.Paper.ExpressionCounitSubstitutionCoherence | unclaimed | Unchanged; all equations and field types retain their meaning. |
| Sheaf.Paper.FiniteExpressionReductionComparison | unclaimed | Unchanged; all equations and field types retain their meaning. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed | Unchanged; all equations and field types retain their meaning. |
| Sheaf.Paper.NormalizedPullbackCompositionTransport | unclaimed | Unchanged; all equations and field types retain their meaning. |
| Sheaf.Paper.NormalizedTensorConstraintTransport | unclaimed | Unchanged; all equations and field types retain their meaning. |

The downstream search for RoosRealization finds the item and five external modules.
finiteTensorBridge and inverseComplexEvaluation have no external direct users.
The full downstream closure is listed above. No consumer source adaptation is needed.
The five external direct users are compiled unchanged against the new item.

Any target depending on this record is reopened for the required definition-meaning
review. This is a definitional refactor, so the review should confirm identical meaning.

## Status

landed 20261024T191013-L-210106 2026-10-24 (merge of deliver/S3/Sheaf.Paper.CompletedPrimitiveCounitComparison)

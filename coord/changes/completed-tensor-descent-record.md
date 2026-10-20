# integralCompletedTensor and integralCompletedTensorComparison

## Reason

Consumers of the tensor descent need its universal property. Extracting that property
from the full nested existence statement repeated large dependent conversions during
kernel checking. Package the existing chosen functor, comparison and uniqueness proof
in `IntegralCompletedTensorDescent`. No new functor or comparison is chosen.

## Old

```lean
noncomputable def integralCompletedTensor (W : AlgebraicGeometry.Scheme.{t}) :
    (DerivedCategory (integralTowerModules.{t, u} l E W)) ×
      (DerivedCategory (integralTowerModules.{t, u} l E W)) ⥤
        DerivedCategory (integralTowerModules.{t, u} l E W) :=
  (integralOperationsWellDefined l E (𝟙 W) W).2.2.choose_spec.choose_spec.choose

noncomputable def integralCompletedTensorComparison (W : AlgebraicGeometry.Scheme.{t}) :
    ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙ integralCompletedTensor l E W ≅
        integralOperationsTensorOnGood l E W :=
  (integralOperationsWellDefined l E (𝟙 W) W).2.2.choose_spec.choose_spec.choose_spec.choose
```

## New

```lean
structure IntegralCompletedTensorDescent (W : AlgebraicGeometry.Scheme.{t}) where
  functor : (DerivedCategory (integralTowerModules l E W)) ×
    (DerivedCategory (integralTowerModules l E W)) ⥤
      DerivedCategory (integralTowerModules l E W)
  comparison : ((integralOperationsGoodLocalization l E W).prod
    (integralOperationsGoodLocalization l E W)) ⋙ functor ≅
      integralOperationsTensorOnGood l E W
  universal : ∀ (G' : (DerivedCategory (integralTowerModules l E W)) ×
      (DerivedCategory (integralTowerModules l E W)) ⥤
        DerivedCategory (integralTowerModules l E W))
    (d' : ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙ G' ≅
        integralOperationsTensorOnGood l E W),
    ∃! ι : functor ≅ G', Functor.isoWhiskerLeft
      ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ι ≪≫ d' = comparison

/-- The existing normalized descent, packaged without making a new choice.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralCompletedTensorDescent (W : AlgebraicGeometry.Scheme.{t}) :
    IntegralCompletedTensorDescent l E W where
  functor :=
    (integralOperationsWellDefined l E (𝟙 W) W).2.2.choose_spec.choose_spec.choose
  comparison :=
    (integralOperationsWellDefined l E (𝟙 W) W).2.2.choose_spec.choose_spec.choose_spec.choose
  universal :=
    (integralOperationsWellDefined l E (𝟙 W) W).2.2.choose_spec.choose_spec
      |>.choose_spec.choose_spec.2.1

noncomputable def integralCompletedTensor (W : AlgebraicGeometry.Scheme.{t}) :
    (DerivedCategory (integralTowerModules.{t, u} l E W)) ×
      (DerivedCategory (integralTowerModules.{t, u} l E W)) ⥤
        DerivedCategory (integralTowerModules.{t, u} l E W) :=
  (integralCompletedTensorDescent l E W).functor

noncomputable def integralCompletedTensorComparison (W : AlgebraicGeometry.Scheme.{t}) :
    ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙ integralCompletedTensor l E W ≅
        integralOperationsTensorOnGood l E W :=
  (integralCompletedTensorDescent l E W).comparison
```

Both projections have exactly the old choice expressions as their record fields.
The universal field packages their existing uniqueness proof; no new choice is made.
The data definition contains no postponed proof and the defining comparison determines
the descent up to unique compatible isomorphism. All signatures stay verbatim.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.CompletedPullbackTensorComparison | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.DerivedPullbackTensorHom | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.IntegralDerivedOperations | unclaimed | Packages the same choices in a record; projects the existing definitions. |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | T5 | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.IntegralOperationsScalarExtension | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.SixFunctors.CompletedTensorShiftRight | J8 | Uses the universal field; constructs the signed model comparison. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Definitions and statements unchanged; the two existing values stay definitionally equal. |

All existing consumers keep definitionally equal functor and comparison interfaces.
No forced adaptation is included. The site-slice definition attachment of
`def-pur-integral-derived-operations` stays unchanged.

## Status

landed 20261020T230756-L-611403 2026-10-20 (merge of deliver/J8/Sheaf.SixFunctors.CompletedTensorShiftRight)

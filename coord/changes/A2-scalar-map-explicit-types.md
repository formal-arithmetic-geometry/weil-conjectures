# WeilConjectures scalar comparison map signatures

## Reason

Give each chosen representative map its existing mathematical type explicitly, avoiding repeated inference through long normalization formulas. Bodies and resulting types are unchanged. Target definition review is requested.

## Old

```lean
def scalarRoosMap
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type a'} [Category.{b'} B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  (scalarRoosMap_existsUnique F C).exists.choose

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
```

```lean
def scalarPullbackLevel {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (scalarPullbackLevel_existsUnique l E L ι f n).exists.choose
```

```lean
def scalarPullbackTower {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :=
  (scalarPullbackTower_existsUnique l E L ι f).exists.choose
```

```lean
def scalarPullbackChain {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((integralOperationsPullbackComplexFunctor l E f).obj P) ⟶
      (integralOperationsPullbackComplexFunctor l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  scalarRoosMap (integralOrdinaryScalar l E L ι X)
      ((integralOperationsPullbackTowerFunctor l E f).obj P) ≫
    integralOperationsRoosMap ((scalarPullbackTower l E L ι f).app P)
```

```lean
def scalarTensorLevel (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :=
  (scalarTensorLevel_existsUnique l E L ι W n).exists.choose
```

```lean
def scalarTensorTower (W : AlgebraicGeometry.Scheme.{u}) :=
  (scalarTensorTower_existsUnique l E L ι W).exists.choose
```

```lean
def scalarTensorChain (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((integralOperationsTensorComplexFunctor l E W).obj (P, Q)) ⟶
      (integralOperationsTensorComplexFunctor l L W).obj
        ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P),
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q)) :=
  scalarRoosMap (integralOrdinaryScalar l E L ι W)
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)) ≫
    integralOperationsRoosMap ((scalarTensorTower l E L ι W).app (P, Q))
```

```lean
def scalarPullbackOrdinary {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :=
  (scalarPullbackOrdinary_existsUnique l E L ι f).exists.choose
```

```lean
def scalarTensorOrdinary (W : AlgebraicGeometry.Scheme.{u}) :=
  (scalarTensorOrdinary_existsUnique l E L ι W).exists.choose
```

```lean
def scalarCompletion (W : AlgebraicGeometry.Scheme.{u}) :=
  (scalarCompletion_existsUnique l E L ι W).exists.choose
```

```lean
def scalarOrdinaryTensorChain (W : AlgebraicGeometry.Scheme.{u}) :=
  (scalarOrdinaryTensorChain_existsUnique l E L ι W).exists.choose
```

```lean
def scalarClosedTensor (W : AlgebraicGeometry.Scheme.{u}) :=
  (scalarClosedTensor_existsUnique l E L ι W).exists.choose
```

```lean
def scalarHomOrdinary (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W)) :=
  coefficientBaseChangeHom (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
    (integralOrdinaryDerivedScalar l E L ι W) (scalarClosedTensor l E L ι W) M N
```


```lean
def scalarIntegralClosed (W : AlgebraicGeometry.Scheme.{u}) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.integralClosed

def scalarIntegralModels (W : AlgebraicGeometry.Scheme.{u}) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.integralTensorModel
```

## New

```lean
def scalarRoosMap
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type a'} [Category.{b'} B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos C) ⟶
      integralOperationsRoos (C ⋙ F.mapHomologicalComplex (.up ℤ)) :=
  (scalarRoosMap_existsUnique F C).exists.choose

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
```

```lean
def scalarPullbackLevel {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    integralOperationsPullbackLevel l E f n ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackLevel l L f n :=
  (scalarPullbackLevel_existsUnique l E L ι f n).exists.choose
```

```lean
def scalarPullbackTower {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    integralOperationsPullbackTowerFunctor l E f ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackTowerFunctor l L f :=
  (scalarPullbackTower_existsUnique l E L ι f).exists.choose
```

```lean
def scalarPullbackChain {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((integralOperationsPullbackComplexFunctor l E f).obj P) ⟶
      (integralOperationsPullbackComplexFunctor l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  scalarRoosMap (integralOrdinaryScalar l E L ι X)
      ((integralOperationsPullbackTowerFunctor l E f).obj P) ≫
    integralOperationsRoosMap ((scalarPullbackTower l E L ι f).app P)
```

```lean
def scalarTensorLevel (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    integralOperationsTensorLevel l E W n ⋙
        (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorLevel l L W n :=
  (scalarTensorLevel_existsUnique l E L ι W n).exists.choose
```

```lean
def scalarTensorTower (W : AlgebraicGeometry.Scheme.{u}) :
    integralOperationsTensorTowerFunctor l E W ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorTowerFunctor l L W :=
  (scalarTensorTower_existsUnique l E L ι W).exists.choose
```

```lean
def scalarTensorChain (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((integralOperationsTensorComplexFunctor l E W).obj (P, Q)) ⟶
      (integralOperationsTensorComplexFunctor l L W).obj
        ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P),
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q)) :=
  scalarRoosMap (integralOrdinaryScalar l E L ι W)
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)) ≫
    integralOperationsRoosMap ((scalarTensorTower l E L ι W).app (P, Q))
```

```lean
def scalarPullbackOrdinary {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f :=
  (scalarPullbackOrdinary_existsUnique l E L ι f).exists.choose
```

```lean
def scalarTensorOrdinary (W : AlgebraicGeometry.Scheme.{u}) :
    integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W :=
  (scalarTensorOrdinary_existsUnique l E L ι W).exists.choose
```

```lean
def scalarCompletion (W : AlgebraicGeometry.Scheme.{u}) :
    integralOrdinaryDerivedScalar l E L ι W ⟶ integralScalarExtension l E L ι W :=
  (scalarCompletion_existsUnique l E L ι W).exists.choose
```

```lean
def scalarOrdinaryTensorChain (W : AlgebraicGeometry.Scheme.{u}) :
    coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙
          (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l L W) :=
  (scalarOrdinaryTensorChain_existsUnique l E L ι W).exists.choose
```

```lean
def scalarClosedTensor (W : AlgebraicGeometry.Scheme.{u}) :
    (scalarIntegralClosed l E W).tensor ⋙
        integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ (scalarIntegralClosed l L W).tensor :=
  (scalarClosedTensor_existsUnique l E L ι W).exists.choose
```

```lean
def scalarHomOrdinary (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W)) :
    (integralOrdinaryDerivedScalar l E L ι W).obj
        ((integralDerivedInternalHom l E W).obj (op M, N)) ⟶
      (integralDerivedInternalHom l L W).obj
        (op ((integralOrdinaryDerivedScalar l E L ι W).obj M),
          (integralOrdinaryDerivedScalar l E L ι W).obj N) :=
  coefficientBaseChangeHom (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
    (integralOrdinaryDerivedScalar l E L ι W) (scalarClosedTensor l E L ι W) M N
```


```lean
def scalarIntegralClosed (W : AlgebraicGeometry.Scheme.{u}) :
    CoefficientClosedStructure (integralDerivedInternalHom l E W) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.integralClosed

def scalarIntegralModels (W : AlgebraicGeometry.Scheme.{u}) :
    CoefficientTensorModels.{u, u+1, u, u+2}
      (AlgebraicGeometry.Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) (scalarIntegralClosed l E W) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.integralTensorModel
```

(The two entries above were added by the reviewer: the delivery also gave these two
definitions explicit types.)

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportScalarShiftNormalization | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.CompactSupportScalarLimitReduction | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.FdScalarRoosComparisonIntertwining | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.PointFibreDerivedTensor | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | A2 | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.ExplicitScalarConeWordCoordinates | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.FrameworkPbcComparisonData | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.PointFibreDerivedTensorCompatibility | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.SourceSectionStalkConeComparison | K6 | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.SpecifiedHomScalarEvaluationArbitraryScheme | R2 | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.PointAutomorphismTransportScalarExtension | J2 | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.DerivedPullbackTensorHom | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.CompletedHomScalarTranspose | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.TraceBoundedQuotientStalkRealization | K8 | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.CompactSupportStrictScalarRefinement | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | F7 | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.CanonicalTateComparisons | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.TraceStalkCompositorTowerRealization | K9 | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.FrobeniusSquareExchange | H6 | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.CompactSupportSystemTransposeNormalization | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.CompletedInverseImageScalarCounit | U3 | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.PodCompletionReindexCoefficientTransition | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.FdScalarPullbackRealizationIdentification | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.SfScalarExtensionComposition | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | unclaimed | Definitionally identical type; no adaptation expected. |
| Sheaf.SixFunctors.OpenRoosUnitAdjunction | P2 | Definitionally identical type; no adaptation expected. |

## Status

landed 20261025T100750-L-3621432 2026-10-25 (merge of deliver/A2/Sheaf.Paper.IntegralOperationsScalarComparisons)

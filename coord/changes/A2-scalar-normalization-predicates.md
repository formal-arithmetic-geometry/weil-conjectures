# WeilConjectures scalar normalization predicates

## Reason

Store the long representative formulas once, so chosen-map type checking does not
repeatedly elaborate their full inferred signatures. Each predicate is exactly its
original formula. Target meanings are unchanged; definition review is requested.

## Old

```lean
theorem scalarPullbackLevel_existsUnique {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃! α : integralOperationsPullbackLevel l E f n ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackLevel l L f n,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (V : Y.ProEt)
        (x : (P.X i).val.obj (op V)),
        ((α.app P).f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X
            (((integralOperationsPullbackLevel l E f n).obj P).X i)
            (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V)) 1
            (integralOperationsPullbackGenerator l E f n
              (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
              (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x))) =
        integralOperationsPullbackGenerator l L f n
          (((unrestrictedIntegralFiniteComplex l L Y n).obj
            (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)).X i) V
          (unrestrictedIntegralTensorSection l L Y n
            ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) (op V) 1
            (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x))
```

```lean
theorem scalarPullbackTower_existsUnique {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) :
    ∃! α : integralOperationsPullbackTowerFunctor l E f ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackTowerFunctor l L f,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ),
        (α.app P).app (op n) = (scalarPullbackLevel l E L ι f n).app P
```

```lean
theorem scalarTensorLevel_existsUnique (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    ∃! α : integralOperationsTensorLevel l E W n ⋙
        (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorLevel l L W n,
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((α.app (P, Q)).f (p + q)).val.app U
          (integralOrdinaryTensorSection l E L ι W
            (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)) U 1
            (integralOperationsTotalTensorSection l E W n P Q p q U
              (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
              (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y))) =
        integralOperationsTotalTensorSection l L W n
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q U
          (unrestrictedIntegralTensorSection l L W n
            ((integralOrdinaryScalar l E L ι W).obj (P.X p)) U 1
            (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x))
          (unrestrictedIntegralTensorSection l L W n
            ((integralOrdinaryScalar l E L ι W).obj (Q.X q)) U 1
            (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y))
```

```lean
theorem scalarTensorTower_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : integralOperationsTensorTowerFunctor l E W ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorTowerFunctor l L W,
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ),
        (α.app (P, Q)).app (op n) = (scalarTensorLevel l E L ι W n).app (P, Q)
```

```lean
theorem scalarPullbackOrdinary_existsUnique {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) :
    ∃! α : integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι X).map
            ((integralDerivedPullbackComparison l E f).hom.app P) ≫
          (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
            ((integralOperationsPullbackComplexFunctor l E f).obj P.obj) ≫
          DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj) =
        α.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (integralDerivedPullback l L f).map
            ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj) ≫
          (integralDerivedPullbackComparison l L f).hom.app
            ⟨_, scalarGood l E L ι Y P⟩
```

```lean
theorem scalarTensorOrdinary_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W,
      ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι W).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) ≫
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map (scalarTensorChain l E L ι W P.obj Q.obj) =
        α.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (integralCompletedTensor l L W).map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
          (integralCompletedTensorComparison l L W).hom.app
            (⟨_, scalarGood l E L ι W P⟩, ⟨_, scalarGood l E L ι W Q⟩)
```

```lean
theorem scalarCompletion_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! χ : integralOrdinaryDerivedScalar l E L ι W ⟶ integralScalarExtension l E L ι W,
      (∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        χ.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparison l E L ι W).hom.app P =
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι W).app P.obj)) ∧
      (∀ K, IsSfDerivedComplete l E W K → IsIso (χ.app K))
```

```lean
theorem scalarOrdinaryTensorChain_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙
          (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l L W),
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((α.hom.app (P, Q)).f (p + q)).val.app U
          (integralOrdinaryTensorSection l E L ι W
            (((coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X (p + q)) U 1
            (coefficientTensorGenerator.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl U x y)) =
        coefficientTensorGenerator.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l L W)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x)
          (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y)
```

```lean
theorem scalarClosedTensor_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : (scalarIntegralClosed l E W).tensor ⋙
        integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ (scalarIntegralClosed l L W).tensor,
      ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι W).map
          (((scalarIntegralModels l E W).iso _ _ _ _ _ P.property.1 Q.property.1).hom) ≫
          α.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (scalarIntegralClosed l L W).tensor.map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q.obj)) =
        (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
          ((coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map ((scalarOrdinaryTensorChain l E L ι W).hom.app (P.obj, Q.obj)) ≫
          ((scalarIntegralModels l L W).iso _ _ _ _ _
            (scalarGood l E L ι W P).1 (scalarGood l E L ι W Q).1).hom
```

## New

```lean
def scalarPullbackLevelNormalization {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    (α : integralOperationsPullbackLevel l E f n ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackLevel l L f n) : Prop :=
  ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (V : Y.ProEt)
        (x : (P.X i).val.obj (op V)),
        ((α.app P).f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X
            (((integralOperationsPullbackLevel l E f n).obj P).X i)
            (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V)) 1
            (integralOperationsPullbackGenerator l E f n
              (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
              (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x))) =
        integralOperationsPullbackGenerator l L f n
          (((unrestrictedIntegralFiniteComplex l L Y n).obj
            (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)).X i) V
          (unrestrictedIntegralTensorSection l L Y n
            ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) (op V) 1
            (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x))
```

```lean
theorem scalarPullbackLevel_existsUnique {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃! α : integralOperationsPullbackLevel l E f n ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackLevel l L f n, scalarPullbackLevelNormalization l E L ι f n α
```

```lean
def scalarPullbackTowerNormalization {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y)
    (α : integralOperationsPullbackTowerFunctor l E f ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackTowerFunctor l L f) : Prop :=
  ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ),
        (α.app P).app (op n) = (scalarPullbackLevel l E L ι f n).app P
```

```lean
theorem scalarPullbackTower_existsUnique {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) :
    ∃! α : integralOperationsPullbackTowerFunctor l E f ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackTowerFunctor l L f, scalarPullbackTowerNormalization l E L ι f α
```

```lean
def scalarTensorLevelNormalization (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (α : integralOperationsTensorLevel l E W n ⋙
        (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorLevel l L W n) : Prop :=
  ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((α.app (P, Q)).f (p + q)).val.app U
          (integralOrdinaryTensorSection l E L ι W
            (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)) U 1
            (integralOperationsTotalTensorSection l E W n P Q p q U
              (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
              (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y))) =
        integralOperationsTotalTensorSection l L W n
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q U
          (unrestrictedIntegralTensorSection l L W n
            ((integralOrdinaryScalar l E L ι W).obj (P.X p)) U 1
            (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x))
          (unrestrictedIntegralTensorSection l L W n
            ((integralOrdinaryScalar l E L ι W).obj (Q.X q)) U 1
            (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y))
```

```lean
theorem scalarTensorLevel_existsUnique (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    ∃! α : integralOperationsTensorLevel l E W n ⋙
        (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorLevel l L W n, scalarTensorLevelNormalization l E L ι W n α
```

```lean
def scalarTensorTowerNormalization (W : AlgebraicGeometry.Scheme.{u})
    (α : integralOperationsTensorTowerFunctor l E W ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorTowerFunctor l L W) : Prop :=
  ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ),
        (α.app (P, Q)).app (op n) = (scalarTensorLevel l E L ι W n).app (P, Q)
```

```lean
theorem scalarTensorTower_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : integralOperationsTensorTowerFunctor l E W ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorTowerFunctor l L W, scalarTensorTowerNormalization l E L ι W α
```

```lean
def scalarPullbackOrdinaryNormalization {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y)
    (α : integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f) : Prop :=
  ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι X).map
            ((integralDerivedPullbackComparison l E f).hom.app P) ≫
          (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
            ((integralOperationsPullbackComplexFunctor l E f).obj P.obj) ≫
          DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj) =
        α.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (integralDerivedPullback l L f).map
            ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj) ≫
          (integralDerivedPullbackComparison l L f).hom.app
            ⟨_, scalarGood l E L ι Y P⟩
```

```lean
theorem scalarPullbackOrdinary_existsUnique {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) :
    ∃! α : integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f, scalarPullbackOrdinaryNormalization l E L ι f α
```

```lean
def scalarTensorOrdinaryNormalization (W : AlgebraicGeometry.Scheme.{u})
    (α : integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι W).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) ≫
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map (scalarTensorChain l E L ι W P.obj Q.obj) =
        α.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (integralCompletedTensor l L W).map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
          (integralCompletedTensorComparison l L W).hom.app
            (⟨_, scalarGood l E L ι W P⟩, ⟨_, scalarGood l E L ι W Q⟩)
```

```lean
theorem scalarTensorOrdinary_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W, scalarTensorOrdinaryNormalization l E L ι W α
```

```lean
def scalarCompletionNormalization (W : AlgebraicGeometry.Scheme.{u})
    (χ : integralOrdinaryDerivedScalar l E L ι W ⟶ integralScalarExtension l E L ι W) : Prop :=
  (∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        χ.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparison l E L ι W).hom.app P =
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι W).app P.obj)) ∧
      (∀ K, IsSfDerivedComplete l E W K → IsIso (χ.app K))
```

```lean
theorem scalarCompletion_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! χ : integralOrdinaryDerivedScalar l E L ι W ⟶ integralScalarExtension l E L ι W, scalarCompletionNormalization l E L ι W χ
```

```lean
def scalarOrdinaryTensorChainNormalization (W : AlgebraicGeometry.Scheme.{u})
    (α : coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙
          (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l L W)) : Prop :=
  ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((α.hom.app (P, Q)).f (p + q)).val.app U
          (integralOrdinaryTensorSection l E L ι W
            (((coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X (p + q)) U 1
            (coefficientTensorGenerator.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl U x y)) =
        coefficientTensorGenerator.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l L W)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x)
          (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y)
```

```lean
theorem scalarOrdinaryTensorChain_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙
          (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l L W), scalarOrdinaryTensorChainNormalization l E L ι W α
```

```lean
def scalarClosedTensorNormalization (W : AlgebraicGeometry.Scheme.{u})
    (α : (scalarIntegralClosed l E W).tensor ⋙
        integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ (scalarIntegralClosed l L W).tensor) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι W).map
          (((scalarIntegralModels l E W).iso _ _ _ _ _ P.property.1 Q.property.1).hom) ≫
          α.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (scalarIntegralClosed l L W).tensor.map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q.obj)) =
        (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
          ((coefficientTotalTensor.{u, u+1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map ((scalarOrdinaryTensorChain l E L ι W).hom.app (P.obj, Q.obj)) ≫
          ((scalarIntegralModels l L W).iso _ _ _ _ _
            (scalarGood l E L ι W P).1 (scalarGood l E L ι W Q).1).hom
```

```lean
theorem scalarClosedTensor_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : (scalarIntegralClosed l E W).tensor ⋙
        integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ (scalarIntegralClosed l L W).tensor, scalarClosedTensorNormalization l E L ι W α
```

The chosen-map definitions and scalarHomOrdinary receive explicit result types
identical to their former inferred types. Their defining expressions are unchanged.
The chain definitions are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompactSupportScalarLimitReduction | unclaimed | Same formulas by definitional equality; no adaptation. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | A2 | Same formulas by definitional equality; no adaptation. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | unclaimed | Same formulas by definitional equality; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | Same formulas by definitional equality; no adaptation. |
| Sheaf.Paper.SfScalarExtensionComposition | unclaimed | Same formulas by definitional equality; no adaptation. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | unclaimed | Same formulas by definitional equality; no adaptation. |

## Status

landed 20261025T100750-L-3621432 2026-10-25 (merge of deliver/A2/Sheaf.Paper.IntegralOperationsScalarComparisons)

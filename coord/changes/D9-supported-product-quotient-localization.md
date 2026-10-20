# Etale/ProEtale supportQuotient coefficient and localization definitions

## Reason

The original component definition expands the signed tensor and exact-localization
comparisons independently at every use. Kernel checking of the combined proof
exceeded the fixed per-file compile limit. Factor the same canonical natural
transformation through two reusable public definitions, construct the complex
comparison first, and define its component by evaluation. Use the underlying
`tensorLeft` functor directly instead of the definitionally equal supported-tensor
wrapper. Transport additivity along the proved ordinary comparison. Use the
canonical constant oplax tensor map and right tensor map directly in the generator;
these are definitionally the original supported wrappers. Mark the ordinary chosen
comparison, complex comparison, descended localization, comparison and transported adjunction
irreducible to keep their large bodies out of downstream reduction. Their formulas
are explicitly unfolded in the proofs that need them.

There is no new choice of support object or comparison: Q is still the actual
cokernel. The new collapse `map₂HomologicalComplexObjSingleIso` is the natural
isomorphism assembled from the same `mapBifunctorSingle₁Iso` degree-zero collapse
used previously. The inserted `mapHomologicalComplexCompIso (Iso.refl _)` only
identifies the two termwise presentations. The quotient-generator, signed tensor,
normalization and all theorem signatures are preserved. In particular the five
Challenge targets are unchanged. Definitions in their import closure are changed,
so their interpretation should be rechecked in independent review; the coefficient
functor and comparison still have exactly the stated mathematical meaning.

## Old

`AlgebraicGeometry.Etale.supportQuotientCoefficients`:

```lean
noncomputable def supportQuotientCoefficients :
    ModuleCat.{u + 1} A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    (supportedSheafTensor A X).obj (supportQuotient A i)
```

`AlgebraicGeometry.Etale.supportQuotientCoefficients_additive`:

```lean
noncomputable instance supportQuotientCoefficients_additive :
    (supportQuotientCoefficients A i).Additive :=
  inferInstanceAs ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    (supportedSheafTensor A X).obj (supportQuotient A i)).Additive)
```

`AlgebraicGeometry.Etale.supportQuotientDerived`:

```lean
noncomputable def supportQuotientDerived :
    DerivedCategory (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory ⋙
    (derivedTensor (ModuleCat.{u + 1} A) X).obj
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i)))
```

`AlgebraicGeometry.Etale.supportQuotientLocalizationComponent`:

```lean
noncomputable def supportQuotientLocalizationComponent
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    (supportQuotientDerived A i).obj (DerivedCategory.Q.obj P) ⟶
      (supportQuotientCoefficients A i).mapDerivedCategory.obj (DerivedCategory.Q.obj P) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i)))).map
      ((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)).mapDerivedCategoryFactors.hom.app P) ≫
    supportedDerivedTensorLocalizationGeneric (ModuleCat.{u + 1} A) X
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i))
      (((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map
      (CochainComplex.mapBifunctorSingle₁Iso (supportedSheafTensor A X)
        (supportQuotient A i)
        (((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
    (supportQuotientCoefficients A i).mapDerivedCategoryFactors.inv.app P
```

`AlgebraicGeometry.Etale.supportQuotientLocalizationComplex`:

```lean
noncomputable def supportQuotientLocalizationComplex :
    DerivedCategory.Q ⋙ supportQuotientDerived A i ⟶
      DerivedCategory.Q ⋙ (supportQuotientCoefficients A i).mapDerivedCategory where
  app := supportQuotientLocalizationComponent A i
  naturality _ _ f := supportQuotientLocalization_naturality A i f
```

`AlgebraicGeometry.Etale.supportQuotientLocalization`:

```lean
noncomputable def supportQuotientLocalization :
    supportQuotientDerived A i ⟶ (supportQuotientCoefficients A i).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ))
    _ _ _ _ (supportQuotientLocalizationComplex A i)
```

`AlgebraicGeometry.Etale.supportQuotientComparison`:

```lean
noncomputable def supportQuotientComparison :
    supportQuotientDerived A i ≅ (supportedCoefficients A i).mapDerivedCategory :=
  @asIso _ _ _ _ (supportQuotientLocalization A i)
    (supportQuotientLocalization_isIso A i) ≪≫
      Functor.mapDerivedCategoryNatIso (supportQuotientOrdinaryIso A i)
```

`AlgebraicGeometry.Etale.supportQuotientDerivedAdjunction`:

```lean
noncomputable def supportQuotientDerivedAdjunction :
    supportQuotientDerived A i ⊣ supportedSectionsDerived A i :=
  (((supportedCoefficientAdjunction A i).ofNatIsoLeft
    (supportQuotientOrdinaryIso A i).symm).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
      (@asIso _ _ _ _ (supportQuotientLocalization A i)
        (supportQuotientLocalization_isIso A i)).symm
```

`AlgebraicGeometry.ProEtale.supportQuotientCoefficients`:

```lean
noncomputable def supportQuotientCoefficients :
    ModuleCat.{u + 1} A ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) :=
  constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⋙
    (supportedSheafTensor A X).obj (supportQuotient A i)
```

`AlgebraicGeometry.ProEtale.supportQuotientCoefficients_additive`:

```lean
noncomputable instance supportQuotientCoefficients_additive :
    (supportQuotientCoefficients A i).Additive :=
  inferInstanceAs ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⋙
    (supportedSheafTensor A X).obj (supportQuotient A i)).Additive)
```

`AlgebraicGeometry.ProEtale.supportQuotientDerived`:

```lean
noncomputable def supportQuotientDerived :
    DerivedCategory (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).mapDerivedCategory ⋙
    (derivedTensor (ModuleCat.{u + 1} A) X).obj
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i)))
```

`AlgebraicGeometry.ProEtale.supportQuotientLocalizationComponent`:

```lean
noncomputable def supportQuotientLocalizationComponent
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    (supportQuotientDerived A i).obj (DerivedCategory.Q.obj P) ⟶
      (supportQuotientCoefficients A i).mapDerivedCategory.obj (DerivedCategory.Q.obj P) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i)))).map
      ((constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A)).mapDerivedCategoryFactors.hom.app P) ≫
    supportedDerivedTensorLocalizationGeneric (ModuleCat.{u + 1} A) X
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i))
      (((constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map
      (CochainComplex.mapBifunctorSingle₁Iso (supportedSheafTensor A X)
        (supportQuotient A i)
        (((constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
    (supportQuotientCoefficients A i).mapDerivedCategoryFactors.inv.app P
```

`AlgebraicGeometry.ProEtale.supportQuotientLocalizationComplex`:

```lean
noncomputable def supportQuotientLocalizationComplex :
    DerivedCategory.Q ⋙ supportQuotientDerived A i ⟶
      DerivedCategory.Q ⋙ (supportQuotientCoefficients A i).mapDerivedCategory where
  app := supportQuotientLocalizationComponent A i
  naturality _ _ f := supportQuotientLocalization_naturality A i f
```

`AlgebraicGeometry.ProEtale.supportQuotientLocalization`:

```lean
noncomputable def supportQuotientLocalization :
    supportQuotientDerived A i ⟶ (supportQuotientCoefficients A i).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ))
    _ _ _ _ (supportQuotientLocalizationComplex A i)
```

`AlgebraicGeometry.ProEtale.supportQuotientComparison`:

```lean
noncomputable def supportQuotientComparison :
    supportQuotientDerived A i ≅ (supportedCoefficients A i).mapDerivedCategory :=
  @asIso _ _ _ _ (supportQuotientLocalization A i)
    (supportQuotientLocalization_isIso A i) ≪≫
      Functor.mapDerivedCategoryNatIso (supportQuotientOrdinaryIso A i)
```

`AlgebraicGeometry.ProEtale.supportQuotientDerivedAdjunction`:

```lean
noncomputable def supportQuotientDerivedAdjunction :
    supportQuotientDerived A i ⊣ supportedSectionsDerived A i :=
  (((supportedCoefficientAdjunction A i).ofNatIsoLeft
    (supportQuotientOrdinaryIso A i).symm).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
      (@asIso _ _ _ _ (supportQuotientLocalization A i)
        (supportQuotientLocalization_isIso A i)).symm
```

## New

`AlgebraicGeometry.Etale.supportQuotientCoefficients`:

```lean
noncomputable def supportQuotientCoefficients :
    ModuleCat.{u + 1} A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    tensorLeft (supportQuotient A i)
```

`AlgebraicGeometry.Etale.supportQuotientCoefficients_additive`:

```lean
noncomputable instance supportQuotientCoefficients_additive :
    (supportQuotientCoefficients A i).Additive :=
  Functor.additive_of_iso (supportQuotientOrdinaryIso A i).symm
```

`AlgebraicGeometry.Etale.supportQuotientDerived`:

```lean
noncomputable def supportQuotientDerived :
    DerivedCategory (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory ⋙
    tensorLeft
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i)))
```

`AlgebraicGeometry.Etale.supportQuotientLocalizationComponent`:

```lean
noncomputable def supportQuotientLocalizationComponent
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    (supportQuotientDerived A i).obj (DerivedCategory.Q.obj P) ⟶
      (supportQuotientCoefficients A i).mapDerivedCategory.obj (DerivedCategory.Q.obj P) :=
  (supportQuotientLocalizationComplex A i).app P
```

`AlgebraicGeometry.Etale.supportQuotientLocalizationComplex`:

```lean
@[irreducible]
noncomputable def supportQuotientLocalizationComplex :
    DerivedCategory.Q ⋙ supportQuotientDerived A i ⟶
      DerivedCategory.Q ⋙ (supportQuotientCoefficients A i).mapDerivedCategory :=
  letI : PreservesFiniteLimits (constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A) ⋙ tensorLeft (supportQuotient A i)) :=
    supportQuotientCoefficients_preservesFiniteLimits A i
  supportCoefficientTensorLocalization
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (supportQuotient A i)
```

`AlgebraicGeometry.Etale.supportQuotientLocalization`:

```lean
@[irreducible]
noncomputable def supportQuotientLocalization :
    supportQuotientDerived A i ⟶ (supportQuotientCoefficients A i).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ))
    _ _ _ _ (supportQuotientLocalizationComplex A i)
```

`AlgebraicGeometry.Etale.supportQuotientComparison`:

```lean
@[irreducible]
noncomputable def supportQuotientComparison :
    supportQuotientDerived A i ≅ (supportedCoefficients A i).mapDerivedCategory :=
  @asIso _ _ _ _ (supportQuotientLocalization A i)
    (supportQuotientLocalization_isIso A i) ≪≫
      Functor.mapDerivedCategoryNatIso (supportQuotientOrdinaryIso A i)
```

`AlgebraicGeometry.Etale.supportQuotientDerivedAdjunction`:

```lean
@[irreducible]
noncomputable def supportQuotientDerivedAdjunction :
    supportQuotientDerived A i ⊣ supportedSectionsDerived A i :=
  (((supportedCoefficientAdjunction A i).ofNatIsoLeft
    (supportQuotientOrdinaryIso A i).symm).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
      (@asIso _ _ _ _ (supportQuotientLocalization A i)
        (supportQuotientLocalization_isIso A i)).symm
```

`AlgebraicGeometry.ProEtale.supportQuotientCoefficients`:

```lean
noncomputable def supportQuotientCoefficients :
    ModuleCat.{u + 1} A ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) :=
  constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⋙
    tensorLeft (supportQuotient A i)
```

`AlgebraicGeometry.ProEtale.supportQuotientCoefficients_additive`:

```lean
noncomputable instance supportQuotientCoefficients_additive :
    (supportQuotientCoefficients A i).Additive :=
  Functor.additive_of_iso (supportQuotientOrdinaryIso A i).symm
```

`AlgebraicGeometry.ProEtale.supportQuotientDerived`:

```lean
noncomputable def supportQuotientDerived :
    DerivedCategory (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).mapDerivedCategory ⋙
    tensorLeft
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i)))
```

`AlgebraicGeometry.ProEtale.supportQuotientLocalizationComponent`:

```lean
noncomputable def supportQuotientLocalizationComponent
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    (supportQuotientDerived A i).obj (DerivedCategory.Q.obj P) ⟶
      (supportQuotientCoefficients A i).mapDerivedCategory.obj (DerivedCategory.Q.obj P) :=
  (supportQuotientLocalizationComplex A i).app P
```

`AlgebraicGeometry.ProEtale.supportQuotientLocalizationComplex`:

```lean
@[irreducible]
noncomputable def supportQuotientLocalizationComplex :
    DerivedCategory.Q ⋙ supportQuotientDerived A i ⟶
      DerivedCategory.Q ⋙ (supportQuotientCoefficients A i).mapDerivedCategory :=
  letI : PreservesFiniteLimits (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A) ⋙ tensorLeft (supportQuotient A i)) :=
    supportQuotientCoefficients_preservesFiniteLimits A i
  supportCoefficientTensorLocalization
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) (supportQuotient A i)
```

`AlgebraicGeometry.ProEtale.supportQuotientLocalization`:

```lean
@[irreducible]
noncomputable def supportQuotientLocalization :
    supportQuotientDerived A i ⟶ (supportQuotientCoefficients A i).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ))
    _ _ _ _ (supportQuotientLocalizationComplex A i)
```

`AlgebraicGeometry.ProEtale.supportQuotientComparison`:

```lean
@[irreducible]
noncomputable def supportQuotientComparison :
    supportQuotientDerived A i ≅ (supportedCoefficients A i).mapDerivedCategory :=
  @asIso _ _ _ _ (supportQuotientLocalization A i)
    (supportQuotientLocalization_isIso A i) ≪≫
      Functor.mapDerivedCategoryNatIso (supportQuotientOrdinaryIso A i)
```

`AlgebraicGeometry.ProEtale.supportQuotientDerivedAdjunction`:

```lean
@[irreducible]
noncomputable def supportQuotientDerivedAdjunction :
    supportQuotientDerived A i ⊣ supportedSectionsDerived A i :=
  (((supportedCoefficientAdjunction A i).ofNatIsoLeft
    (supportQuotientOrdinaryIso A i).symm).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
      (@asIso _ _ _ _ (supportQuotientLocalization A i)
        (supportQuotientLocalization_isIso A i)).symm
```

New generic definition `supportSingleTensorLocalization` (same existing blueprint node):

```lean
@[irreducible]
noncomputable def supportSingleTensorLocalization
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [SymmetricCategory C] [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    [HasColimitsOfSize.{0, 0} C] (K : C) :
    DerivedCategory.Q ⋙ tensorLeft
        (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj K)) ⟶
      (tensorLeft K).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  exact (Functor.LaxMonoidal.μNatTrans DerivedCategory.Q).app
      ((HomologicalComplex.single C (.up ℤ) 0).obj K) ≫
    Functor.whiskerRight
      (CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) K).hom
      DerivedCategory.Q
```

New generic definition `supportCoefficientTensorLocalization` (same existing blueprint node):

```lean
@[irreducible]
noncomputable def supportCoefficientTensorLocalization
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [SymmetricCategory C] [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    [HasColimitsOfSize.{0, 0} C] (F : B ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : C) [PreservesFiniteLimits (F ⋙ tensorLeft K)]
    [PreservesFiniteColimits (F ⋙ tensorLeft K)] :
    DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ tensorLeft
        (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj K))) ⟶
      DerivedCategory.Q ⋙ (F ⋙ tensorLeft K).mapDerivedCategory :=
  Functor.whiskerRight F.mapDerivedCategoryFactors.hom
      (tensorLeft (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj K))) ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (supportSingleTensorLocalization K) ≫
    Functor.whiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ tensorLeft K)) (.up ℤ)).inv
      DerivedCategory.Q ≫
    (F ⋙ tensorLeft K).mapDerivedCategoryFactors.inv
```

Additional refactoring of `AlgebraicGeometry.Etale.supportQuotientGenerator`:

Old:

```lean
noncomputable def supportQuotientGenerator (M : ModuleCat.{u + 1} A) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⟶
      (supportQuotientCoefficients A i).obj M :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map (λ_ M).inv ≫
    supportedConstantTensor A X (𝟙_ (ModuleCat.{u + 1} A)) M ≫
      ((supportedSheafTensor A X).map (cokernel.π (supportQuotientOpenArrow A i))).app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)
```

New:

```lean
noncomputable def supportQuotientGenerator (M : ModuleCat.{u + 1} A) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⟶
      (supportQuotientCoefficients A i).obj M :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map (λ_ M).inv ≫
    Functor.OplaxMonoidal.δ
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (𝟙_ _) M ≫
      (cokernel.π (supportQuotientOpenArrow A i) ▷
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)
```

Additional refactoring of `AlgebraicGeometry.Etale.supportQuotientOrdinaryIso`:

Old:

```lean
noncomputable def supportQuotientOrdinaryIso :
    supportQuotientCoefficients A i ≅ supportedCoefficients A i :=
  (supportQuotientOrdinary_existsUnique A i).choose
```

New:

```lean
@[irreducible]
noncomputable def supportQuotientOrdinaryIso :
    supportQuotientCoefficients A i ≅ supportedCoefficients A i :=
  (supportQuotientOrdinary_existsUnique A i).choose
```

Additional refactoring of `AlgebraicGeometry.ProEtale.supportQuotientGenerator`:

Old:

```lean
noncomputable def supportQuotientGenerator (M : ModuleCat.{u + 1} A) :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj M ⟶
      (supportQuotientCoefficients A i).obj M :=
  (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map (λ_ M).inv ≫
    supportedConstantTensor A X (𝟙_ (ModuleCat.{u + 1} A)) M ≫
      ((supportedSheafTensor A X).map (cokernel.π (supportQuotientOpenArrow A i))).app
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj M)
```

New:

```lean
noncomputable def supportQuotientGenerator (M : ModuleCat.{u + 1} A) :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj M ⟶
      (supportQuotientCoefficients A i).obj M :=
  (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map (λ_ M).inv ≫
    Functor.OplaxMonoidal.δ
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) (𝟙_ _) M ≫
      (cokernel.π (supportQuotientOpenArrow A i) ▷
        (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj M)
```

Additional refactoring of `AlgebraicGeometry.ProEtale.supportQuotientOrdinaryIso`:

Old:

```lean
noncomputable def supportQuotientOrdinaryIso :
    supportQuotientCoefficients A i ≅ supportedCoefficients A i :=
  (supportQuotientOrdinary_existsUnique A i).choose
```

New:

```lean
@[irreducible]
noncomputable def supportQuotientOrdinaryIso :
    supportQuotientCoefficients A i ≅ supportedCoefficients A i :=
  (supportQuotientOrdinary_existsUnique A i).choose
```

## Users

`tools/downstream.py` found 205 transitive importers and one direct importer.
Whole-word searches for every changed name found only the item itself. No
consumer is adapted. The table lists every transitive importer as well as the
item. Claim holders were read from the current coordination claims on 2026-10-20.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.SupportedProductQuotientModel` | D9 | Definitions refactored; seven proofs completed; same statements and canonical maps. |
| `Sheaf.AlgebraicGeometry.CompactProductArrows` | F6 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.AlgebraicGeometry.CompactProductRealizationArrows` | M3 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | X3 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.AlgebraicGeometry.ProperSupportCompactMaps` | T8 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | S2 | Unchanged direct importer; compile checked against new module. |
| `Sheaf.AlgebraicGeometry.SupportedBottomGluing` | K4 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.AdicPurityFiniteTensor` | W8 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.AdicPurityRootComparisons` | X5 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.AdicPuritySourceReduction` | X6 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.AdicPurityTwistReduction` | X8 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.CartierClassAgreement` | U5 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.ChernFlagFormula` | G4 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | P2 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.CompactProductProperSupportCompatibility` | G7 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.CompactProductProperSupportLaws` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.CompactProductRealizationCoreLaws` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.CompactProductRealizationLaws` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.CompactProductTwistLaws` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | H7 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | T6 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.FiniteReductionChartCalculus` | S7 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.FiniteReductionComparisons` | T7 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.FiniteReductionRootCharts` | D8 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | V6 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.LocalizedTopChern` | E5 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurAdicReconstruction` | H8 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurityAffineLineOrientation` | J6 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurityDiagonalBaseChangeCompared` | R3 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | G3 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | G6 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurityDivisorClass` | J7 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurityDncComparisons` | G3 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurityDncInvariance` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurityFrameIndependence` | A4 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | F2 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | K6 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | K7 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | W5 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.RegularImmersionCancellation` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.RegularImmersionClassData` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.RegularImmersionExteriorClass` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.RegularImmersionPurity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.RegularImmersionSignedEvaluation` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.RelativeSupportBottomDescent` | A3 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.SmoothPurityMap` | R2 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.SmoothTrace` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.SupportedClassGeometry` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.SupportedClassSiteComparison` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.SupportedExteriorClassArrows` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.SupportedExteriorShift` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.SupportedTwistDegreeZeroProduct` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.SupportedTwistMultiplication` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.SupportedTwistPullback` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.TwistFrobeniusScalar` | G4 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.WeilFourierInversion` | J6 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.WeilOne` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | D6 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | K9 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | E6 | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `TargetsCheck` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.Statement` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.CohomologicalRange` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.CohomologicalRangeAffine` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.CurveTopCohomology` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.FourierStalk` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.FourierTrace` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.LissePoincarePairing` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.LowerShriekPackage` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.OpenClosedTriangle` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.VerdierDual` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.VerdierDualFinite` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.WeilSheaf.VerdierDualLocalization` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | No reference to changed declarations; statements unaffected (transitive importer). |

## Status

landed 20261020T051159-L-1587245 2026-10-20 (merge of deliver/D9/Sheaf.AlgebraicGeometry.SupportedProductQuotientModel)

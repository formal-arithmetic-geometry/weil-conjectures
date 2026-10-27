# Tensor functor transport and representative constraint projections

## Reason

Repair C-25a68 A1 starts from the current G6 source (b4e6cc1b458 and its
published interface), preserving every retained cochain functor, shared tensor
instance, naturality API, public import and explicit localization parameter.
Only the U3 tensor-functor sharing and transportedDerivedMonoidal are reapplied.
The original tensor object and original two-whisker map are shared between the
functor and monoidal data. Proved whole-data and whole-structure equalities identify
the canonical transport. Its associator and both unitors remain definitionally the
original constraints. No arbitrary mathematical data or new postponed proof is used.

The square's generic ConstraintData abbreviates the original displayed paths.
Private validation checks compare all four full predicates with the current source
by reflexivity. The theorem signature is retained verbatim. No target meaning changes;
the definition changes remain subject to the independent reader's target check.

The current totalTensor/internalTotalTensor binders and import of
SectionCochainTensorComparison are retained. The existing tensorUnit,
localizedTotalComparison, internalLocalizationTensorMap and every D7/G6 proof are
retained verbatim. The former U3 generic flat-cover, chosen-total-comparison and lax
localization proof optimizations are not carried over. The data and realization
files select synchronous elaboration; this changes scheduling only. The resolving
constraint-data file also selects synchronous elaboration after its asynchronous
compile exceeded 60 seconds. Profiling of the unchanged definitions with this
setting measured 7.29 seconds of kernel checking, 1.99 seconds of elaboration and
0.647 seconds of linting; the accepted request completed in 22.1 seconds. All
profiling options are removed.
The representative-square proof also selects synchronous elaboration and caches
the canonical derived-category instance and the data fields of its monoidal
structure in private definitions after the public predicates. This avoids repeated
conversion through compact wrappers; the accepted profile measured 22.6 seconds
of kernel checking, 3.67 seconds of elaboration and 6.77 seconds of instance
inference. All profiling options are removed.
All adapted dependencies are unclaimed. Only Sheaf files change.

## Old

```lean
def tensor (X : Scheme.{u}) :
    DerivedCategory (modules Λ X) × DerivedCategory (modules Λ X) ⥤
      DerivedCategory (modules Λ X) :=
  ((derivedEquivalence Λ X).inverse.prod (derivedEquivalence Λ X).inverse) ⋙
    Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) ⋙ (derivedEquivalence Λ X).functor
```

```lean
def derivedMonoidal (T : Scheme.{u}) : MonoidalCategory (DerivedCategory (modules Λ T)) :=
  Monoidal.transport (derivedEquivalence Λ T)
```

```lean
def AssociatorNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ P Q H : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory,
    ((derivedPullback Λ f).map
        (@MonoidalCategoryStruct.associator _ _
          (Monoidal.transportStruct (derivedEquivalence Λ Y))
          (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj)
          (DerivedCategory.Q.obj H.obj)).hom ≫
      actualTensor Λ f (DerivedCategory.Q.obj P.obj)
        ((tensor Λ Y).obj (DerivedCategory.Q.obj Q.obj, DerivedCategory.Q.obj H.obj)) ≫
      (tensor Λ X).map (Prod.mkHom
        (𝟙 ((derivedPullback Λ f).obj (DerivedCategory.Q.obj P.obj)))
        (actualTensor Λ f (DerivedCategory.Q.obj Q.obj) (DerivedCategory.Q.obj H.obj))) ≫
      tripleOutput Λ f P.obj Q.obj H.obj =
      tripleInput Λ f P.obj Q.obj H.obj ≫ DerivedCategory.Q.map
        ((totalSectionPull Λ f).map (α_ P.obj Q.obj H.obj).hom ≫
          (sectionTotalIso Λ f P.obj (Q.obj ⊗ H.obj)).hom ≫
          (totalSectionPull Λ f).obj P.obj ◁ (sectionTotalIso Λ f Q.obj H.obj).hom)) ∧
    (actualTensor Λ f
        ((tensor Λ Y).obj (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
        (DerivedCategory.Q.obj H.obj) ≫
      (tensor Λ X).map (Prod.mkHom
        (actualTensor Λ f (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj))
        (𝟙 ((derivedPullback Λ f).obj (DerivedCategory.Q.obj H.obj)))) ≫
      (@MonoidalCategoryStruct.associator _ _
        (Monoidal.transportStruct (derivedEquivalence Λ X))
        ((derivedPullback Λ f).obj (DerivedCategory.Q.obj P.obj))
        ((derivedPullback Λ f).obj (DerivedCategory.Q.obj Q.obj))
        ((derivedPullback Λ f).obj (DerivedCategory.Q.obj H.obj))).hom ≫
      tripleOutput Λ f P.obj Q.obj H.obj =
      tripleInput Λ f P.obj Q.obj H.obj ≫ DerivedCategory.Q.map
        ((sectionTotalIso Λ f (P.obj ⊗ Q.obj) H.obj).hom ≫
          (sectionTotalIso Λ f P.obj Q.obj).hom ▷ (totalSectionPull Λ f).obj H.obj ≫
          (α_ ((totalSectionPull Λ f).obj P.obj) ((totalSectionPull Λ f).obj Q.obj)
            ((totalSectionPull Λ f).obj H.obj)).hom))
```

```lean
def UnitorNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ P : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory,
    (actualTensor Λ f
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ)))
        (DerivedCategory.Q.obj P.obj) ≫
      (tensor Λ X).map (Prod.mkHom (actualUnit Λ f)
        (𝟙 ((derivedPullback Λ f).obj (DerivedCategory.Q.obj P.obj)))) ≫
      regularLeftUnitor Λ X ((derivedPullback Λ f).obj (DerivedCategory.Q.obj P.obj)) ≫
      (pullback Λ f).mapDerivedCategoryFactors.hom.app P.obj =
      input Λ f (𝟙_ (CochainComplex (modules Λ Y) ℤ)) P.obj ≫
        DerivedCategory.Q.map
          ((sectionTotalIso Λ f (𝟙_ (CochainComplex (modules Λ Y) ℤ)) P.obj).hom ≫
            sectionTotalUnit Λ f ▷ (totalSectionPull Λ f).obj P.obj ≫
            (λ_ ((totalSectionPull Λ f).obj P.obj)).hom)) ∧
    ((derivedPullback Λ f).map (regularLeftUnitor Λ Y (DerivedCategory.Q.obj P.obj)) ≫
      (pullback Λ f).mapDerivedCategoryFactors.hom.app P.obj =
      input Λ f (𝟙_ (CochainComplex (modules Λ Y) ℤ)) P.obj ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map (λ_ P.obj).hom)) ∧
    (actualTensor Λ f (DerivedCategory.Q.obj P.obj)
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ≫
      (tensor Λ X).map (Prod.mkHom
        (𝟙 ((derivedPullback Λ f).obj (DerivedCategory.Q.obj P.obj))) (actualUnit Λ f)) ≫
      regularRightUnitor Λ X ((derivedPullback Λ f).obj (DerivedCategory.Q.obj P.obj)) ≫
      (pullback Λ f).mapDerivedCategoryFactors.hom.app P.obj =
      input Λ f P.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ≫
        DerivedCategory.Q.map
          ((sectionTotalIso Λ f P.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))).hom ≫
            (totalSectionPull Λ f).obj P.obj ◁ sectionTotalUnit Λ f ≫
            (ρ_ ((totalSectionPull Λ f).obj P.obj)).hom)) ∧
    ((derivedPullback Λ f).map (regularRightUnitor Λ Y (DerivedCategory.Q.obj P.obj)) ≫
      (pullback Λ f).mapDerivedCategoryFactors.hom.app P.obj =
      input Λ f P.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map (ρ_ P.obj).hom))
```

```lean
def regularLeftUnitor (T : Scheme.{u}) (M : DerivedCategory (modules Λ T)) :=
  (tensor Λ T).map (Prod.mkHom (regular Λ T).inv (𝟙 M)) ≫
    (@MonoidalCategoryStruct.leftUnitor _ _
      (Monoidal.transportStruct (derivedEquivalence Λ T)) M).hom
```

```lean
def regularRightUnitor (T : Scheme.{u}) (M : DerivedCategory (modules Λ T)) :=
  (tensor Λ T).map (Prod.mkHom (𝟙 M) (regular Λ T).inv) ≫
    (@MonoidalCategoryStruct.rightUnitor _ _
      (Monoidal.transportStruct (derivedEquivalence Λ T)) M).hom
```

## New

The generic sharing API is in the TensorFunctorTransport namespace. Its
struct_eq and monoidal_eq prove equality with canonical transport; the complete
tensor functor is definitionally equal to the original conjugation.

```lean
def transportedDerivedMonoidal (X : Scheme.{u}) :
    MonoidalCategory (DerivedCategory (modules Λ X)) :=
  ResolvingOplaxConstraints.TensorFunctorTransport.monoidal (derivedEquivalence Λ X)
```

```lean
def tensorObject (e : C ≌ D) (X Y : D) : D :=
  e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y)
```

```lean
def derivedMonoidal (T : Scheme.{u}) : MonoidalCategory (DerivedCategory (modules Λ T)) :=
  transportedDerivedMonoidal Λ T
```

```lean
def AssociatorNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  letI := transportedDerivedMonoidal Λ X
  letI := transportedDerivedMonoidal Λ Y
  ConstraintData.AssociatorNormalization (totalSectionPull Λ f) (derivedPullback Λ f)
    DerivedCategory.Q DerivedCategory.Q
    (fun P Q ↦ (qTensor Λ Y).app (P, Q))
    (fun P Q ↦ (qTensor Λ X).app (P, Q))
    (pullback Λ f).mapDerivedCategoryFactors.hom (sectionTotalIso Λ f)
    (actualTensor Λ f) (KFlatSectionComparison.sectionResolving Λ Y)
```

```lean
def UnitorNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  letI := transportedDerivedMonoidal Λ X
  letI := transportedDerivedMonoidal Λ Y
  ConstraintData.UnitorNormalization (totalSectionPull Λ f) (derivedPullback Λ f)
    DerivedCategory.Q DerivedCategory.Q (fun P Q ↦ (qTensor Λ Y).app (P, Q))
    (pullback Λ f).mapDerivedCategoryFactors.hom (sectionTotalIso Λ f)
    (sectionTotalUnit Λ f) (regular Λ Y) (regular Λ X)
    (actualTensor Λ f) (actualUnit Λ f) (KFlatSectionComparison.sectionResolving Λ Y)


attribute [local instance 3000] CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000] CondensedRing.projectionModuleAbelian
  CondensedRing.projectionModuleMonoidal CondensedRing.projectionModuleHasDerived
attribute [local instance 5000] CondensedRing.projectionSheafMonoidal
  CondensedRing.projectionCoefficientMonObj CondensedRing.projectionModuleCategory

set_option allowUnsafeReducibility true in
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CondensedRing.upperStar CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapHomologicalComplex

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
@[instance_reducible] private def coreModuleClosed (T : Scheme.{u}) :
    MonoidalClosed (internalModules Λ T) := inferInstance

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
@[instance_reducible] private def coreModuleBraided (T : Scheme.{u}) :
    BraidedCategory (internalModules Λ T) := inferInstance

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
@[instance_reducible] private def coreDerivedMonoidal (T : Scheme.{u}) :
    MonoidalCategory (DerivedCategory (internalModules Λ T)) := inferInstance

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem coreTensorPreservesLeft (T : Scheme.{u}) (M : internalModules Λ T) :
    PreservesColimitsOfShape ℤ ((curriedTensor (internalModules Λ T)).obj M) := by
  infer_instance

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem coreTensorPreservesRight (T : Scheme.{u}) (M : internalModules Λ T) :
    PreservesColimitsOfShape ℤ ((curriedTensor (internalModules Λ T)).flip.obj M) := by
  infer_instance

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem coreModuleFlatResolution (T : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (internalModules Λ T) := by
  infer_instance

attribute [local instance 20000] coreModuleClosed coreModuleBraided coreModuleFlatResolution
  coreTensorPreservesLeft coreTensorPreservesRight
attribute [local instance 3000] coreDerivedMonoidal

section NativeModels


private def internalTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y) ⋙ internalDerivedPullback Λ f ≅
      ((internalDerivedPullback Λ f).prod (internalDerivedPullback Λ f)) ⋙
        Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) := by
  have : IsIso (internalDelta Λ f) := by
    dsimp only [internalDelta]
    infer_instance
  exact tensorIsoFromCurried (CondensedRing.derivedTensor Λ Y)
    (CondensedRing.derivedTensor Λ X) (internalDerivedPullback Λ f) (internalDelta Λ f)

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem internalTensorIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    (internalTensorIso Λ f).hom.app (M, N) = ((internalDelta Λ f).app M).app N := by
  have : IsIso (internalDelta Λ f) := by
    dsimp only [internalDelta]
    infer_instance
  exact tensorIsoFromCurried_hom (CondensedRing.derivedTensor Λ Y)
    (CondensedRing.derivedTensor Λ X) (internalDerivedPullback Λ f) (internalDelta Λ f) M N

private def actualComparisonIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor Λ Y ⋙ derivedPullback Λ f ≅
      ((derivedPullback Λ f).prod (derivedPullback Λ f)) ⋙ tensor Λ X :=
  conjugatedIso (Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y))
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
    (derivedEquivalence Λ Y) (derivedEquivalence Λ X).functor
    (internalDerivedPullback Λ f) (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
    (tensorComparison Λ Y) (tensorComparison Λ X) (derivedPullComparison Λ f)
    (internalTensorIso Λ f)

private theorem actualComparisonIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (modules Λ Y)) :
    (actualComparisonIso Λ f).hom.app (M, N) =
      actualTensor Λ f M N := by
  have h := conjugatedIso_hom (Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y))
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
    (derivedEquivalence Λ Y) (derivedEquivalence Λ X).functor
    (internalDerivedPullback Λ f) (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
    (tensorComparison Λ Y) (tensorComparison Λ X) (derivedPullComparison Λ f)
    (internalTensorIso Λ f) M N
  simp only [internalTensorIso_hom] at h
  exact h

private def actualComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor Λ Y ⋙ derivedPullback Λ f ⟶
      ((derivedPullback Λ f).prod (derivedPullback Λ f)) ⋙ tensor Λ X where
  app M := actualTensor Λ f M.1 M.2
  naturality := by
    intro ⟨M, N⟩ ⟨M', N'⟩ a
    simpa only [actualComparisonIso_hom] using
      (actualComparisonIso Λ f).hom.naturality a

attribute [local irreducible] tensorComparison qTensor totalComparison tensor
  ResolvingOplaxConstraints.TensorFunctorTransport.tensorFunctor
  actualTensor actualUnit regular input output actualPath cochainPath
  actualComparisonIso derivedPullComparison
  CategoryTheory.Localization.Monoidal.tensorBifunctor
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.leftDerivedTensorComparison
  CategoryTheory.Functor.leftDerivedFunctorCounit
  internalPullMonoidal CondensedRing.monoidal_upperStar

set_option allowUnsafeReducibility true in
attribute [local irreducible] HomologicalComplex.mapBifunctor
  Functor.mapBifunctorHomologicalComplex




section CoreModels
section CachedGenericStructures
variable {C : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
private abbrev cachedComplexMonoidal : MonoidalCategory (CochainComplex C ℤ) := inferInstance
private abbrev cachedHomotopyMonoidal :
    MonoidalCategory (HomotopyCategory C (.up ℤ)) := inferInstance
private abbrev cachedDerivedMonoidal : MonoidalCategory (DerivedCategory C) := inferInstance
end CachedGenericStructures
attribute [local instance 2000] cachedComplexMonoidal cachedHomotopyMonoidal
  cachedDerivedMonoidal

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
private theorem tensorator_Q_generic
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (P Q : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
      ((DerivedCategory.quotientCompQhIso C).inv.app P ⊗ₘ
        (DerivedCategory.quotientCompQhIso C).inv.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj Q) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app (P ⊗ Q) := by
  unfold Functor.LaxMonoidal.μ
  unfold DerivedCategory.laxMonoidalQ
  unfold inferInstance
  unfold DerivedCategory.instLaxMonoidalCochainComplexIntQ_weilConjectures
  unfold Functor.LaxMonoidal.ofIso
  dsimp only
  rw [Functor.LaxMonoidal.comp_μ]
  change (_ ⊗ₘ _) ≫ (_ ≫ (DerivedCategory.Qh (C := C)).map (𝟙 _)) ≫ _ = _
  rw [(DerivedCategory.Qh (C := C)).map_id, Category.comp_id]
  rfl

private theorem tensorator_Q_strict {C : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (P Q : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ _).obj P)
        ((HomotopyCategory.quotient _ _).obj Q) := by
  rw [tensorator_Q_generic]
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫ _ ≫ 𝟙 _ = _
  simp only [id_tensorHom_id, Category.id_comp, Category.comp_id]
  erw [Category.comp_id]

private theorem cochain_tensor_comparison
    {C₁ C₂ : Type*} [Category.{u + 1} C₁] [Category.{u + 1} C₂]
    [Abelian C₁] [Abelian C₂]
    [IsGrothendieckAbelian.{u + 1} C₁] [IsGrothendieckAbelian.{u + 1} C₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalPreadditive C₁] [MonoidalPreadditive C₂]
    [MonoidalClosed C₁] [MonoidalClosed C₂] [BraidedCategory C₁] [BraidedCategory C₂]
    [Abelian.HasFunctorialFlatResolution C₁] [Abelian.HasFunctorialFlatResolution C₂]
    (G : C₁ ⥤ C₂) [G.Additive] [G.PreservesKFlatQuasiIso]
    [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]
    (P Q : CochainComplex C₁ ℤ) :
    ((G.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q)) ≫
      (G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P) ⊗ₘ
        G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj Q)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
    G.leftDerivedFunctor.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj (P ⊗ Q)) ≫
      DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app P).app Q) := by
  erw [tensorator_Q_strict ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q),
    tensorator_Q_strict P Q]
  let δ := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app P).app Q
  have hδ := DerivedCategory.quotientCompQhIso_hom_naturality δ
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map δ) ≫ 𝟙 _ =
    𝟙 _ ≫ DerivedCategory.Q.map δ at hδ
  simp only [Category.comp_id, Category.id_comp] at hδ
  have h := G.leftDerivedTensorComparison_app_app_comp_tensorHom
    ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj Q)
  rw [Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app] at h
  erw [hδ] at h
  exact h


omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
private theorem ordinaryMonoidal_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalPullMonoidal Λ f = CondensedRing.monoidal_upperStar Λ f := by
  apply Functor.Monoidal.toOplaxMonoidal_injective
  unfold internalPullMonoidal
  exact totalInternalOplax_eq Λ f

private theorem delta_model {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalDelta Λ f =
      (letI := CondensedRing.monoidal_upperStar Λ f
       (CondensedRing.upperStar Λ f).leftDerivedTensorComparison) := by
  unfold internalDelta
  rw [ordinaryMonoidal_eq Λ f]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem internal_pair {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    ((internalDelta Λ f).app (DerivedCategory.Q.obj A)).app (DerivedCategory.Q.obj B) ≫
      ResolutionConjugation.cInternal Λ f A B =
    ResolutionConjugation.aInternal Λ f A B ≫
      DerivedCategory.Q.map (actualInternalTotalIso Λ f A B).hom := by
  letI := CondensedRing.monoidal_upperStar Λ f
  rw [delta_model, actualInternalTotalIso_hom, totalInternalOplax_eq]
  simpa only [ResolutionConjugation.cInternal, ResolutionConjugation.aInternal,
    ResolutionConjugation.eta, internalQTensorArrow,
    internalDerivedPullback, internalDerivedPullFunctor,
    internalLocalizationFunctor, comparisonSource,
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app, Category.assoc] using
    cochain_tensor_comparison (CondensedRing.upperStar Λ f) A B



end CoreModels
end NativeModels

set_option allowUnsafeReducibility true in
attribute [local irreducible] Functor.Monoidal.toLaxMonoidal
  Functor.Monoidal.toOplaxMonoidal Mod.monoidalCategoryStruct

attribute [local irreducible] tensorComparison qTensor totalComparison tensor
  ResolvingOplaxConstraints.TensorFunctorTransport.tensorFunctor
  actualTensor actualUnit regular input output actualPath cochainPath
  actualComparisonIso derivedPullComparison
  CategoryTheory.Localization.Monoidal.tensorBifunctor
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.leftDerivedTensorComparison
  CategoryTheory.Functor.leftDerivedFunctorCounit
  internalPullMonoidal CondensedRing.monoidal_upperStar

set_option allowUnsafeReducibility true in
attribute [local irreducible] HomologicalComplex.mapBifunctor
  Functor.mapBifunctorHomologicalComplex





set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem actual_conjugation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    (derivedEquivalence Λ X).functor.map (((internalDelta Λ f).app M).app N) ≫
      (tensorComparison Λ X).hom.app
        ((internalDerivedPullback Λ f).obj M, (internalDerivedPullback Λ f).obj N) ≫
      (tensor Λ X).map (Prod.mkHom ((derivedPullComparison Λ f).hom.app M)
        ((derivedPullComparison Λ f).hom.app N)) =
    (derivedPullComparison Λ f).hom.app (M ⊗ N) ≫
      (derivedPullback Λ f).map ((tensorComparison Λ Y).hom.app (M, N)) ≫
      actualTensor Λ f ((derivedEquivalence Λ Y).functor.obj M)
        ((derivedEquivalence Λ Y).functor.obj N) := by
  have h := genericSquare_hom
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y))
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
    (derivedEquivalence Λ Y) (derivedEquivalence Λ X).functor
    (internalDerivedPullback Λ f) (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
    (tensorComparison Λ Y) (tensorComparison Λ X) (derivedPullComparison Λ f)
    (internalTensorIso Λ f) (actualComparisonIso Λ f)
    (genericSquare_eq _ _ _ _ _ _ _ _ _ _ _ _ _ (by unfold actualComparisonIso; rfl)) M N
  simp only [internalTensorIso_hom, actualComparisonIso_hom] at h
  exact h

private theorem map_pair_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C × D ⥤ E) {A B C' : C} {X Y Z : D}
    (a : A ⟶ B) (b : B ⟶ C') (c : X ⟶ Y) (d : Y ⟶ Z) :
    F.map (Prod.mkHom (a ≫ b) (c ≫ d)) =
      F.map (Prod.mkHom a c) ≫ F.map (Prod.mkHom b d) :=
  F.map_comp (Prod.mkHom a c) (Prod.mkHom b d)

private theorem actualComparison_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (modules Λ Y)) :
    (actualComparison Λ f).app (M, N) = actualTensor Λ f M N := by
  unfold actualComparison
  rfl

private theorem extend_conjugation
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (S : C × C ⥤ C) (T : D × D ⥤ D)
    (μ : S ⋙ L ⟶ (L.prod L) ⋙ T)
    {A B A' B' P Q R : C} {I O : D}
    (δ : I ⟶ O) (out : O ⟶ T.obj (L.obj A, L.obj B))
    (a : I ⟶ L.obj R) (b : R ⟶ S.obj (A, B))
    (x : A ⟶ A') (y : B ⟶ B') (s : A' ⟶ P) (t : B' ⟶ Q)
    (h : δ ≫ out = a ≫ L.map b ≫ μ.app (A, B)) :
    δ ≫ (out ≫ T.map (Prod.mkHom (L.map x) (L.map y))) ≫
        T.map (Prod.mkHom (L.map s) (L.map t)) =
      a ≫ L.map (b ≫ S.map (Prod.mkHom x y)) ≫
        L.map (S.map (Prod.mkHom s t)) ≫ μ.app (P, Q) := by
  have h₀ := μ.naturality (Prod.mkHom x y)
  change L.map (S.map (Prod.mkHom x y)) ≫ μ.app (A', B') =
    μ.app (A, B) ≫ T.map (Prod.mkHom (L.map x) (L.map y)) at h₀
  have h₁ := μ.naturality (Prod.mkHom s t)
  change L.map (S.map (Prod.mkHom s t)) ≫ μ.app (P, Q) =
    μ.app (A', B') ≫ T.map (Prod.mkHom (L.map s) (L.map t)) at h₁
  have hn : μ.app (A, B) ≫ T.map (Prod.mkHom (L.map x) (L.map y)) ≫
        T.map (Prod.mkHom (L.map s) (L.map t)) =
      L.map (S.map (Prod.mkHom x y)) ≫ L.map (S.map (Prod.mkHom s t)) ≫
        μ.app (P, Q) := by
    rw [← Category.assoc, ← h₀, Category.assoc, ← h₁]
  calc
    _ = (δ ≫ out) ≫ T.map (Prod.mkHom (L.map x) (L.map y)) ≫
        T.map (Prod.mkHom (L.map s) (L.map t)) := by simp only [Category.assoc]
    _ = (a ≫ L.map b ≫ μ.app (A, B)) ≫
        T.map (Prod.mkHom (L.map x) (L.map y)) ≫
        T.map (Prod.mkHom (L.map s) (L.map t)) := by rw [h]
    _ = a ≫ L.map b ≫ L.map (S.map (Prod.mkHom x y)) ≫
        L.map (S.map (Prod.mkHom s t)) ≫ μ.app (P, Q) := by
      simpa only [Category.assoc] using congrArg (fun z ↦ a ≫ L.map b ≫ z) hn
    _ = _ := by rw [Functor.map_comp]; simp only [Category.assoc]

private theorem conjugation_on_models {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ)
    (P Q : CochainComplex (modules Λ Y) ℤ)
    (σ : (totalSectionEquivalence Λ Y).obj A ≅ P)
    (τ : (totalSectionEquivalence Λ Y).obj B ≅ Q) :
    (derivedEquivalence Λ X).functor.map
        (((internalDelta Λ f).app (DerivedCategory.Q.obj A)).app (DerivedCategory.Q.obj B)) ≫
      ResolutionConjugation.kTensor Λ f A B ≫
      (tensor Λ X).map (Prod.mkHom
        ((derivedPullback Λ f).map (DerivedCategory.Q.map σ.hom))
        ((derivedPullback Λ f).map (DerivedCategory.Q.map τ.hom))) =
    ResolutionConjugation.jTensor Λ f A B ≫
      (derivedPullback Λ f).map ((tensor Λ Y).map
        (Prod.mkHom (DerivedCategory.Q.map σ.hom) (DerivedCategory.Q.map τ.hom))) ≫
      actualTensor Λ f (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) := by
  have h := extend_conjugation (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
    (actualComparison Λ f)
    ((derivedEquivalence Λ X).functor.map
      (((internalDelta Λ f).app (DerivedCategory.Q.obj A)).app (DerivedCategory.Q.obj B)))
    ((tensorComparison Λ X).hom.app
        ((internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj A),
          (internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj B)) ≫
      (tensor Λ X).map (Prod.mkHom
        ((derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj A))
        ((derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj B))))
    ((derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj A ⊗ DerivedCategory.Q.obj B))
    ((tensorComparison Λ Y).hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B))
    (sectionLocalizationComparison Λ Y A).hom (sectionLocalizationComparison Λ Y B).hom
    (DerivedCategory.Q.map σ.hom) (DerivedCategory.Q.map τ.hom)
    (by simpa only [actualComparison_app, Category.assoc] using
      actual_conjugation Λ f (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B))
  simpa only [ResolutionConjugation.kTensor, ResolutionConjugation.jTensor,
    derivedPullSquare, cochainLocalizationIso, derivedSectionTensorIso,
    actualComparison_app, Category.assoc] using h



private theorem transport_square {C : Type*} [Category C]
    {I O Z V S T U W : C}
    (δ : I ⟶ O) (ai : I ⟶ Z) (ci : O ⟶ V) (bi : Z ⟶ V)
    (j : I ⟶ S) (k : O ⟶ T) (dz : Z ⟶ U) (dout : V ⟶ W)
    (a : S ⟶ U) (c : T ⟶ W) (b : U ⟶ W) (μ : S ⟶ T)
    (hd : δ ≫ k = j ≫ μ) (ha : ai ≫ dz = j ≫ a)
    (hc : ci ≫ dout = k ≫ c) (hb : bi ≫ dout = dz ≫ b)
    (hi : δ ≫ ci = ai ≫ bi) : j ≫ μ ≫ c = j ≫ a ≫ b := by
  calc
    j ≫ μ ≫ c = δ ≫ k ≫ c := by rw [← Category.assoc, ← hd, Category.assoc]
    _ = δ ≫ ci ≫ dout := by rw [hc]
    _ = ai ≫ bi ≫ dout := by rw [← Category.assoc, hi, Category.assoc]
    _ = ai ≫ dz ≫ b := by rw [hb]
    _ = j ≫ a ≫ b := by rw [← Category.assoc, ha, Category.assoc]

private theorem transport_square_cancel {C : Type*} [Category C]
    {I O Z V J S K T Z' U V' W : C}
    (δ : I ⟶ O) (ai : I ⟶ Z) (ci : O ⟶ V) (bi : Z ⟶ V)
    (j₁ : I ⟶ J) (j₂ : J ⟶ S) (k₁ : O ⟶ K) (k₂ : K ⟶ T)
    (z₁ : Z ⟶ Z') (z₂ : Z' ⟶ U) (w₁ : V ⟶ V') (w₂ : V' ⟶ W)
    (a : S ⟶ U) (c : T ⟶ W) (b : U ⟶ W) (μ : S ⟶ T)
    [Epi j₁] [Epi j₂]
    (hd : δ ≫ k₁ ≫ k₂ = j₁ ≫ j₂ ≫ μ)
    (ha : ai ≫ z₁ ≫ z₂ = j₁ ≫ j₂ ≫ a)
    (hc : ci ≫ w₁ ≫ w₂ = k₁ ≫ k₂ ≫ c)
    (hb : bi ≫ w₁ ≫ w₂ = z₁ ≫ z₂ ≫ b)
    (hi : δ ≫ ci = ai ≫ bi) : μ ≫ c = a ≫ b := by
  apply (cancel_epi (j₁ ≫ j₂)).1
  have h := transport_square δ ai ci bi (j₁ ≫ j₂) (k₁ ≫ k₂)
    (z₁ ≫ z₂) (w₁ ≫ w₂) a c b μ
    (by simpa only [Category.assoc] using hd)
    (by simpa only [Category.assoc] using ha)
    (by simpa only [Category.assoc] using hc)
    (by simpa only [Category.assoc] using hb) hi
  simpa only [Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pair_equation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory) :
    actualPath Λ f P.obj Q.obj = cochainPath Λ f P.obj Q.obj := by
  let E := (equivalence Λ Y).mapHomologicalComplex (.up ℤ)
  let A := E.inverse.obj P.obj
  let B := E.inverse.obj Q.obj
  let σ := E.counitIso.app P.obj
  let τ := E.counitIso.app Q.obj
  have hs := (ResolutionConjugation.section_resolution_conjugation_identities Λ f).the project server
    P.obj Q.obj P.property Q.property
  have hsub := hs.2.2
  change ResolutionConjugation.SubstitutionEquations Λ f A B P.obj Q.obj σ τ at hsub
  unfold ResolutionConjugation.SubstitutionEquations at hsub
  obtain ⟨_, ha, hc, hb⟩ := hsub
  have hjT : IsIso (ResolutionConjugation.jTensor Λ f A B) := by
    unfold ResolutionConjugation.jTensor
    infer_instance
  have hδ := conjugation_on_models Λ f A B P.obj Q.obj σ τ
  have hi := congrArg ((derivedEquivalence Λ X).functor.map) (internal_pair Λ f A B)
  simp only [Functor.map_comp] at hi
  have hg := transport_square_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hδ ha hc hb hi
  simp only [actualPath, cochainPath, ResolutionConjugation.aSection,
    ResolutionConjugation.cSection, ResolutionConjugation.epsilon, qTensorArrow,
    input, output] at hg ⊢
  exact hg


private theorem e_eq_regular (T : Scheme.{u}) :
    ResolutionConjugation.e Λ T = (regular Λ T).hom := by
  unfold ResolutionConjugation.e regular
    cochainUnitComparison
  rfl

private theorem invert_prefix {C : Type*} [Category C] {A B E D : C}
    (a : A ≅ B) (b : B ≅ E) (u : A ⟶ D) (v : E ⟶ D)
    (h : u = a.hom ≫ b.hom ≫ v) : b.inv ≫ a.inv ≫ u = v := by
  rw [h]
  simp only [Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unit_equation {X Y : Scheme.{u}} (f : X ⟶ Y) :
    actualUnit Λ f =
      (pullback Λ f).mapDerivedCategoryFactors.hom.app
          (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ≫
        DerivedCategory.Q.map (sectionTotalUnit Λ f) := by
  have h := (ResolutionConjugation.section_resolution_conjugation_identities Λ f).2.1
  have hu := (internal_oplax_resolving_components Λ f).2.2
  unfold ResolutionConjugation.UnitEquation ResolutionConjugation.eta internalPullUnitArrow at h
  rw [← hu] at h
  rw [e_eq_regular Λ X, e_eq_regular Λ Y] at h
  simp only [ResolutionConjugation.epsilon, derivedPullSquare, sectionPullUnitArrow] at h
  unfold actualUnit
  exact invert_prefix
    ((derivedPullComparison Λ f).app (𝟙_ (DerivedCategory (internalModules Λ Y))))
    ((derivedPullback Λ f).mapIso (regular Λ Y)) _ _ h

attribute [local semireducible] HomologicalComplex.mapBifunctor
  Functor.mapBifunctorHomologicalComplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem totalTensor_map (T : Scheme.{u})
    {P Q P' Q' : CochainComplex (modules Λ T) ℤ} (a : P ⟶ P') (b : Q ⟶ Q') :
    (totalTensor Λ T).map (Prod.mkHom a b) = a ⊗ₘ b := by
  change (a ⊗ₘ 𝟙 Q) ≫ (𝟙 P' ⊗ₘ b) = a ⊗ₘ b
  rw [tensorHom_id, id_tensorHom]
  exact (tensorHom_def a b).symm

private theorem generic_path_naturality
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (L : C ⥤ D) (q : A ⥤ C) (r : B ⥤ D)
    (TY : C × C ⥤ C) (TX : D × D ⥤ D) (TB : B × B ⥤ B)
    (μ : TY ⋙ L ⟶ (L.prod L) ⋙ TX) (ε : q ⋙ L ⟶ F ⋙ r)
    (t : (r.prod r) ⋙ TX ⟶ TB ⋙ r)
    {P Q P' Q' : A} (a : P ⟶ P') (b : Q ⟶ Q') :
    L.map (TY.map (Prod.mkHom (q.map a) (q.map b))) ≫
        μ.app (q.obj P', q.obj Q') ≫ TX.map (Prod.mkHom (ε.app P') (ε.app Q')) ≫
        t.app (F.obj P', F.obj Q') =
      μ.app (q.obj P, q.obj Q) ≫ TX.map (Prod.mkHom (ε.app P) (ε.app Q)) ≫
        t.app (F.obj P, F.obj Q) ≫ r.map (TB.map (Prod.mkHom (F.map a) (F.map b))) := by
  let τ : (q.prod q) ⋙ TY ⋙ L ⟶ (F.prod F) ⋙ TB ⋙ r :=
    Functor.whiskerLeft (q.prod q) μ ≫
      Functor.whiskerRight (NatTrans.prod ε ε) TX ≫ Functor.whiskerLeft (F.prod F) t
  have h := τ.naturality (Prod.mkHom a b)
  simpa only [τ, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.prod, Functor.comp_map, Functor.prod_map,
    Functor.comp_obj, Functor.prod_obj, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem actual_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {P Q P' Q' : CochainComplex (modules Λ Y) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    (derivedPullback Λ f).map ((tensor Λ Y).map
        (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b))) ≫
        actualPath Λ f P' Q' =
      actualPath Λ f P Q ≫ DerivedCategory.Q.map
        ((totalSectionPull Λ f).map a ⊗ₘ (totalSectionPull Λ f).map b) := by
  have h := generic_path_naturality (totalSectionPull Λ f) (derivedPullback Λ f)
    DerivedCategory.Q DerivedCategory.Q (tensor Λ Y) (tensor Λ X) (totalTensor Λ X)
    (actualComparison Λ f) (pullback Λ f).mapDerivedCategoryFactors.hom (qTensor Λ X) a b
  simpa only [actualComparison, actualPath, output, totalTensor_map, Category.assoc] using h

private theorem inverse_square {C : Type*} [Category C]
    {A B D E : C} (a : A ⟶ B) (s : B ⟶ A) (b : D ⟶ E) (t : E ⟶ D)
    (x : A ⟶ D) (y : B ⟶ E)
    (ha : s ≫ a = 𝟙 B) (hb : b ≫ t = 𝟙 D) (h : a ≫ y = x ≫ b) :
    s ≫ x = y ≫ t := by
  calc
    s ≫ x = s ≫ x ≫ (b ≫ t) := by rw [hb, Category.comp_id]
    _ = s ≫ (a ≫ y) ≫ t := by rw [h]; simp only [Category.assoc]
    _ = y ≫ t := by
      simp only [Category.assoc] 
      rw [← Category.assoc s a (y ≫ t), ha, Category.id_comp]

private theorem inverse_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : Naturality Λ f) : InverseNaturality Λ f := by
  intro P Q P' Q' a b _ _ s t v has hsa hbt htb hab hv
  have hi : (Prod.mkHom s t) ≫
      (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) = 𝟙 _ := by
    ext <;> assumption
  apply inverse_square
    ((derivedPullback Λ f).map ((tensor Λ Y).map
      (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b))))
    ((derivedPullback Λ f).map ((tensor Λ Y).map (Prod.mkHom s t)))
    _ v _ _
  · rw [← Functor.map_comp, ← Functor.map_comp, hi,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  · exact hab
  · exact h P Q P' Q' a b

set_option allowUnsafeReducibility true in
attribute [local irreducible] HomologicalComplex.mapBifunctor
  Functor.mapBifunctorHomologicalComplex

attribute [local semireducible] tensor

private theorem constraint_hypotheses {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ResolvingOplaxConstraints.SectionHypotheses Λ f
      (actualComparison Λ f) (actualUnit Λ f) := by
  letI := ResolvingOplaxConstraints.derivedMonoidal Λ X
  letI := ResolvingOplaxConstraints.derivedMonoidal Λ Y
  refine ⟨?_, unit_equation Λ f⟩
  intro P Q
  have hp := pair_equation Λ f P Q
  unfold actualPath cochainPath at hp
  unfold input output at hp
  unfold actualComparison ResolvingOplaxConstraints.modelTensor
    ResolvingOplaxConstraints.pairModel
  exact hp


section GenericConstraints
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
  (F : A ⥤ B) (L : C ⥤ D) (q : A ⥤ C) (r : B ⥤ D)
  (s : ∀ P Q : A, q.obj P ⊗ q.obj Q ⟶ q.obj (P ⊗ Q))
  (t : ∀ P Q : B, r.obj P ⊗ r.obj Q ⟶ r.obj (P ⊗ Q))
  (ε : q ⋙ L ⟶ F ⋙ r)
  (β : ∀ P Q : A, F.obj (P ⊗ Q) ≅ F.obj P ⊗ F.obj Q)
  (unit : F.obj (𝟙_ A) ⟶ 𝟙_ B)
  (eA : 𝟙_ C ≅ q.obj (𝟙_ A)) (eB : 𝟙_ D ≅ r.obj (𝟙_ B))
  (μ : ∀ M N : C, L.obj (M ⊗ N) ⟶ L.obj M ⊗ L.obj N)
  (v : L.obj (q.obj (𝟙_ A)) ⟶ r.obj (𝟙_ B)) (P0 : ObjectProperty A)

private theorem GTripleOutput_model (P Q H : A) :
    ConstraintData.tripleOutput F L q r t ε P Q H =
      (ε.app P ⊗ₘ (ε.app Q ⊗ₘ ε.app H)) ≫
        r.obj (F.obj P) ◁ t (F.obj Q) (F.obj H) ≫
        t (F.obj P) (F.obj Q ⊗ F.obj H) := by
  dsimp only [ConstraintData.tripleOutput, ConstraintData.output, MonoidalCategory.tensor]
  rw [← Category.assoc]
  congr 1
  simpa only [Category.comp_id, MonoidalCategory.id_tensorHom, Functor.comp_obj] using
    (MonoidalCategory.tensorHom_comp_tensorHom (ε.app P) (ε.app Q ⊗ₘ ε.app H)
      (𝟙 _) (t (F.obj Q) (F.obj H))).symm

private theorem generic_constraint_normalization
    (ha : ∀ P Q H : P0.FullSubcategory,
      ResolvingOplaxConstraints.AssociativityPaths
        (F := F) (L := L) (q := q) (r := r) (s := s) (t := t) (ε := ε)
        (β := fun P Q ↦ (β P Q).hom) (μ := μ) P.obj Q.obj H.obj)
    (hu : ∀ P : P0.FullSubcategory,
      ResolvingOplaxConstraints.UnitIdentification
        (F := F) (L := L) (q := q) (r := r) (s := s) (t := t) (ε := ε)
        (β := fun P Q ↦ (β P Q).hom) (unit := unit) (eA := eA) (eB := eB)
        (μ := μ) (v := v) P.obj) :
    ConstraintData.AssociatorNormalization F L q r s t ε β μ P0 ∧
      ConstraintData.UnitorNormalization F L q r s ε β unit eA eB μ v P0 := by
  constructor
  · intro P Q H
    obtain ⟨hup, hlo, _⟩ := ha P Q H
    constructor
    · simpa only [ResolvingOplaxConstraints.upperPath,
        ResolvingOplaxConstraints.vertex3, ResolvingOplaxConstraints.rightModel,
        ResolvingOplaxConstraints.vertex0, ResolvingOplaxConstraints.leftModel,
        ConstraintData.tripleInput, ConstraintData.input, GTripleOutput_model,
      MonoidalCategory.tensor,
        MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id,
        Functor.map_comp, Category.assoc] using hup
    · simpa only [ResolvingOplaxConstraints.lowerPath,
        ResolvingOplaxConstraints.vertex3, ResolvingOplaxConstraints.rightModel,
        ResolvingOplaxConstraints.vertex0, ResolvingOplaxConstraints.leftModel,
        ConstraintData.tripleInput, ConstraintData.input, GTripleOutput_model,
      MonoidalCategory.tensor,
        MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id,
        Functor.map_comp, Category.assoc] using hlo
  · intro P
    obtain ⟨_, _, _, _, _, _, _, hl, hls, _, _, _, _, _, _, _, _, hr, hrs, _⟩ := hu P
    simpa only [ResolvingOplaxConstraints.leftUnitPath,
      ResolvingOplaxConstraints.rightUnitPath, ResolvingOplaxConstraints.regularLeft,
      ResolvingOplaxConstraints.regularRight, ResolvingOplaxConstraints.pairModel,
      ConstraintData.regularLeft, ConstraintData.regularRight, ConstraintData.input,
      MonoidalCategory.tensor,
      MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id, Category.assoc] using
        And.intro hl (And.intro hls (And.intro hr hrs))

end GenericConstraints


private theorem constraint_regular_eq (T : Scheme.{u}) :
    ResolvingOplaxConstraints.regular Λ T = regular Λ T := by
  unfold ResolvingOplaxConstraints.regular regular
  rfl

private theorem constraints_from_hypotheses {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hs : ResolvingOplaxConstraints.SectionHypotheses Λ f
      (actualComparison Λ f) (actualUnit Λ f)) :
    AssociatorNormalization Λ f ∧ UnitorNormalization Λ f := by
  letI := ResolvingOplaxConstraints.derivedMonoidal Λ X
  letI := ResolvingOplaxConstraints.derivedMonoidal Λ Y
  have h := ResolvingOplaxConstraints.section_resolving_oplax_constraint_diagrams Λ f
    (actualComparison Λ f) (actualUnit Λ f) hs
  have hh := generic_constraint_normalization
    (totalSectionPull Λ f) (derivedPullback Λ f) DerivedCategory.Q DerivedCategory.Q
    (ResolvingOplaxConstraints.modelTensor Λ Y)
    (ResolvingOplaxConstraints.modelTensor Λ X)
    (pullback Λ f).mapDerivedCategoryFactors.hom (sectionTotalIso Λ f)
    (sectionTotalUnit Λ f)
    (ResolvingOplaxConstraints.regular Λ Y) (ResolvingOplaxConstraints.regular Λ X)
    (fun M N ↦ (actualComparison Λ f).app (M, N)) (actualUnit Λ f)
    (KFlatSectionComparison.sectionResolving Λ Y)
    (fun P Q H ↦ (h.1 P Q H).2.2.2) (fun P ↦ h.2.1 P)
  unfold ResolvingOplaxConstraints.modelTensor at hh
  simpa only [AssociatorNormalization, UnitorNormalization,
    ResolvingOplaxConstraints.derivedMonoidal, ResolvingOplaxConstraints.modelTensor,
    constraint_regular_eq, actualComparison_app] using hh



private theorem constraints {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AssociatorNormalization Λ f ∧ UnitorNormalization Λ f :=
  constraints_from_hypotheses Λ f (constraint_hypotheses Λ f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem input_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory) :
    IsIso (input Λ f P.obj Q.obj) := by
  have hq :=
    (KFlatSectionComparison.section_kflat_tensor_comparison.{u, u + 1, u + 1} Λ Y).the project server.2.1
    P.obj Q.obj (Or.inl P.property.1)
  simp only [input]
  infer_instance

private theorem output_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory) :
    IsIso (output Λ f P.obj Q.obj) := by
  have hi := input_iso Λ f P Q
  have ht : IsIso (actualTensor Λ f (DerivedCategory.Q.obj P.obj)
      (DerivedCategory.Q.obj Q.obj)) := by
    rw [← actualComparisonIso_hom]
    infer_instance
  have he := pair_equation Λ f P Q
  have ho : output Λ f P.obj Q.obj =
      inv (actualTensor Λ f (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj)) ≫
        cochainPath Λ f P.obj Q.obj := by
    rw [← he]
    simp only [actualPath, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [ho]
  simp only [cochainPath]
  infer_instance
```

```lean
def regularLeftUnitor (T : Scheme.{u}) (M : DerivedCategory (modules Λ T)) :=
  (tensor Λ T).map (Prod.mkHom (regular Λ T).inv (𝟙 M)) ≫
    (@MonoidalCategoryStruct.leftUnitor _ _
      (transportedDerivedMonoidal Λ T).toMonoidalCategoryStruct M).hom
```

```lean
def regularRightUnitor (T : Scheme.{u}) (M : DerivedCategory (modules Λ T)) :=
  (tensor Λ T).map (Prod.mkHom (𝟙 M) (regular Λ T).inv) ≫
    (@MonoidalCategoryStruct.rightUnitor _ _
      (transportedDerivedMonoidal Λ T).toMonoidalCategoryStruct M).hom
```

## Users

Current source query: `tools/downstream.py Sheaf.Paper.SectionDerivedTensorData
Sheaf.Paper.SectionResolvingOplaxConstraintData --uses tensor
transportedDerivedMonoidal derivedMonoidal`. Short-name matches deliberately include
unrelated tensor uses. Additional rows include all adapted and explicitly checked
consumers. Validation results are in report.md; table membership alone is not a
claim of compiling the whole downstream closure.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.RingedForgetTensorDescent | J2 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Algebra.Homology.RingedForgetTensorTransposition | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Algebra.Homology.RingedForgetTensorTranspositionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicReindexingHom | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicReindexingTensor | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AdmissibleHomSubstitution | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AffineLineComparisonNaturality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AffineOrderedIntegrationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | H7 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AffineSpacePurityCompositionMaps | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.AffineSpaceZeroSectionConstructions | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.BasicOperationReductionAndEvaluation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.BoundedFlatTensorContinuity | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ClassicalRawLissePointFibres | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CoefFiniteHomSiteDescent | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CoefFiniteSiteHomTransport | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CoefficientEvaluationNaturality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CoefficientScalarSectionRealization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CoefficientScalarTensorData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CoefficientScalarTensorRepresentative | X2 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CoefficientTensorNormalization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactSupportLimitEquationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactSupportProjectionCoefficientChange | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactSupportProjectionFiniteStages | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactSupportProjectionFormula | N1 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactSupportScalarLimitReduction | F5 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | F6 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactSupportScalarShiftNormalization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactSupportScalarShiftStructures | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | S2 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactSupportStrictScalarMate | S3 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactificationBOrdinaryProjectionSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactificationBProjectionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactificationBProjectionDomains | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactificationBProjectionReduction | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactificationCompletedRealizationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompactificationProjectionInverse | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompleteProjectionDescentMaps | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompleteProjectionMateDescent | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompleteProjectionReductionSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConcreteOpenScalarTensorSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConcreteProjectionCoefficientCoherence | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConcreteProjectionFactorizationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConcreteProjectionReductionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConcreteProjectionReductionSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConcreteProperScalarTensorSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConstantExtensionSheetGeometry | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConstantExtensionSheetHeartData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConstantScalarTowerAdjunction | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConstantScalarTowerMates | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CoordinateTowerNormalizationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.CtfCoefficientStageSelectors | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.DerivedHomSubstitutionCoherence | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.DerivedTensorRealization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.EtaleKFlatTensorPresentation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.EtaleSystemDerivedTensorEvaluation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.EtaleSystemImageTensor | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.EtaleSystemTensorEvaluation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.EvenLineProductIntegrationMaps | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ExactProperOpenProjectionMate | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FieldExtensionSourceNormalization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FieldProjectionOpenSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FieldProjectionProperSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FieldProjectionSystemData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FieldProjectionSystemSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FieldPurityTransposeArrows | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteCoefficientAdjointData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteCoefficientSiteTensorPresentation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteHomDomainCalculus | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteHomIntrinsicTensorComposition | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteOrientationReduction | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteProjectionInputNaturality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteProjectionRefinementLeft | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteProjectionTensorSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteRingRelativeScalarComparison | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteScalarTensorData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteScalarTensorSource | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteStageNormalizedCoherence | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteTargetChangeCoherence | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteTraceDiagonalDatum | V3 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteTripleProductDefinitions | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FrameworkPbcComparisonData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FrameworkPbcIntegralComparisonLaws | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FrameworkPbcRawComparisonData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FrameworkPbcRawComparisonLaws | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.GeometricOperations | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.IntegralCoefficientModelComparison | Q1 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | D8 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.IntegralDirectImageTowerData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.IntegralProjectionCoordinateData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.IntegralProjectionSystemCoordinates | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.IntegralTowerPullTensorConstructible | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.InternalScalarMateProjection | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.InternalScalarProjectionMate | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.InternalScalarPullbackNormalizationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.LisseLatticeHeartLiftData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.LisseTensorPullbackRealizationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.NativeClosedTransposition | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.NativeOpenDerivedTensor | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.NativeWeilClosedModels | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.NativeWeilTensorLift | H3 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.NativeWeilTensorTransport | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.OpenProjectionFactorCoefficientChange | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.OperationCoefficientActionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.OrderedAffineTransposeData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.OrderedAffineTransposeSuccessor | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.OrderedLineLevelBounds | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.OrdinaryOpenScalarComposition | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.OrientationPerfectLines | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.OrientedDoubleHomCancellation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PerfectDualPairAndTateStability | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PfReductionProperOpenIdentities | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PointSignedCyclotomicAction | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PointSignedCyclotomicActionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PointSystemPowerRoosData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ProductOpenCounitNormalization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ProductOpenSupportNormalization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ProductOpenTensorProjection | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ProductOpenTensorProjectionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ProjectionFactorCoordinates | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ProjectionPurityCoordinates | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ProjectionReductionPresentation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ProjectionScalarSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ProjectionTensorCoefficientCocycles | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | D6 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.QuotientSectionTensorNormalization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RationalSmoothPurityCanonical | N4 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RationalTwistedPullbackCompositor | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RelativeKunnethConstructions | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RelativeProductCoefficientFactorSquares | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RelativeProductFactors | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ScalarLimitTensorComposition | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ScalarLimitTensorRestriction | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ScalarPullTensorCoefficientCoherence | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ScalarReductionTowerBalancing | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ScalarSourceCounitUniversal | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SectionDerivedRealization | unclaimed | All declarations and bodies retained; synchronous elaboration. |
| Sheaf.Paper.SectionDerivedRepresentativeSquare | U3 | Proved square; predicate reflexivity checked against current originals. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | G6 import, parameters and all D7/G6 declarations retained; tensor transport shared. |
| Sheaf.Paper.SectionDerivedTensorNormalization | unclaimed | Private proof uses forward API; all signatures retained. |
| Sheaf.Paper.SectionKFlatTensorComparison | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SectionOplaxTotalComparison | unclaimed | G6 proof retained; projection APIs replace constructor unfolding. |
| Sheaf.Paper.SectionRepresentativeTensorArrow | unclaimed | Current G6 retained components; no adaptation. |
| Sheaf.Paper.SectionResolutionConjugationIdentities | unclaimed | Current G6 proof and retained interfaces; no adaptation. |
| Sheaf.Paper.SectionResolvingOplaxConstraintData | unclaimed | Same transported structure through shared constant; synchronous elaboration; signatures retained. |
| Sheaf.Paper.SectionResolvingOplaxConstraintDiagrams | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SectionScalarComputationTransport | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SectionTensorConjugateComputation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SectionTensorNormalizationTransport | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SectionTensorRightComputation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SectionTotalOplaxComparisonData | unclaimed | All G6 constructions retained verbatim; four proved projection APIs added. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SfOpenReductionAdjunctionTransport | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | Q4 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SmoothPurityCompositionFactors | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SmoothPurityTowerChartData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SmoothPurityTowerGammaData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SmoothPurityTowerP1Data | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SystemCompactSupportData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SystemCompactSupportEvaluation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SystemEnrichedProjectionAdjunction | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SystemInternalHomRepresentability | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SystemProjectionChangeCompatibility | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SystemProjectionFormulaMaps | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SystemProjectionTriangleCompatibility | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SystemScalarProjectionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SystemTensorPresentationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TensorHeartSpecialization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerGeometricPurityMate | P4 | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerOrientationEvaluation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerP1CtfData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerP1DiagonalTransport | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerP1FirstTraceReordering | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerP1LevelWords | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerP1SecondTraceReordering | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerP1SingleLevelData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerP1TensorCoordinates | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerP1TriangleFactorization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerP1TriangleWords | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerP1UniformPresentation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerProjectionDomainEvaluation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TwistedPullbackLineMembership | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TwistedPullbackReductionTower | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TwistedPullbackTowerBounds | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.UniformTowerTensorClosure | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.VaryingDimensionDualizingInverse | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.VerdierCompositionMateNormalization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.VerdierPairingThreeTransposes | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.WfTateTwist | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.ZlOpenCompactSupportRestriction | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SecSmoothPurity.SupportedScalarTorInterval | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.AmbientProperOpenCalculus | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.AugmentedStrictIntegralCompletion | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefPairingCompactificationModels | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefPairingFrameNaturality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefQbarVerdierData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefQbarVerdierInternalHom | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairingData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefVerdierWeilData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CompletedProjectionExchangeData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CompositionProjectionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.EtaleOpenKFlat | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.FiniteExceptionalData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.FiniteIntrinsicBidualComparison | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.FiniteTorOrdinaryTensorComplete | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.GeneratorReductionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IndependentExpressionReductionShift | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IndependentExpressionShiftNaturality | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralBasicRealizationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralCompactificationRealizationData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | T2 | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralOpenReductionQuotientSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralRealizationAssemblyData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralTensorShiftProperties | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.OpenFactorCoherenceData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.OpenInterchangeReductionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.OpenProjectionCompletedSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.OpenProjectionOrdinaryRoos | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.OpenRoosUnitAdjunction | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.OpenTensorReductionSquare | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.PrimitiveCompletionEffectivity | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.PrimitiveQuotientAugmentations | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.ProductCompactificationIdentity | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | U1 | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.ProjectionSystemCoherence | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.RationalOperationsData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.RationalVerdierDatum | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.RationalVerdierExtension | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.RationalVerdierModels | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.RefinementProjectionCounit | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.RefinementProjectionProperComposition | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.RefinementProjectionWords | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.SemilinearOpenExternalCoherence | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.ShortWordCompletionIsomorphism | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.ShortWordIntegralDomain | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.SystemTensorLeftShiftUnique | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.SystemTensorRightShiftUnique | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.TensorExchangePresentation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.TensorQuotientAugmentationOnGood | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.TriangleProjectionSystemNormalForm | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed | Same mathematical data; no consumer adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseSheafEquivalence | unclaimed | Same mathematical data; no consumer adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor | unclaimed | Same mathematical data; no consumer adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentationTensor | unclaimed | Same mathematical data; no consumer adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same mathematical data; no consumer adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationFunctor | unclaimed | Same mathematical data; no consumer adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalarsComp | unclaimed | Same mathematical data; no consumer adaptation required. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStar | unclaimed | Same mathematical data; no consumer adaptation required. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Same mathematical data; no consumer adaptation required. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Same mathematical data; no consumer adaptation required. |
| WeilConjectures.WeilSheaf.TensorHomAdjunction | unclaimed | Same mathematical data; no consumer adaptation required. |

## Validation

The edited modules and all six requested consumers compile through lcompile.py.
The four full representative predicates were compared with current originals by
private rfl proofs; all checks passed. The theorem signature is verbatim.
Current G6 component and conjugation modules compile unchanged. See report.md
for the exact validation scope and existing warnings.

## Status

landed 20261026T222800-L-695347 2026-10-26 (merge of deliver/U3/Sheaf.Paper.SectionDerivedRepresentativeSquare)

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointSectionsFiniteReductionData
import Sheaf.Paper.PointFiniteReductionSectionAlgebra
import Sheaf.Paper.PointSectionsFiniteReductionModuleBound
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Point sections and finite coefficient reduction

Source: Stacks Tags 093J, 064L, 06YY, 06Y6 and the blueprint proof (1).
(blueprint: lem-trf-point-sections-finite-reduction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
universe u v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures
variable (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [IsAlgClosed k]

/-- Keep the standard point-sheaf localization while module localization stays small.
Source: Stacks Tag 05RU (blueprint: lem-trf-point-sections-finite-reduction). -/
local instance finiteReductionStandardDerived (n : ℕ) :
    HasDerivedCategory.{u + 2} (pointFiniteReductionSheaves k l E n) :=
  HasDerivedCategory.standard _

open SheafOfModules in
private theorem SheafOfModules.finiteReductionBoundedFlatReplacement
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r})
    (G : CochainComplex (SheafOfModules.{r}
      (derivedChangeRingIndependentCoefficients J R)) ℤ)
    (a : ℤ) [G.IsStrictlyLE a] :
    ∃ (P : CochainComplex (SheafOfModules.{r}
        (derivedChangeRingIndependentCoefficients J R)) ℤ) (p : P ⟶ G),
      P.IsStrictlyLE a ∧
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (P.X i)) ∧ QuasiIso p := by
  let A := SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive R
  have (M : A) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) := by
    have := tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (MonoidalCategory.tensorLeft M)
  have (M : A) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance
  let := hasFunctorialFlatResolution_kfi R
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  let K : CochainComplex.Minus A := ⟨G, a, inferInstance⟩
  have : (Λ.bicomplexFunctor.obj G).HasTotal (.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_isStrictlyLE _ a 0
  let P := ((ObjectProperty.flat.ι : _ ⥤ A).mapHomologicalComplex (.up ℤ)).obj
    ((Λ.bicomplexFunctor.obj G).total (.up ℤ))
  have hb : CochainComplex.IsStrictlyLE P a := by
    dsimp [P]
    infer_instance
  have hf (i : ℤ) : IsFlatOnSite (J := J) (R := R) (P.X i) := by
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X i)).symm
      (((Λ.bicomplexFunctor.obj G).total (.up ℤ)).X i).property.2
  exact ⟨P, Λ.totalπ K, hb,
    hf, inferInstance⟩

omit [IsAlgClosed k] in
private theorem finiteReductionFlatArrow (n : ℕ)
    (K : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ)
    (hK : pointFiniteReductionBoundedAbove k l E n (DerivedCategory.Q.obj K)) :
    ∃ (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ) (p : P ⟶ K),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (R := pointFiniteReductionRingSheaf k l E n) (P.X i)) ∧ QuasiIso p := by
  obtain ⟨b, hb⟩ := hK
  letI : K.IsLE b := (DerivedCategory.isLE_Q_obj_iff K b).1 hb
  obtain ⟨P, p, hP, hf, hp⟩ :=
    SheafOfModules.finiteReductionBoundedFlatReplacement
      (pointFiniteReductionRingSheaf k l E n) (K.truncLE b) b
  letI := hp
  refine ⟨P, p ≫ K.ιTruncLE b, ⟨b, (P.isStrictlyLE_iff b).1 hP⟩, hf, ?_⟩
  infer_instance

omit [IsAlgClosed k] in
private theorem finiteReductionFlatModel (n : ℕ)
    (N : (pointFiniteReductionBoundedAbove k l E n).FullSubcategory) :
    ∃ P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (R := pointFiniteReductionRingSheaf k l E n) (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ N.obj) := by
  let K := DerivedCategory.Q.objPreimage N.obj
  let e : DerivedCategory.Q.obj K ≅ N.obj := DerivedCategory.Q.objObjPreimageIso N.obj
  have hK : pointFiniteReductionBoundedAbove k l E n (DerivedCategory.Q.obj K) := by
    obtain ⟨b, hb⟩ := N.property
    letI := hb
    exact ⟨b, DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩
  obtain ⟨P, p, hb, hf, hp⟩ := finiteReductionFlatArrow k l E n K hK
  letI := hp
  exact ⟨P, hb, hf, ⟨asIso (DerivedCategory.Q.map p) ≪≫ e⟩⟩


private def finiteReductionOrdinaryIso (n j : ℕ) (h : j ≤ n) :
    pointFiniteSections k (Padic.coefficientExtensionRing l E n) ⋙
        ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (pointFiniteReductionRingMap l E n j h) ≅
      pointFiniteReductionSheafExtension k l E n j h ⋙
        pointFiniteSections k (Padic.coefficientExtensionRing l E j) :=
  ((pointFiniteReductionSectionAlgebra k l E).2 n j h).choose

private def finiteReductionMixedIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [(ModuleCat.extendScalars.{u, u, u} f).Additive] :
    (((ModuleCat.mixedTensor f).flip.map₂CochainComplex).flip.obj
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))) ≅
        (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) :=
  CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (ModuleCat.mixedTensor f).flip (ModuleCat.of S S) ≪≫
    NatIso.mapHomologicalComplex
      (Functor.isoWhiskerLeft (ModuleCat.extendScalars.{u, u, u} f)
        (MonoidalCategory.leftUnitorNatIso (ModuleCat.{u} S)) ≪≫
          Functor.rightUnitor _) (.up ℤ)

private theorem finiteReductionMixedIso_inv {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [(ModuleCat.extendScalars.{u, u, u} f).Additive]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) (y : (ModuleCat.extendScalars f).obj (C.X a)) :
    ((finiteReductionMixedIso f).inv.app C).f a y =
      (HomologicalComplex.ιMapBifunctorOrZero C
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))
        (ModuleCat.mixedTensor f).flip (.up ℤ) a 0 a)
        ((1 : S) ⊗ₜ y) := by
  simp only [finiteReductionMixedIso, Iso.trans_inv, NatTrans.comp_app,
    HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    CochainComplex.map₂HomologicalComplexFlipObjSingleIso_inv_app,
    CochainComplex.mapBifunctorSingle₂Iso_inv]
  change (HomologicalComplex.mapBifunctorFlipIso C
    ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))
    (ModuleCat.mixedTensor f).flip (.up ℤ)).hom.f a
      ((CochainComplex.mapBifunctorSingle₁Iso (ModuleCat.mixedTensor f)
        (ModuleCat.of S S) C).inv.f a
          ((1 : S) ⊗ₜ[S] y)) = _
  rw [CochainComplex.mapBifunctorSingle₁Iso_inv_f]
  have hsingle : (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (ModuleCat.of S S)).inv = 𝟙 (ModuleCat.of S S) := rfl
  erw [hsingle, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rw [HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ a 0 a (by simp)]
  have hf := HomologicalComplex.ι_mapBifunctorFlipIso_hom C
    ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))
    (ModuleCat.mixedTensor f).flip (.up ℤ) a 0 a (by simp)
  have hs : ComplexShape.σ (.up ℤ) (.up ℤ) (.up ℤ) a 0 = 1 := by
    change (a * 0).negOnePow = 1
    simp
  rw [hs, one_smul] at hf
  exact congrArg (fun g ↦ g ((1 : S) ⊗ₜ[S] y)) hf

private theorem finiteReductionMixedIso_hom {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [(ModuleCat.extendScalars.{u, u, u} f).Additive]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) (b : S)
    (y : (ModuleCat.extendScalars f).obj (C.X a)) :
    ((finiteReductionMixedIso f).hom.app C).f a
      ((HomologicalComplex.ιMapBifunctorOrZero C
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))
        (ModuleCat.mixedTensor f).flip (.up ℤ) a 0 a) (b ⊗ₜ[S] y)) = b • y := by
  let e := (finiteReductionMixedIso f).app C
  let ι := HomologicalComplex.ιMapBifunctorOrZero C
    ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))
    (ModuleCat.mixedTensor f).flip (.up ℤ) a 0 a
  have h1 : e.hom.f a (ι ((1 : S) ⊗ₜ[S] y)) = y := by
    rw [← finiteReductionMixedIso_inv f C a y]
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom e.inv_hom_id a) y
  have hb : b ⊗ₜ[S] y = b • ((1 : S) ⊗ₜ[S] y) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  change e.hom.f a (ι (b ⊗ₜ[S] y)) = _
  erw [hb, map_smul, map_smul, h1]
  rfl

private def finiteReductionComplexIso (n j : ℕ) (h : j ≤ n) :
    pointFiniteReductionSectionComplex k l E n ⋙
        pointFiniteReductionComplexTensor l E n j h ≅
      pointFiniteReductionSheafComplexTensor k l E n j h ⋙
        pointFiniteReductionSectionComplex k l E j := by
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j)
  letI : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointFiniteReductionRingMap l E n j h)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      (pointFiniteReductionRingMap l E n j h)).left_adjoint_additive
  letI : (pointFiniteReductionSheafExtension k l E n j h).Additive :=
    pointFiniteReductionSheafExtensionAdditive k l E n j h
  letI : (pointFiniteSections k (Padic.coefficientExtensionRing l E j)).Additive :=
    pointFiniteSectionsAdditive k (Padic.coefficientExtensionRing l E j)
  letI : (pointFiniteSections k (Padic.coefficientExtensionRing l E n) ⋙
      ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointFiniteReductionRingMap l E n j h)).Additive := inferInstance
  letI hzeroLeft : (pointFiniteSections k (Padic.coefficientExtensionRing l E n) ⋙
      ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointFiniteReductionRingMap l E n j h)).PreservesZeroMorphisms := inferInstance
  letI hzero : (pointFiniteReductionSheafExtension k l E n j h ⋙
      pointFiniteSections k (Padic.coefficientExtensionRing l E j)).PreservesZeroMorphisms := by
    constructor
    intro X Y
    change (pointFiniteSections k (Padic.coefficientExtensionRing l E j)).map
        ((pointFiniteReductionSheafExtension k l E n j h).map (0 : X ⟶ Y)) = _
    rw [(pointFiniteReductionSheafExtension k l E n j h).map_zero]
    exact (pointFiniteSections k (Padic.coefficientExtensionRing l E j)).map_zero _ _
  let eOrd : pointFiniteSections k (Padic.coefficientExtensionRing l E n) ⋙
      ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointFiniteReductionRingMap l E n j h) ≅
      pointFiniteReductionSheafExtension k l E n j h ⋙
        pointFiniteSections k (Padic.coefficientExtensionRing l E j) :=
    finiteReductionOrdinaryIso k l E n j h
  exact Functor.isoWhiskerLeft _
      (finiteReductionMixedIso (pointFiniteReductionRingMap l E n j h)) ≪≫
    (@NatIso.mapHomologicalComplex ℤ _ _ _ _ _ _ _ _ hzeroLeft hzero eOrd (.up ℤ))

private theorem finiteReductionComplexIso_generator (n j : ℕ) (h : j ≤ n)
    (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ) (a : ℤ)
    (b c : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))
    (x : (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj (P.X a)) :
    (((finiteReductionComplexIso k l E n j h).app P).hom.f a)
        (pointFiniteReductionTensorGenerator l E n j h
          ((pointFiniteReductionSectionComplex k l E n).obj P) a b c x) =
      (b * c) • pointFiniteReductionSectionGenerator k l E n j h (P.X a) x := by
  letI : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointFiniteReductionRingMap l E n j h)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      (pointFiniteReductionRingMap l E n j h)).left_adjoint_additive
  change (finiteReductionOrdinaryIso k l E n j h).hom.app (P.X a)
    (((finiteReductionMixedIso (pointFiniteReductionRingMap l E n j h)).app
      ((pointFiniteReductionSectionComplex k l E n).obj P)).hom.f a
        (pointFiniteReductionTensorGenerator l E n j h
          ((pointFiniteReductionSectionComplex k l E n).obj P) a b c x)) = _
  dsimp only [pointFiniteReductionTensorGenerator]
  erw [finiteReductionMixedIso_hom]
  letI := (pointFiniteReductionRingMap l E n j h).toAlgebra
  change (finiteReductionOrdinaryIso k l E n j h).hom.app (P.X a)
    ((b * c) ⊗ₜ[_, pointFiniteReductionRingMap l E n j h] x) = _
  exact ((pointFiniteReductionSectionAlgebra k l E).2 n j h).choose_spec (P.X a) (b * c) x

attribute [local irreducible] pointFiniteReductionSheafExistence pointFiniteReductionSheafModel

omit [IsAlgClosed k] in
private theorem finiteReductionSheafCounitIso (n j : ℕ) (h : j ≤ n)
    (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ)
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pointFiniteReductionRingSheaf k l E n) (P.X i)) :
    IsIso (pointFiniteReductionSheafCounit k l E n j h P) := by
  obtain ⟨b, hb⟩ := hb
  letI : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 hb
  have hk := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (pointFiniteReductionRingSheaf k l E n) P b hf
  letI := (pointFiniteReductionSheafModel k l E n j h).computes P hk
  dsimp only [pointFiniteReductionSheafCounit]
  apply IsIso.comp_isIso'
  · infer_instance
  apply IsIso.comp_isIso'
  · exact (pointFiniteReductionSheafModel k l E n j h).computes P hk
  apply IsIso.comp_isIso'
  · exact (DerivedCategory.Qh.mapIso
      (((pointFiniteReductionSheafExtension k l E n j h).mapHomotopyCategoryFactors
        (.up ℤ)).app P)).isIso_hom
  exact ((DerivedCategory.quotientCompQhIso
    (pointFiniteReductionSheaves k l E j)).app
      (((pointFiniteReductionSheafExtension k l E n j h).mapHomologicalComplex
        (.up ℤ)).obj P)).isIso_hom

private theorem finiteReductionModuleCounitIso (n j : ℕ) (h : j ≤ n)
    (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ)
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pointFiniteReductionRingSheaf k l E n) (P.X i)) :
    IsIso ((pointFiniteReductionModuleCounit l E n j h).app
      ((pointFiniteReductionSectionComplex k l E n).obj P)) := by
  let C := (pointFiniteReductionSectionComplex k l E n).obj P
  obtain ⟨b, hb⟩ := hb
  have hC : C.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).map_isZero (hb i hi)
  letI := hC
  have hk : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat C b (fun i ↦
      (ModuleCat.flat_iff_flat _).2 ((pointFiniteReductionSectionAlgebra k l E).1
        n (P.X i) (hf i)))
  exact (DerivedCategory.exists_derivedTensor_second_factor_functor
    (pointFiniteReductionRingMap l E n j h)).2.choose_spec.choose_spec.2.2.1
      (pointFiniteReductionCoefficientComplex l E j) C hk

private def finiteReductionSheafCounitNat (n j : ℕ) (h : j ≤ n) :
    DerivedCategory.Q ⋙ pointFiniteReductionSheafTensor k l E n j h ⟶
      pointFiniteReductionSheafComplexTensor k l E n j h ⋙ DerivedCategory.Q :=
  Functor.whiskerRight
      (DerivedCategory.quotientCompQhIso (pointFiniteReductionSheaves k l E n)).inv _ ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
      (pointFiniteReductionSheafEpsilon k l E n j h) ≫
    Functor.whiskerRight
      ((pointFiniteReductionSheafExtension k l E n j h).mapHomotopyCategoryFactors
        (.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerLeft (pointFiniteReductionSheafComplexTensor k l E n j h)
      (DerivedCategory.quotientCompQhIso (pointFiniteReductionSheaves k l E j)).hom

private def finiteReductionAlpha (n j : ℕ) (h : j ≤ n)
    (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ)
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pointFiniteReductionRingSheaf k l E n) (P.X i)) :
    (pointFiniteReductionModuleTensor l E n j h).obj
        ((pointFiniteReductionSections k l E n).obj (DerivedCategory.Q.obj P)) ≅
      (pointFiniteReductionSections k l E j).obj
        ((pointFiniteReductionSheafTensor k l E n j h).obj (DerivedCategory.Q.obj P)) := by
  letI := finiteReductionSheafCounitIso k l E n j h P hb hf
  letI := finiteReductionModuleCounitIso k l E n j h P hb hf
  exact (pointFiniteReductionModuleTensor l E n j h).mapIso
      (pointFiniteReductionSectionFactors k l E n P) ≪≫
    asIso ((pointFiniteReductionModuleCounit l E n j h).app
      ((pointFiniteReductionSectionComplex k l E n).obj P)) ≪≫
    DerivedCategory.Q.mapIso ((finiteReductionComplexIso k l E n j h).app P) ≪≫
    (pointFiniteReductionSectionFactors k l E j
      ((pointFiniteReductionSheafComplexTensor k l E n j h).obj P)).symm ≪≫
    (pointFiniteReductionSections k l E j).mapIso
      (asIso (pointFiniteReductionSheafCounit k l E n j h P)).symm

private theorem squareComp {C : Type*} [Category* C]
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : C}
    {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {a' : Y₀ ⟶ Y₁} {b' : Y₁ ⟶ Y₂}
    {f₀ : X₀ ⟶ Y₀} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (ha : a ≫ f₁ = f₀ ≫ a') (hb : b ≫ f₂ = f₁ ≫ b') :
    (a ≫ b) ≫ f₂ = f₀ ≫ (a' ≫ b') := by
  rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]

private theorem mapSquare {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X₀ X₁ Y₀ Y₁ : C} {a : X₀ ⟶ X₁} {b : Y₀ ⟶ Y₁}
    {f₀ : X₀ ⟶ Y₀} {f₁ : X₁ ⟶ Y₁} (h : a ≫ f₁ = f₀ ≫ b) :
    F.map a ≫ F.map f₁ = F.map f₀ ≫ F.map b := by
  rw [← F.map_comp, h, F.map_comp]

private theorem inverseSquare {C : Type*} [Category* C]
    {X Y X' Y' : C} (e : X ≅ Y) (e' : X' ≅ Y')
    (f : X ⟶ X') (g : Y ⟶ Y') (h : f ≫ e'.hom = e.hom ≫ g) :
    e.inv ≫ f = g ≫ e'.inv := by
  have hh := congrArg (fun t ↦ e.inv ≫ t ≫ e'.inv) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hh

private theorem finiteReductionAlpha_naturality (n j : ℕ) (h : j ≤ n)
    {P P' : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ}
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hb' : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P'.X i))
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pointFiniteReductionRingSheaf k l E n) (P.X i))
    (hf' : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pointFiniteReductionRingSheaf k l E n) (P'.X i)) (f : P ⟶ P') :
    (finiteReductionAlpha k l E n j h P hb hf).hom ≫
        (pointFiniteReductionSheafTensor k l E n j h ⋙
          pointFiniteReductionSections k l E j).map (DerivedCategory.Q.map f) =
      (pointFiniteReductionSections k l E n ⋙
          pointFiniteReductionModuleTensor l E n j h).map (DerivedCategory.Q.map f) ≫
        (finiteReductionAlpha k l E n j h P' hb' hf').hom := by
  let L := pointFiniteReductionModuleTensor l E n j h
  let G := pointFiniteReductionSections k l E j
  let C := pointFiniteReductionSectionComplex k l E n
  let B := pointFiniteReductionSheafComplexTensor k l E n j h
  let c := pointFiniteReductionModuleCounit l E n j h
  let s := pointFiniteReductionSectionFactorsNat k l E n
  let s' := pointFiniteReductionSectionFactorsNat k l E j
  letI := finiteReductionSheafCounitIso k l E n j h P hb hf
  letI := finiteReductionSheafCounitIso k l E n j h P' hb' hf'
  let eP := asIso (pointFiniteReductionSheafCounit k l E n j h P)
  let eP' := asIso (pointFiniteReductionSheafCounit k l E n j h P')
  have hs := mapSquare L (s.hom.naturality f).symm
  have hc := (c.naturality (C.map f)).symm
  have ht := mapSquare DerivedCategory.Q
    ((finiteReductionComplexIso k l E n j h).hom.naturality f).symm
  have hs' := (s'.inv.naturality (B.map f)).symm
  have hi := inverseSquare eP eP'
    ((pointFiniteReductionSheafTensor k l E n j h).map (DerivedCategory.Q.map f))
    (DerivedCategory.Q.map (B.map f))
    ((finiteReductionSheafCounitNat k l E n j h).naturality f)
  have hi' := mapSquare G hi
  exact squareComp hs (squareComp hc (squareComp ht (squareComp hs' hi')))

private theorem finiteReductionAlpha_derived (n j : ℕ) (h : j ≤ n)
    (P P' : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ)
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hb' : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P'.X i))
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pointFiniteReductionRingSheaf k l E n) (P.X i))
    (hf' : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pointFiniteReductionRingSheaf k l E n) (P'.X i))
    (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj P') :
    (finiteReductionAlpha k l E n j h P hb hf).hom ≫
        (pointFiniteReductionSheafTensor k l E n j h ⋙
          pointFiniteReductionSections k l E j).map f =
      (pointFiniteReductionSections k l E n ⋙
          pointFiniteReductionModuleTensor l E n j h).map f ≫
        (finiteReductionAlpha k l E n j h P' hb' hf').hom := by
  let F := pointFiniteReductionSections k l E n ⋙
    pointFiniteReductionModuleTensor l E n j h
  let H := pointFiniteReductionSheafTensor k l E n j h ⋙
    pointFiniteReductionSections k l E j
  obtain ⟨S, s, hs, g, hfac⟩ := DerivedCategory.right_fac f
  have hsq : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs
  have hS : pointFiniteReductionBoundedAbove k l E n (DerivedCategory.Q.obj S) := by
    obtain ⟨b, hb⟩ := hb
    letI : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 hb
    letI : (DerivedCategory.Q.obj P).IsLE b := by
      rw [DerivedCategory.isLE_Q_obj_iff]
      infer_instance
    letI := hs
    exact ⟨b, DerivedCategory.TStructure.t.isLE_of_iso
      (asIso (DerivedCategory.Q.map s)).symm b⟩
  obtain ⟨V, q, hbV, hfV, hq⟩ := finiteReductionFlatArrow k l E n S hS
  letI := hq
  letI := hsq
  let a := q ≫ s
  let b := q ≫ g
  have ha := finiteReductionAlpha_naturality k l E n j h hbV hb hfV hf a
  have hb := finiteReductionAlpha_naturality k l E n j h hbV hb' hfV hf' b
  have hab : DerivedCategory.Q.map a ≫ f = DerivedCategory.Q.map b := by
    simp [a, b, hfac, Functor.map_comp, Category.assoc]
  apply (cancel_epi (F.map (DerivedCategory.Q.map a))).1
  change F.map (DerivedCategory.Q.map a) ≫
    (finiteReductionAlpha k l E n j h P _ hf).hom ≫ H.map f = _
  change F.map (DerivedCategory.Q.map a) ≫
    ((finiteReductionAlpha k l E n j h P _ hf).hom ≫ H.map f) =
      F.map (DerivedCategory.Q.map a) ≫ F.map f ≫
        (finiteReductionAlpha k l E n j h P' hb' hf').hom
  change (finiteReductionAlpha k l E n j h V hbV hfV).hom ≫
      H.map (DerivedCategory.Q.map a) =
    F.map (DerivedCategory.Q.map a) ≫
      (finiteReductionAlpha k l E n j h P _ hf).hom at ha
  change (finiteReductionAlpha k l E n j h V hbV hfV).hom ≫
      H.map (DerivedCategory.Q.map b) =
    F.map (DerivedCategory.Q.map b) ≫
      (finiteReductionAlpha k l E n j h P' hb' hf').hom at hb
  rw [← Category.assoc, ← ha, Category.assoc, ← H.map_comp, hab, hb,
    ← F.map_comp_assoc, hab]

private def finiteReductionDerivedIso (n j : ℕ) (h : j ≤ n) :
    (pointFiniteReductionBoundedAbove k l E n).ι ⋙
        pointFiniteReductionSections k l E n ⋙ pointFiniteReductionModuleTensor l E n j h ≅
      (pointFiniteReductionBoundedAbove k l E n).ι ⋙
        pointFiniteReductionSheafTensor k l E n j h ⋙ pointFiniteReductionSections k l E j := by
  choose P hb hf he using finiteReductionFlatModel k l E n
  let e N := (he N).some
  let F := pointFiniteReductionSections k l E n ⋙
    pointFiniteReductionModuleTensor l E n j h
  let H := pointFiniteReductionSheafTensor k l E n j h ⋙
    pointFiniteReductionSections k l E j
  exact NatIso.ofComponents
    (fun N ↦ (F.mapIso (e N)).symm ≪≫
      finiteReductionAlpha k l E n j h (P N) (hb N) (hf N) ≪≫ H.mapIso (e N))
    (by
      intro N N' f
      have hn := finiteReductionAlpha_derived k l E n j h
        (P N) (P N') (hb N) (hb N') (hf N) (hf N')
        ((e N).hom ≫ f.hom ≫ (e N').inv)
      change (finiteReductionAlpha k l E n j h (P N) (hb N) (hf N)).hom ≫
        H.map ((e N).hom ≫ f.hom ≫ (e N').inv) =
          F.map ((e N).hom ≫ f.hom ≫ (e N').inv) ≫
            (finiteReductionAlpha k l E n j h (P N') (hb N') (hf N')).hom at hn
      have hh := congrArg
        (fun t ↦ F.map (e N).inv ≫ t ≫ H.map (e N').hom) hn
      change F.map f.hom ≫
          (F.map (e N').inv ≫
            (finiteReductionAlpha k l E n j h (P N') (hb N') (hf N')).hom ≫
              H.map (e N').hom) =
        (F.map (e N).inv ≫
          (finiteReductionAlpha k l E n j h (P N) (hb N) (hf N)).hom ≫
            H.map (e N).hom) ≫ H.map f.hom
      simpa only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc,
        Iso.map_inv_hom_id_assoc, Iso.map_inv_hom_id, Category.comp_id] using hh.symm)

private theorem finiteReductionDerivedIso_app (n j : ℕ) (h : j ≤ n)
    (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ)
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pointFiniteReductionRingSheaf k l E n) (P.X i))
    (hP : pointFiniteReductionBoundedAbove k l E n (DerivedCategory.Q.obj P)) :
    (finiteReductionDerivedIso k l E n j h).hom.app ⟨DerivedCategory.Q.obj P, hP⟩ =
      (finiteReductionAlpha k l E n j h P hb hf).hom := by
  let N : (pointFiniteReductionBoundedAbove k l E n).FullSubcategory :=
    ⟨DerivedCategory.Q.obj P, hP⟩
  let m := finiteReductionFlatModel k l E n N
  let P' := m.choose
  let hb' := m.choose_spec.1
  let hf' := m.choose_spec.2.1
  let e := m.choose_spec.2.2.some
  let F := pointFiniteReductionSections k l E n ⋙
    pointFiniteReductionModuleTensor l E n j h
  let H := pointFiniteReductionSheafTensor k l E n j h ⋙
    pointFiniteReductionSections k l E j
  have hn := finiteReductionAlpha_derived k l E n j h P' P hb' hb hf' hf e.hom
  change F.map e.inv ≫ (finiteReductionAlpha k l E n j h P' hb' hf').hom ≫
    H.map e.hom = (finiteReductionAlpha k l E n j h P hb hf).hom
  change (finiteReductionAlpha k l E n j h P' hb' hf').hom ≫ H.map e.hom =
    F.map e.hom ≫ (finiteReductionAlpha k l E n j h P hb hf).hom at hn
  rw [hn, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]

/-- Natural comparison on the bounded-above derived subcategory.
Source: Steps 4--6 of the parent proof.
(blueprint: lem-trf-point-sections-finite-reduction-iso).

Proof: resolve bounded-above objects by functorial bounded-above flat complexes. Exact point
sections identify the degreewise quotient complex with sections after sheaf scalar extension.
The derived change-of-rings universal counits and localization universal property descend this
comparison to a natural isomorphism on the bounded-above subcategory.
-/
theorem point_sections_finite_reduction_iso (_hl : IsUnit (l : k)) :
    Nonempty (∀ (n j : ℕ) (_hn : 1 ≤ n) (_hj : 1 ≤ j) (hjn : j ≤ n),
      (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSections k l E n ⋙ pointFiniteReductionModuleTensor l E n j hjn ≅
        (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSheafTensor k l E n j hjn ⋙
            pointFiniteReductionSections k l E j) := by
  exact ⟨fun n j _ _ h ↦ finiteReductionDerivedIso k l E n j h⟩

/-- Boundedness and vanishing after finite coefficient reduction.
Source: Steps 4 and 7 of the parent proof.
(blueprint: lem-trf-point-sections-finite-reduction-bounded).

Proof: finite scalar extension of a bounded-above flat model remains bounded above and termwise
flat. Exact point sections preserve the resulting complexes and their homology, so the reduced
sheaf object and the module tensor object have the asserted upper vanishing bound.
-/
theorem point_sections_finite_reduction_bounded (_hl : IsUnit (l : k)) :
    ∀ (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n),
      (∀ N : (pointFiniteReductionBoundedAbove k l E n).FullSubcategory,
        pointFiniteReductionBoundedAbove k l E j
          ((pointFiniteReductionSheafTensor k l E n j hjn).obj N.obj) ∧
        ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero
          ((DerivedCategory.homologyFunctor _ q).obj
            ((pointFiniteReductionModuleTensor l E n j hjn).obj
              ((pointFiniteReductionSections k l E n).obj N.obj)))) := by
  intro n j hn hj hjn N
  clear hn hj
  obtain ⟨b, hb⟩ := N.property
  have hSheaf : pointFiniteReductionBoundedAbove k l E j
      ((pointFiniteReductionSheafTensor k l E n j hjn).obj N.obj) := by
    obtain ⟨P, hbP, hfP, ⟨eP⟩⟩ := finiteReductionFlatModel k l E n N
    let B := (pointFiniteReductionSheafComplexTensor k l E n j hjn).obj P
    obtain ⟨c, hc⟩ := hbP
    have hB : B.IsStrictlyLE c := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact (pointFiniteReductionSheafExtension k l E n j hjn).map_isZero (hc i hi)
    letI := hB
    letI : (DerivedCategory.Q.obj B).IsLE c :=
      (DerivedCategory.isLE_Q_obj_iff B c).2 inferInstance
    letI := finiteReductionSheafCounitIso k l E n j hjn P ⟨c, hc⟩ hfP
    let e : DerivedCategory.Q.obj B ≅
        (pointFiniteReductionSheafTensor k l E n j hjn).obj N.obj :=
      (asIso (pointFiniteReductionSheafCounit k l E n j hjn P)).symm ≪≫
      (pointFiniteReductionSheafTensor k l E n j hjn).mapIso eP
    exact ⟨c, DerivedCategory.TStructure.t.isLE_of_iso e c⟩
  have hsec : ((pointFiniteReductionSections k l E n).obj N.obj).IsLE b := by
    letI := hb
    let F : pointFiniteReductionSheaves k l E n ⥤ pointFiniteReductionModules l E n :=
      pointFiniteSections k (Padic.coefficientExtensionRing l E n)
    exact F.isLE_mapDerivedCategory_obj N.obj b
  have hC : (pointFiniteReductionCoefficientComplex l E j).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro q hq
    simpa [pointFiniteReductionCoefficientComplex] using
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (ModuleCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))) q (by omega))
  have hmod := DerivedCategory.isLE_derivedTensor_second_factor_obj
    (pointFiniteReductionRingMap l E n j hjn)
    (pointFiniteReductionCoefficientComplex l E j) hC
    ((pointFiniteReductionSections k l E n).obj N.obj) ⟨b, hsec⟩
  refine ⟨hSheaf, ?_⟩
  obtain ⟨c, hc⟩ := hmod
  refine ⟨c, ?_⟩
  intro q hq
  exact (DerivedCategory.isLE_iff _ c).1 hc q hq


/-- Flat-complex model, generator normalization, and counit compatibility.
Source: Steps 5, 6 and 8 of the parent proof.
(blueprint: lem-trf-point-sections-finite-reduction-complex).

Proof: apply the degreewise quotient-to-sections map to a bounded-above termwise flat complex.
The balanced tensor associator proves the pure tensor generator equation, while the universal
counits and localization factors give the displayed counit square.
-/
/- STATEMENT-DISPUTED: the previous formulation asserted normalization for every
natural isomorphism e. Multiplying the canonical comparison by a nonidentity unit
preserves naturality but changes its normalization. The repaired statement constructs
one normalized comparison, as required by the parent theorem. -/
theorem point_sections_finite_reduction_complex (_hl : IsUnit (l : k)) :
    ∃ e : ∀ (n j : ℕ) (_hn : 1 ≤ n) (_hj : 1 ≤ j) (hjn : j ≤ n),
      (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSections k l E n ⋙ pointFiniteReductionModuleTensor l E n j hjn ≅
        (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSheafTensor k l E n j hjn ⋙ pointFiniteReductionSections k l E j,
    ∀ (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n),
      ∀ (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ)
        (_hbound : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (P.X q))
        (_hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (R := pointFiniteReductionRingSheaf k l E n) (P.X q)),
      ∃ hP : pointFiniteReductionBoundedAbove k l E n (DerivedCategory.Q.obj P),
      ∃ q :
        (pointFiniteReductionComplexTensor l E n j hjn).obj
          ((pointFiniteReductionSectionComplex k l E n).obj P) ≅
        (pointFiniteReductionSectionComplex k l E j).obj
          ((pointFiniteReductionSheafComplexTensor k l E n j hjn).obj P),
      (∀ (a : ℤ) (b c : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))
        (x : (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj (P.X a)),
        q.hom.f a
          (pointFiniteReductionTensorGenerator l E n j hjn
            ((pointFiniteReductionSectionComplex k l E n).obj P) a b c x) =
          (b * c) • pointFiniteReductionSectionGenerator k l E n j hjn (P.X a) x) ∧
      (pointFiniteReductionModuleTensor l E n j hjn).map
          (pointFiniteReductionSectionFactors k l E n P).hom ≫
        (pointFiniteReductionModuleCounit l E n j hjn).app
          ((pointFiniteReductionSectionComplex k l E n).obj P) ≫
        DerivedCategory.Q.map q.hom =
      (e n j hn hj hjn).hom.app ⟨DerivedCategory.Q.obj P, hP⟩ ≫
        (pointFiniteReductionSections k l E j).map
          (pointFiniteReductionSheafCounit k l E n j hjn P) ≫
        (pointFiniteReductionSectionFactors k l E j
          ((pointFiniteReductionSheafComplexTensor k l E n j hjn).obj P)).hom := by
  refine ⟨fun n j _ _ h ↦ finiteReductionDerivedIso k l E n j h, ?_⟩
  intro n j hn hj h P hb hf
  have hP : pointFiniteReductionBoundedAbove k l E n (DerivedCategory.Q.obj P) := by
    obtain ⟨b, hb⟩ := hb
    letI : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 hb
    exact ⟨b, (DerivedCategory.isLE_Q_obj_iff P b).2 inferInstance⟩
  refine ⟨hP, (finiteReductionComplexIso k l E n j h).app P,
    finiteReductionComplexIso_generator k l E n j h P, ?_⟩
  rw [finiteReductionDerivedIso_app k l E n j h P hb hf hP]
  letI := finiteReductionSheafCounitIso k l E n j h P hb hf
  dsimp only [finiteReductionAlpha, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv]
  let G := pointFiniteReductionSections k l E j
  simp only [asIso_hom, Category.assoc]
  rw [← G.map_comp_assoc, IsIso.inv_hom_id, G.map_id, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id]


/-- Sections at an algebraically closed point commute canonically with finite reduction.
Source: blueprint `prop-trf-adic-coefficient-morphism-systems.proof.md`, Proof (1);
Stacks Tags 093J, 00HD, 064L, 06YY and 06Y6
(blueprint: lem-trf-point-sections-finite-reduction).

The tensor-generator normalization specifies the canonical comparison on every
bounded-above flat representative. It encodes the unit and successive-reduction
clauses without introducing arbitrary unit or associativity isomorphisms: for j=n
it sends x to x; for n >= j >= i both iterated and direct reductions send the class
of x to its quotient section. The universal counits transport these equalities to
D(A_i), under the usual tensor unit and associativity identifications.

Proof: every covering sieve at the final point contains its identity, so sheafification
is bijective there. The constant-section ring map is consequently an isomorphism.
The local equational criterion for flatness becomes global at the final point, and
transport of tensor products across these ring isomorphisms gives the ordinary
comparison with its pure-tensor formula. Good truncation and the total of a
functorial flat resolution produce bounded-above flat models. The site and module
K-flat criteria make both universal derived counits invertible on these models.
The ordinary comparison therefore gives an isomorphism between their derived
images. Naturality for chain maps, fractions for derived morphisms, and another
bounded-above flat replacement show independence of the model and give naturality
on the bounded-above derived subcategory. Its value on every flat model is the
explicit composite of the counits and ordinary comparison, proving the displayed
normalization. Tensoring preserves the upper bound of these models, and the
existing module tensor upper-bound theorem gives the stated homology vanishing.
-/
theorem point_sections_finite_reduction (_hl : IsUnit (l : k)) :
    ∃ e : ∀ (n j : ℕ) (_hn : 1 ≤ n) (_hj : 1 ≤ j) (hjn : j ≤ n),
      (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSections k l E n ⋙ pointFiniteReductionModuleTensor l E n j hjn ≅
        (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSheafTensor k l E n j hjn ⋙ pointFiniteReductionSections k l E j,
    ∀ (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n),
      (∀ N : (pointFiniteReductionBoundedAbove k l E n).FullSubcategory,
        pointFiniteReductionBoundedAbove k l E j
          ((pointFiniteReductionSheafTensor k l E n j hjn).obj N.obj) ∧
        ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero
          ((DerivedCategory.homologyFunctor _ q).obj
            ((pointFiniteReductionModuleTensor l E n j hjn).obj
              ((pointFiniteReductionSections k l E n).obj N.obj)))) ∧
      ∀ (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ)
        (_hbound : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (P.X q))
        (_hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (R := pointFiniteReductionRingSheaf k l E n) (P.X q)),
      ∃ hP : pointFiniteReductionBoundedAbove k l E n (DerivedCategory.Q.obj P),
      ∃ q :
        (pointFiniteReductionComplexTensor l E n j hjn).obj
          ((pointFiniteReductionSectionComplex k l E n).obj P) ≅
        (pointFiniteReductionSectionComplex k l E j).obj
          ((pointFiniteReductionSheafComplexTensor k l E n j hjn).obj P),
      (∀ (a : ℤ) (b c : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))
        (x : (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj (P.X a)),
        q.hom.f a
          (pointFiniteReductionTensorGenerator l E n j hjn
            ((pointFiniteReductionSectionComplex k l E n).obj P) a b c x) =
          (b * c) • pointFiniteReductionSectionGenerator k l E n j hjn (P.X a) x) ∧
      (pointFiniteReductionModuleTensor l E n j hjn).map
          (pointFiniteReductionSectionFactors k l E n P).hom ≫
        (pointFiniteReductionModuleCounit l E n j hjn).app
          ((pointFiniteReductionSectionComplex k l E n).obj P) ≫
        DerivedCategory.Q.map q.hom =
      (e n j hn hj hjn).hom.app ⟨DerivedCategory.Q.obj P, hP⟩ ≫
        (pointFiniteReductionSections k l E j).map
          (pointFiniteReductionSheafCounit k l E n j hjn P) ≫
        (pointFiniteReductionSectionFactors k l E j
          ((pointFiniteReductionSheafComplexTensor k l E n j hjn).obj P)).hom := by
  obtain ⟨e, hcomplex⟩ := point_sections_finite_reduction_complex k l E _hl
  have hbounded := fun (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n) ↦
    point_sections_finite_reduction_bounded k l E _hl n j hn hj hjn
  have hcomplex := fun (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n) ↦
    hcomplex n j hn hj hjn
  refine ⟨e, ?_⟩
  intro n j hn hj hjn
  exact ⟨hbounded n j hn hj hjn, hcomplex n j hn hj hjn⟩


end WeilConjectures

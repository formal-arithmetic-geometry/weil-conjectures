module

public import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalizationData
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Chain representatives for resolution normalization

Source: Stacks Project, Tags 072W, 0DVC and 09T5.
(blueprint: lem-weil-pbc-raw-restricted-resolution-cocycle).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

/-- The shifted, bounded below injective representative.
Source: Stacks Project, Tag 072W.
(blueprint: lem-weil-pbc-raw-restricted-resolution-cocycle). -/
noncomputable def normalizationShiftedResolution {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (q : ℕ) : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ⟨I.cochainComplex⟦(q : ℤ)⟧, -(q : ℤ),
    I.cochainComplex.isStrictlyGE_shift 0 (q : ℤ) (-(q : ℤ)) (by simp)⟩

/-- The shifted augmentation, with the localization shift comparison.
Source: Stacks Project, Tags 072W and 0DVC.
(blueprint: lem-weil-pbc-raw-restricted-resolution-cocycle). -/
noncomputable def normalizationShiftedAugmentation {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (q : ℕ) :
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧ ≅
      DerivedCategory.Plus.Q.obj (normalizationShiftedResolution F I q) := by
  exact DerivedCategory.Plus.ι.preimageIso
    (((DerivedCategory.Plus.ι.commShiftIso (q : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≪≫
      (shiftFunctor _ (q : ℤ)).mapIso (asIso (DerivedCategory.Q.map I.ι')) ≪≫
      ((DerivedCategory.Q.commShiftIso (q : ℤ)).app I.cochainComplex).symm)

/-- Undo the section-complex shift and evaluate the homology presheaf on the chart.
Source: Stacks Project, Tag 072W.
(blueprint: lem-weil-pbc-raw-restricted-resolution-cocycle). -/
noncomputable def normalizationResolutionCocycleIso {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) (V : S.Etale) :
    (((RawRestrictedComparison.underivedSections
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)).mapHomologicalComplex
        (.up ℤ)).obj (normalizationShiftedResolution F I q).obj).homology 0 ≅
      ((normalizationPresheafComplex f F I).homology (q : ℤ)).obj (op V) :=
  (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso
      (((RawRestrictedComparison.underivedSections
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)).mapHomologicalComplex
          (.up ℤ)).commShiftIso (q : ℤ) |>.app I.cochainComplex) ≪≫
    ((HomologicalComplex.homologyFunctor _ (.up ℤ) 0).shiftIso
      (q : ℤ) 0 (q : ℤ) (add_zero _)).app _ ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso
      ((NatIso.mapHomologicalComplex
        (normalizationSectionsIso ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))
        (.up ℤ)).app I.cochainComplex) ≪≫
    ((normalizationPresheafComplex f F I).sc (q : ℤ)).mapHomologyIso
      ((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op V))

/-- Etale restriction of the shifted injective resolution is K-injective.
Source: Stacks Project, Tags 072W and 070J.
(blueprint: lem-weil-pbc-raw-restricted-resolution-cocycle). -/
theorem normalizationShiftedResolution_restriction_isKInjective {X : Scheme.{u}}
    (W : X.Etale) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) (q : ℕ) :
    CochainComplex.IsKInjective
      (((upperStar AddCommGrpCat.{u + 1} W.hom).mapHomologicalComplex (.up ℤ)).obj
        (normalizationShiftedResolution F I q).obj) := by
  let L : CochainComplex (Sheaf W.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ :=
    normalizationRestrictionComplex W F I
  have hL : L.IsKInjective := normalizationRestrictionComplex_isKInjective W F I
  have hshift : (L⟦(q : ℤ)⟧).IsKInjective :=
    (CochainComplex.isKInjective_shift_iff L (q : ℤ)).2 hL
  exact (CochainComplex.isKInjective_iff_of_iso
    (((upperStar AddCommGrpCat.{u + 1} W.hom).mapHomologicalComplex
      (.up ℤ)).commShiftIso (q : ℤ) |>.app I.cochainComplex)).2 hshift

attribute [local instance] normalizationShiftedResolution_restriction_isKInjective

set_option backward.isDefEq.respectTransparency false in
private theorem canonical_unit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  let inj := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  let E := HomotopyCategory.KInjectives.equivalence C
  let G := inj ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hI : NatTrans.CommShift F.rightDerivedFunctorIsoKInjectives.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  have hinv (Y : DerivedCategory C) :
      F.rightDerivedFunctorIsoKInjectives.inv.app Y =
        F.rightDerivedFunctorUnit.app (inj.obj (E.inverse.obj Y)) ≫
          F.rightDerivedFunctor.map (E.counit.app Y) := by
    simp [Functor.rightDerivedFunctorIsoKInjectives, inj, E]
  have heq : Functor.whiskerLeft inj F.rightDerivedFunctorUnit =
      (Functor.leftUnitor G).inv ≫ Functor.whiskerRight E.unitIso.hom G ≫
        (Functor.associator E.functor E.inverse G).hom ≫
        Functor.whiskerLeft E.functor F.rightDerivedFunctorIsoKInjectives.inv ≫
        (Functor.associator inj DerivedCategory.Qh F.rightDerivedFunctor).hom := by
    ext X
    have hn := F.rightDerivedFunctorUnit.naturality (inj.map (E.unit.app X))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.leftUnitor_inv_app, hinv]
    dsimp only [G, E, inj] at hn ⊢
    simp only [Category.id_comp, Category.assoc]
    rw [← Category.assoc]
    erw [hn]
    erw [Category.comp_id]
    simp only [Functor.comp_map, Category.assoc]
    change _ = _ ≫ F.rightDerivedFunctor.map (E.functor.map (E.unit.app X)) ≫
      F.rightDerivedFunctor.map (E.counit.app (E.functor.obj X))
    rw [← Functor.map_comp]
    erw [E.functor_unit_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have : NatTrans.CommShift (Functor.whiskerLeft inj F.rightDerivedFunctorUnit) ℤ := by
    rw [heq]
    dsimp only [G, E, inj]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
  let J := E.inverse.obj (DerivedCategory.Qh.obj K)
  obtain ⟨f, hf⟩ := (J.property.map_bijective_of_isTriangulated DerivedCategory.Qh
    K).surjective
      (E.counitIso.inv.app (DerivedCategory.Qh.obj K))
  refine ⟨J, f, ?_⟩
  rw [Functor.comp_map, hf]
  infer_instance

@[irreducible] private noncomputable def restrictionUnit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : D ⥤ E) [R.Additive] :
    (L ⋙ R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ L.mapDerivedCategory ⋙ R.rightDerivedFunctor :=
  (Functor.isoWhiskerRight
    (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ R)) (.up ℤ)).symm
    DerivedCategory.Q).hom ≫
  (Functor.associator (L.mapHomologicalComplex (.up ℤ))
    (R.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q).hom ≫
  Functor.whiskerLeft (L.mapHomologicalComplex (.up ℤ))
    ((Functor.isoWhiskerLeft (R.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso E)).inv ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (R.mapHomotopyCategoryFactors (.up ℤ))
        DerivedCategory.Qh).inv ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (HomotopyCategory.quotient _ _) R.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso D)
        R.rightDerivedFunctor).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight L.mapDerivedCategoryFactors.inv R.rightDerivedFunctor ≫
    (Functor.associator _ _ _).hom

@[irreducible] private noncomputable def restrictionComparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : D ⥤ E) [R.Additive] (K : CochainComplex C ℤ)
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj K)] :
    R.rightDerivedFunctor.obj (L.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj (((L ⋙ R).mapHomologicalComplex (.up ℤ)).obj K) :=
  R.rightDerivedFunctor.mapIso (L.mapDerivedCategoryFactors.app K) ≪≫
    R.rightDerivedFunctorObjQIso ((L.mapHomologicalComplex (.up ℤ)).obj K)

private theorem restrictionUnit_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : D ⥤ E) [R.Additive] (K : CochainComplex C ℤ)
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj K)] :
    (restrictionUnit L R).app K = (restrictionComparison L R K).inv := by
  have hc : (Functor.mapHomologicalComplexCompIso
      (Iso.refl (L ⋙ R)) (.up ℤ)).inv.app K = 𝟙 _ := by
    ext i
    simp
  simp [restrictionUnit, restrictionComparison, Functor.rightDerivedFunctorObjQIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, hc]

private theorem restrictionComparison_shift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : D ⥤ E) [R.Additive] (K : CochainComplex C ℤ) (n : ℤ)
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj K)]
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj (K⟦n⟧))] :
    let P := L.mapDerivedCategory ⋙ R.rightDerivedFunctor
    let B := (L ⋙ R).mapHomologicalComplex (.up ℤ)
    P.map ((DerivedCategory.Q.commShiftIso n).inv.app K) ≫
        (restrictionComparison L R (K⟦n⟧)).hom ≫
        DerivedCategory.Q.map ((B.commShiftIso n).hom.app K) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (B.obj K) =
      (P.commShiftIso n).hom.app (DerivedCategory.Q.obj K) ≫
        (restrictionComparison L R K).hom⟦n⟧' := by
  intro P B
  have := canonical_unit_commShift R
  have : NatTrans.CommShift (DerivedCategory.quotientCompQhIso E).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  have : NatTrans.CommShift (R.mapHomotopyCategoryFactors (.up ℤ)).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  have : NatTrans.CommShift L.mapDerivedCategoryFactors.inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  have : NatTrans.CommShift
      (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ R)) (.up ℤ)).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  have : NatTrans.CommShift (restrictionUnit L R) ℤ := by
    unfold restrictionUnit
    simp only [Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerRight_hom, Iso.symm_hom]
    infer_instance
  have h := NatTrans.shift_app_comm (restrictionUnit L R) n K
  simp only [Functor.commShiftIso_comp_hom_app, restrictionUnit_app, Category.assoc] at h
  have hp := Functor.commShiftIso_comp_hom_app L.mapDerivedCategory R.rightDerivedFunctor
    n (DerivedCategory.Q.obj K)
  rw [← hp] at h
  change DerivedCategory.Q.map ((B.commShiftIso n).hom.app K) ≫
    (DerivedCategory.Q.commShiftIso n).hom.app (B.obj K) ≫
    (restrictionComparison L R K).inv⟦n⟧' =
      (restrictionComparison L R (K⟦n⟧)).inv ≫
        P.map ((DerivedCategory.Q.commShiftIso n).hom.app K) ≫
        (P.commShiftIso n).hom.app (DerivedCategory.Q.obj K) at h
  rw [← cancel_epi (P.map ((DerivedCategory.Q.commShiftIso n).hom.app K))]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← cancel_epi (restrictionComparison L R (K⟦n⟧)).inv]
  simp only [Iso.inv_hom_id_assoc]
  rw [← reassoc_of% h]
  simp only [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem restrictionHomologyShift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : D ⥤ E) [R.Additive] (K : CochainComplex C ℤ) (n : ℤ)
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj K)]
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj (K⟦n⟧))] :
    let P := L.mapDerivedCategory ⋙ R.rightDerivedFunctor
    let B := (L ⋙ R).mapHomologicalComplex (.up ℤ)
    let H : ℤ → DerivedCategory E ⥤ E := DerivedCategory.homologyFunctor E
    let HC : ℤ → CochainComplex E ℤ ⥤ E :=
      fun k ↦ HomologicalComplex.homologyFunctor E (.up ℤ) k
    let δ (J : CochainComplex C ℤ)
        [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj J)] (k : ℤ) :=
      (H k).mapIso (restrictionComparison L R J) ≪≫
        (DerivedCategory.homologyFunctorFactors E k).app (B.obj J)
    (H 0).map (P.map ((DerivedCategory.Q.commShiftIso n).inv.app K)) ≫
        (δ (K⟦n⟧) 0).hom ≫
        (HC 0).map ((B.commShiftIso n).hom.app K) ≫
        ((HC 0).shiftIso n 0 n (add_zero _)).hom.app (B.obj K) =
      (H 0).map ((P.commShiftIso n).hom.app (DerivedCategory.Q.obj K)) ≫
        ((H 0).shiftIso n 0 n (add_zero _)).hom.app (P.obj (DerivedCategory.Q.obj K)) ≫
        (δ K n).hom := by
  intro P B H HC δ
  have hs := restrictionComparison_shift L R K n
  have hβ := (DerivedCategory.homologyFunctorFactors E 0).hom.naturality
    ((B.commShiftIso n).hom.app K)
  dsimp only [Functor.comp_map] at hβ
  have hQ := DerivedCategory.shiftMap_homologyFunctor_map_Q
    (𝟙 ((B.obj K)⟦n⟧)) 0 n (add_zero _)
  simp only [Functor.shiftMap, ShiftedHom.map] at hQ
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hQ
  have hQ' := congrArg
    (fun k ↦ k ≫ (DerivedCategory.homologyFunctorFactors E n).hom.app (B.obj K)) hQ
  simp only [Category.assoc, Iso.inv_hom_id_app] at hQ'
  erw [Category.comp_id] at hQ'
  dsimp only [δ, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [Category.assoc]
  rw [← reassoc_of% hβ]
  erw [← hQ']
  erw [← (H 0).map_comp_assoc, ← (H 0).map_comp_assoc,
    ← (H 0).map_comp_assoc]
  simp only [Category.assoc]
  erw [hs]
  simp only [Functor.map_comp, Category.assoc]
  have hn := ((H 0).shiftIso n 0 n (add_zero _)).hom.naturality
    (restrictionComparison L R K).hom
  simpa only [Functor.comp_map, Category.assoc, DerivedCategory.shift_homologyFunctor]
    using! congrArg (fun t ↦ (H 0).map
      ((P.commShiftIso n).hom.app (DerivedCategory.Q.obj K)) ≫ t ≫
        (DerivedCategory.homologyFunctorFactors E n).hom.app (B.obj K)) hn

private theorem restrictionAugmentationShift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : D ⥤ E) [R.Additive] (K : CochainComplex C ℤ) (n : ℤ)
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj K)]
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj (K⟦n⟧))]
    {A : DerivedCategory C} (a : A ⟶ DerivedCategory.Q.obj K) :
    let P := L.mapDerivedCategory ⋙ R.rightDerivedFunctor
    let B := (L ⋙ R).mapHomologicalComplex (.up ℤ)
    let H : ℤ → DerivedCategory E ⥤ E := DerivedCategory.homologyFunctor E
    let HC : ℤ → CochainComplex E ℤ ⥤ E :=
      fun k ↦ HomologicalComplex.homologyFunctor E (.up ℤ) k
    let δ (J : CochainComplex C ℤ)
        [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj J)] (k : ℤ) :=
      (H k).mapIso (restrictionComparison L R J) ≪≫
        (DerivedCategory.homologyFunctorFactors E k).app (B.obj J)
    (H 0).map (P.map (a⟦n⟧' ≫ (DerivedCategory.Q.commShiftIso n).inv.app K)) ≫
        ((H 0).mapIso (restrictionComparison L R (K⟦n⟧)) ≪≫
          (DerivedCategory.homologyFunctorFactors E 0).app
            ((R.mapHomologicalComplex (.up ℤ)).obj
              ((L.mapHomologicalComplex (.up ℤ)).obj (K⟦n⟧)))).hom ≫
        (HC 0).map ((B.commShiftIso n).hom.app K) ≫
        ((HC 0).shiftIso n 0 n (add_zero _)).hom.app (B.obj K) =
      (H 0).map ((P.commShiftIso n).hom.app A) ≫
        ((H 0).shiftIso n 0 n (add_zero _)).hom.app (P.obj A) ≫
        (H n).map (P.map a) ≫ (δ K n).hom := by
  intro P B H HC δ
  have hs := restrictionHomologyShift L R K n
  rw [P.map_comp, (H 0).map_comp]
  simp only [Category.assoc]
  erw [hs]
  rw [← (H 0).map_comp_assoc, P.commShiftIso_hom_naturality]
  simp only [Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc, DerivedCategory.shift_homologyFunctor]
    using! congrArg (fun t ↦ (H 0).map ((P.commShiftIso n).hom.app A) ≫ t ≫
      (δ K n).hom) (((H 0).shiftIso n 0 n (add_zero _)).hom.naturality (P.map a))



private theorem included_single_obj
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] (F : C) :
    DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor C 0).obj F) =
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj F) := rfl

private theorem single_augmentation
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    [HasKInjectiveResolutions D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : D ⥤ AddCommGrpCat.{u + 1}) [R.Additive] [PreservesFiniteLimits R]
    (F : C) (I : InjectiveResolution F) :
    (RawRestrictedComparison.Evaluation.singleIso L R F).hom ≫
        R.rightDerivedFunctor.map
          (DerivedCategory.Q.map (normalizationMappedAugmentation L F I)) =
      R.rightDerivedFunctor.map
        (L.mapDerivedCategory.map (DerivedCategory.Q.map I.ι') ≫
          L.mapDerivedCategoryFactors.hom.app I.cochainComplex) := by
  simp only [RawRestrictedComparison.Evaluation.singleIso, Functor.mapIso_hom,
    Iso.trans_hom, Iso.app_hom, normalizationMappedAugmentation, Functor.map_comp,
    Category.assoc]
  simp only [← Functor.map_comp]
  congr 1
  dsimp only [DerivedCategory.Plus.singleFunctorιIso,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app]
  erw [L.mapDerivedCategory.map_id, Category.id_comp, Category.id_comp]
  rw [DerivedCategory.Q.map_comp]
  have hf : (L.mapDerivedCategorySingleFunctor 0).hom.app F ≫
      DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).inv.app F) =
        L.mapDerivedCategoryFactors.hom.app
          ((CochainComplex.singleFunctor C 0).obj F) := by
    apply (cancel_epi ((L.mapDerivedCategorySingleFunctor 0).inv.app F)).1
    simp only [Iso.inv_hom_id_app_assoc]
    exact (L.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app F).symm
  rw [← Category.assoc, hf]
  exact (L.mapDerivedCategoryFactors_hom_naturality I.ι').symm

private theorem single_augmentation_homology
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    [HasKInjectiveResolutions D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : D ⥤ AddCommGrpCat.{u + 1}) [R.Additive] [PreservesFiniteLimits R]
    (F : C) (I : InjectiveResolution F) (n : ℤ)
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)] :
    let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n
    H.map (RawRestrictedComparison.Evaluation.singleIso L R F).hom ≫
      H.map (R.rightDerivedFunctor.map
        (DerivedCategory.Q.map (normalizationMappedAugmentation L F I))) ≫
      H.map (R.rightDerivedFunctorObjQIso
        ((L.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)).hom ≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u + 1} n).hom.app
        (((L ⋙ R).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) =
    H.map ((L.mapDerivedCategory ⋙ R.rightDerivedFunctor).map
      (DerivedCategory.Q.map I.ι')) ≫
      H.map (restrictionComparison L R I.cochainComplex).hom ≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u + 1} n).hom.app
        (((L ⋙ R).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) := by
  intro H
  rw [← H.map_comp_assoc, single_augmentation L R F I]
  simp only [restrictionComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Functor.comp_map, Category.assoc]

private noncomputable def shiftedResolution
    {C : Type*} [Category C] [Abelian C] {F : C} (I : InjectiveResolution F) (q : ℕ) :
    CochainComplex.Plus C :=
  ⟨I.cochainComplex⟦(q : ℤ)⟧, -(q : ℤ),
    I.cochainComplex.isStrictlyGE_shift 0 (q : ℤ) (-(q : ℤ)) (by simp)⟩

private noncomputable def shiftedAugmentation
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : C) (I : InjectiveResolution F) (q : ℕ) :
    ((DerivedCategory.Plus.singleFunctor C 0).obj F)⟦(q : ℤ)⟧ ≅
      DerivedCategory.Plus.Q.obj (shiftedResolution I q) :=
  DerivedCategory.Plus.ι.preimageIso
    (((DerivedCategory.Plus.ι.commShiftIso (q : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor C 0).obj F)) ≪≫
      (shiftFunctor _ (q : ℤ)).mapIso (asIso (DerivedCategory.Q.map I.ι')) ≪≫
      ((DerivedCategory.Q.commShiftIso (q : ℤ)).app I.cochainComplex).symm)


private theorem resolution_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    [HasKInjectiveResolutions D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : D ⥤ AddCommGrpCat.{u + 1}) [R.Additive] [PreservesFiniteLimits R]
    (F : C) (I : InjectiveResolution F) (q : ℕ)
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)]
    [CochainComplex.IsKInjective
      ((L.mapHomologicalComplex (.up ℤ)).obj (shiftedResolution I q).obj)]
    [IsIso (DerivedCategory.Q.map (normalizationMappedAugmentation L F I))]
    {Y : AddCommGrpCat.{u + 1}}
    (e : (((L ⋙ R).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology
      (q : ℤ) ≅ Y) :
    let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1}
    let HC := fun k ↦ HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) k
    let B := (L ⋙ R).mapHomologicalComplex (.up ℤ)
    (RawRestrictedComparison.Evaluation.shiftIso L R q F).hom ≫
      ((H (q : ℤ)).mapIso
        (R.rightDerivedFunctor.mapIso
          (asIso (DerivedCategory.Q.map (normalizationMappedAugmentation L F I))) ≪≫
          R.rightDerivedFunctorObjQIso
            ((L.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)) ≪≫
        (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u + 1} (q : ℤ)).app
          ((R.mapHomologicalComplex (.up ℤ)).obj
            ((L.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)) ≪≫ e).hom =
    (RawRestrictedComparison.Evaluation.functor L R ⋙ H 0).map
      (shiftedAugmentation F I q).hom ≫
      ((H 0).mapIso
        (R.rightDerivedFunctor.mapIso
          (L.mapDerivedCategoryFactors.app (shiftedResolution I q).obj) ≪≫
          R.rightDerivedFunctorObjQIso
            ((L.mapHomologicalComplex (.up ℤ)).obj (shiftedResolution I q).obj)) ≪≫
        (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u + 1} 0).app
          ((R.mapHomologicalComplex (.up ℤ)).obj
            ((L.mapHomologicalComplex (.up ℤ)).obj (shiftedResolution I q).obj))).hom ≫
      ((HC 0).mapIso ((B.commShiftIso (q : ℤ)).app I.cochainComplex) ≪≫
        ((HC 0).shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _)).app (B.obj I.cochainComplex) ≪≫
        e).hom := by
  intro H HC B
  let P := L.mapDerivedCategory ⋙ R.rightDerivedFunctor
  have : CochainComplex.IsKInjective
      ((L.mapHomologicalComplex (.up ℤ)).obj (I.cochainComplex⟦(q : ℤ)⟧)) :=
    inferInstanceAs (CochainComplex.IsKInjective
      ((L.mapHomologicalComplex (.up ℤ)).obj (shiftedResolution I q).obj))
  have hs := restrictionAugmentationShift L R I.cochainComplex (q : ℤ)
    (DerivedCategory.Q.map I.ι')
  have hbase := single_augmentation_homology L R F I (q : ℤ)
  have he := congrArg (fun k ↦ (H 0).map
    (P.map ((DerivedCategory.Plus.ι.commShiftIso (q : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj F))) ≫ k ≫ e.hom) hs.symm
  simp only [RawRestrictedComparison.Evaluation.shiftIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, asIso_hom, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hbase]
  simpa only [shiftedAugmentation, shiftedResolution, Functor.comp_map,
    Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, asIso_hom,
    RawRestrictedComparison.Evaluation.functor, Functor.commShiftIso_comp_hom_app,
    Functor.map_comp, Category.assoc, included_single_obj, restrictionComparison,
    P, H, HC, B, Functor.comp_obj]
    using he


/-- The shifted resolution and restricted cohomology comparisons form a square.
Source: Stacks Project, Tag 072W, proof of lemma-higher-direct-images; Tag 03Q8.
(blueprint: lem-weil-pbc-raw-restricted-resolution-cocycle).

Proof: Write L for exact restriction to W=V times_S X and R for sections
on W. Expand normalizationRestrictedIso as H^q(R) of the restricted
augmentation, followed by the inverse right-derived unit on L(I),
homology's localization comparison, the termwise normalizationSectionsIso,
and the evaluation-homology comparison. Expand resolutionSectionsIso
at I[q] as the same three localization and derived-unit factors in
degree zero. Move the shifted augmentation across the derived-section
shift comparison by naturality. The exact-restriction localization
comparison commutes with shifts, as does the right-derived unit; hence
the two resulting composites agree after the homology shift from H^0
of a q-shift to H^q. Its naturality moves the termwise sections
comparison through the shift. These are exactly the remaining factors
in normalizationResolutionCocycleIso. Cancelling each isomorphism with
its inverse proves the displayed map equality. Every shift is the
canonical functorial shift, so there is no change of sign. The argument
includes q=0 and the empty restriction, without any reference to a raw
Hom class, a chain representative, or a higher-direct-image class. -/
theorem rawRestricted_resolution_shift_square {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) (V : S.Etale) :
    let W := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V
    let T := RawRestrictedComparison.sectionsFunctor W ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
    (RawRestrictedComparison.shiftIso f q F V).hom ≫
        (normalizationRestrictedIso f q F I V).hom =
      T.map (normalizationShiftedAugmentation F I q).hom ≫
        (RawRestrictedComparison.resolutionSectionsIso W
          (normalizationShiftedResolution F I q)).hom ≫
        (normalizationResolutionCocycleIso f q F I V).hom := by
  let W := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V
  let L : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1} :=
    upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)
  let R := Sheaf.Γ (pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}
  have : CochainComplex.IsKInjective
      ((L.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) :=
    normalizationRestrictionComplex_isKInjective W F I
  have : CochainComplex.IsKInjective
      ((L.mapHomologicalComplex (.up ℤ)).obj (shiftedResolution I q).obj) :=
    normalizationShiftedResolution_restriction_isKInjective W F I q
  have : QuasiIso (normalizationMappedAugmentation L F I) :=
    normalizationRestrictionAugmentation_quasiIso W F I
  let e := (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso
      ((NatIso.mapHomologicalComplex (normalizationSectionsIso W) (.up ℤ)).app
        I.cochainComplex) ≪≫
    (((normalizationPresheafComplex f F I).sc (q : ℤ)).mapHomologyIso
      ((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)))
  exact resolution_square L R F I q e

end AlgebraicGeometry.Etale

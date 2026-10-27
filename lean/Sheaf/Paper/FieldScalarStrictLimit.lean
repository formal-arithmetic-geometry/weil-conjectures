/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.FieldScalarStrictLimitData
import all Sheaf.CategoryTheory.RoosComparisonHorizontalCoherence
import all Sheaf.Paper.NormalizedLimitSquareCoherence
import Sheaf.CategoryTheory.StrictRoosDerivation
import Sheaf.Paper.FieldScalarOrdinaryCoordinates
import Sheaf.Paper.SmallProEtaleExactProducts
import all Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition

/-! # Canonical finite-free scalar transport of strict derived limits -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u w t v uB vB
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.RingedTensor

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

variable [hD : ∀ R : Sheaf J CommRingCat.{u},
    HasDerivedCategory.{w} (ringedSiteModules.{u} (ringSheaf R))]
  [hDT : ∀ R : Sheaf J CommRingCat.{u},
    HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R))]

open FieldScalarStrictLimit

namespace FieldScalarStrictLimit

attribute [local irreducible] roosF roosχ roosι DerivedCategory.Q
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
attribute [local irreducible] roosAdditiveComparison

section Roos
universe a b c d
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  {B : Type c} [Category.{d} B] [Abelian B] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) F)]
  [PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) F)]
  [PreservesLimitsOfShape (Discrete ℕ) F]

private def canonicalCone : roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    (projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ) ⋙ roosF :=
  NatIso.ofComponents (fun X ↦ by
    have := roosAdditiveComparison_isIso F X
    exact (asIso (roosAdditiveComparison F X) :
      (roosF ⋙ F.mapHomologicalComplex (.up ℤ)).obj X ≅
        ((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ) ⋙ roosF).obj X))
    (fun f ↦ by
      simpa only [Functor.comp_map, asIso_hom, roosTowerAction] using
        roosAdditiveComparison_natural F f)

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) F)]
  [PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) F)] in
private theorem inclusion_square (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosι X) ≫ (canonicalCone F).hom.app X =
      limit.post X.asFunctor (F.mapHomologicalComplex (.up ℤ)) ≫
        roosι (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X) := by
  have h := CategoryTheory.NormalizedLimitSquare.chain_augmentation F X
    (limit X.asFunctor) (limit.cone X.asFunctor).π
  change (F.mapHomologicalComplex (.up ℤ)).map
      (limit.lift X.asFunctor (limit.cone X.asFunctor) ≫ roosι X) ≫
        roosAdditiveComparison F X = _ at h
  rw [limit.lift_cone] at h
  erw [Category.id_comp] at h
  exact h

private theorem comparison_exists
    (LR : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (LS : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w} B)
    (rhoR : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ LR)
    (rhoS : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ LS) :
    ∃ c : ScalarStrictLimitComparison F LR LS rhoR rhoS,
      c.cone = canonicalCone F := by
  let FT := projectionPost (I := ℕᵒᵖ) F
  let FC := F.mapHomologicalComplex (.up ℤ)
  let FTC := FT.mapHomologicalComplex (.up ℤ)
  let e₁ : DerivedCategory.Q ⋙ (LR ⋙ F.mapDerivedCategory) ≅
      roosF ⋙ (FC ⋙ DerivedCategory.Q) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight rhoR.symm F.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft roosF F.mapDerivedCategoryFactors
  let e₂ : DerivedCategory.Q ⋙ (FT.mapDerivedCategory ⋙ LS) ≅
      FTC ⋙ (roosF ⋙ DerivedCategory.Q) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight FT.mapDerivedCategoryFactors LS ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft FTC rhoS.symm
  let e := e₁ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (canonicalCone F) DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫ e₂.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) (DerivedCategory.{w} B)
  let lambda := ff.preimageIso e
  have hl X : lambda.hom.app (DerivedCategory.Q.obj X) = e.hom.app X :=
    congr_app (ff.map_preimage e.hom) X
  have realizes (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      F.mapDerivedCategory.map (rhoR.hom.app X) ≫
          lambda.hom.app (DerivedCategory.Q.obj X) =
        F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
          DerivedCategory.Q.map ((canonicalCone F).hom.app X) ≫
          rhoS.hom.app (FTC.obj X) ≫ LS.map (FT.mapDerivedCategoryFactors.inv.app X) := by
    rw [hl]
    simp [e, e₁, e₂, FC, FTC, FT]
  have normalized (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      F.mapDerivedCategory.map ((roosDerivedUnit rhoR).app X) ≫
          lambda.hom.app (DerivedCategory.Q.obj X) =
        F.mapDerivedCategoryFactors.hom.app (limit X.asFunctor) ≫
          DerivedCategory.Q.map (limit.post X.asFunctor FC) ≫
          (roosDerivedUnit rhoS).app (FTC.obj X) ≫
          LS.map (FT.mapDerivedCategoryFactors.inv.app X) := by
    change F.mapDerivedCategory.map (DerivedCategory.Q.map (roosι X) ≫
      rhoR.hom.app X) ≫ _ = _
    rw [Functor.map_comp, Category.assoc, realizes]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
      F.mapDerivedCategoryFactors_hom_naturality]
    simp only [Category.assoc, ← DerivedCategory.Q.map_comp]
    rw [inclusion_square]
    simp [roosDerivedUnit, roosInclusion, FC, FTC, FT, Category.assoc]
  have hprod (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      IsIso (roosProductComparison F X) := by
    dsimp only [roosProductComparison]
    infer_instance
  let := hprod
  refine ⟨{ comparison := lambda
            normalized := normalized
            beta := fun X ↦ asIso (roosProductComparison F X)
            beta_projection := ?_
            beta_transition := ?_
            cone := canonicalCone F
            cone_first := ?_
            cone_second := ?_
            cone_realizes := realizes }, rfl⟩
  · intro X n
    exact piComparison_comp_π _ _ n
  · intro X
    exact productComparison_u F X
  · intro X p
    exact comparison_fst F X p
  · intro X p
    exact comparison_snd F X p


omit [PreservesLimitsOfShape (Discrete ℕ) F] in
private theorem comparison_fac
    (LR : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (LS : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w} B)
    (rhoR : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ LR)
    (rhoS : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ LS)
    (c : ScalarStrictLimitComparison F LR LS rhoR rhoS)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    c.comparison.hom.app (DerivedCategory.Q.obj X) ≫
        LS.map ((projectionPost (I := ℕᵒᵖ) F).mapDerivedCategoryFactors.hom.app X) ≫
        rhoS.inv.app (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X) =
      F.mapDerivedCategory.map (rhoR.inv.app X) ≫
        F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
        DerivedCategory.Q.map (c.cone.hom.app X) := by
  apply (cancel_epi (F.mapDerivedCategory.map (rhoR.hom.app X))).1
  simp only [← Category.assoc]
  rw [c.cone_realizes]
  simp [Category.assoc, ← F.mapDerivedCategory.map_comp]

private theorem comparison_unit
    (F : A ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) F)]
    [PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) F)]
    (L : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (rho : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ L)
    (U : F ≅ 𝟭 A)
    (UT : projectionPost (I := ℕᵒᵖ) F ≅ 𝟭 (ℕᵒᵖ ⥤ A))
    (ht : ∀ (X : ℕᵒᵖ ⥤ A) (n : ℕᵒᵖ), (UT.hom.app X).app n = U.hom.app (X.obj n))
    (c : ScalarStrictLimitComparison F L L rho rho)
    (hc : ∀ X, c.cone.hom.app X = roosAdditiveComparison F X)
    (K : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :
    c.comparison.hom.app K ≫ L.map ((exactDerivedUnit inferInstance inferInstance UT).hom.app K) =
      (exactDerivedUnit inferInstance inferInstance U).hom.app (L.obj K) := by
  let u := exactDerivedUnit (F := F) inferInstance inferInstance U
  let ut := exactDerivedUnit (F := projectionPost (I := ℕᵒᵖ) F)
    inferInstance inferInstance UT
  let lhs : L ⋙ F.mapDerivedCategory ⟶ L :=
    c.comparison.hom ≫ Functor.whiskerRight ut.hom L
  let rhs : L ⋙ F.mapDerivedCategory ⟶ L := Functor.whiskerLeft L u.hom
  have heq : lhs = rhs := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
    intro X
    change c.comparison.hom.app (DerivedCategory.Q.obj X) ≫
      L.map (ut.hom.app (DerivedCategory.Q.obj X)) = u.hom.app (L.obj (DerivedCategory.Q.obj X))
    apply (cancel_mono (rho.inv.app X)).1
    have hut : ut.hom.app (DerivedCategory.Q.obj X) =
        (projectionPost (I := ℕᵒᵖ) F).mapDerivedCategoryFactors.hom.app X ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex UT.hom (.up ℤ)).app X) := by
      dsimp only [ut, exactDerivedUnit, Iso.trans_hom, NatTrans.comp_app]
      rw [Functor.mapDerivedCategoryIdIso_hom_app_Q_obj, Functor.mapDerivedCategoryNatIso_fac]
    have hu : u.hom.app (DerivedCategory.Q.obj (roosF.obj X)) =
        F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex U.hom (.up ℤ)).app (roosF.obj X)) := by
      dsimp only [u, exactDerivedUnit, Iso.trans_hom, NatTrans.comp_app]
      rw [Functor.mapDerivedCategoryIdIso_hom_app_Q_obj, Functor.mapDerivedCategoryNatIso_fac]
    rw [hut, Functor.map_comp]
    simp only [Category.assoc]
    have hn := rho.inv.naturality ((NatTrans.mapHomologicalComplex UT.hom (.up ℤ)).app X)
    dsimp only [Functor.comp_map] at hn
    erw [hn, reassoc_of% comparison_fac F L L rho rho c X]
    have hn' := u.hom.naturality (rho.inv.app X)
    dsimp only [Functor.comp_map, Functor.id_map] at hn'
    erw [← hn', hu]
    simp only [← DerivedCategory.Q.map_comp]
    rw [hc]
    apply congrArg (fun f ↦ F.mapDerivedCategory.map (rho.inv.app X) ≫
      F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫ f)
    apply congrArg DerivedCategory.Q.map
    have h := roosComparison_horizontal_coherence (𝟭 A) F (𝟭 A)
      ((Functor.leftUnitor F).hom ≫ U.hom) X
    have hi : roosAdditiveComparison (𝟭 A) X = 𝟙 (roosF.obj X) := by
      have hi := roosAdditiveComparison_id X
      change roosAdditiveComparison (𝟭 A) X =
        𝟙 (roosF.obj X) ≫ roosF.map (𝟙 X) at hi
      erw [roosF.map_id, Category.id_comp] at hi
      exact hi
    have hti : (NatTrans.mapHomologicalComplex
        ((Functor.whiskeringRight ℕᵒᵖ A A).map
          ((Functor.leftUnitor F).hom ≫ U.hom)) (.up ℤ)).app X =
        (NatTrans.mapHomologicalComplex UT.hom (.up ℤ)).app X := by
      ext p n
      simpa using (ht (X.X p) n).symm
    erw [hi, hti] at h
    erw [(F.mapHomologicalComplex (.up ℤ)).map_id, Category.id_comp, Category.comp_id] at h
    change roosAdditiveComparison F X ≫
      roosF.map ((NatTrans.mapHomologicalComplex UT.hom (.up ℤ)).app X) =
      (NatTrans.mapHomologicalComplex
        ((Functor.leftUnitor F).hom ≫ U.hom) (.up ℤ)).app (roosF.obj X) at h
    have hu' : (NatTrans.mapHomologicalComplex
        ((Functor.leftUnitor F).hom ≫ U.hom) (.up ℤ)).app (roosF.obj X) =
        (NatTrans.mapHomologicalComplex U.hom (.up ℤ)).app (roosF.obj X) := by
      ext p
      simp
    rw [hu'] at h
    exact h
  exact congr_app heq K

end Roos

attribute [local irreducible] tensorFunctor tensorAdjunction scalarPure

omit hD hDT in
private theorem scalar_exact {R S : Sheaf J CommRingCat.{u}}
    (a : FiniteFreeScalarArrow J R S) :
    PreservesLimitsOfSize.{0, 0} (tensorFunctor a.val) ∧
      PreservesFiniteColimits (tensorFunctor a.val) := by
  obtain ⟨d, ⟨theta⟩⟩ := a.property
  obtain ⟨phi, _, _⟩ := (fieldScalarOrdinaryCoordinates J).1 a d theta
  let U := restriction a.val
  obtain ⟨href, hlim, hcolim⟩ := scalarRestrictionProperties.{u, u, u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a.val)
  let : U.ReflectsIsomorphisms := href
  let : PreservesLimitsOfSize.{u, u} U := hlim
  let : PreservesLimitsOfSize.{0, 0} U := preservesLimitsOfSize_shrink _
  let : ReflectsLimitsOfSize.{0, 0} U := reflectsLimits_of_reflectsIsomorphisms
  let P := (Functor.const (Discrete (Fin d)) :
    ringedSiteModules.{u} (ringSheaf R) ⥤ _) ⋙ lim
  let : PreservesLimitsOfSize.{0, 0} P := inferInstance
  let : PreservesLimitsOfSize.{0, 0} (tensorFunctor a.val ⋙ U) :=
    preservesLimits_of_natIso phi.symm
  let : (tensorFunctor a.val).IsLeftAdjoint := (tensorAdjunction a.val).isLeftAdjoint
  exact ⟨preservesLimits_of_reflects_of_preserves (tensorFunctor a.val) U, inferInstance⟩

omit hD hDT in
private theorem scalar_products {R S : Sheaf J CommRingCat.{u}}
    (a : FiniteFreeScalarArrow J R S) :
    PreservesLimitsOfShape (Discrete ℕ) (tensorFunctor a.val) := by
  obtain ⟨d, ⟨theta⟩⟩ := a.property
  obtain ⟨phi, _, _⟩ := (fieldScalarOrdinaryCoordinates J).1 a d theta
  let U := restriction a.val
  obtain ⟨href, hlim, _⟩ := scalarRestrictionProperties.{u, u, u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a.val)
  let : U.ReflectsIsomorphisms := href
  let : PreservesLimitsOfSize.{u, u} U := hlim
  let : PreservesLimitsOfSize.{0, 0} U := preservesLimitsOfSize_shrink _
  let : ReflectsLimitsOfShape (Discrete ℕ) U := reflectsLimitsOfShape_of_reflectsIsomorphisms
  let P := (Functor.const (Discrete (Fin d)) :
    ringedSiteModules.{u} (ringSheaf R) ⥤ _) ⋙ lim
  let : PreservesLimitsOfShape (Discrete ℕ) P := inferInstance
  let : PreservesLimitsOfShape (Discrete ℕ) (tensorFunctor a.val ⋙ U) :=
    preservesLimitsOfShape_of_natIso phi.symm
  exact preservesLimitsOfShape_of_reflects_of_preserves (tensorFunctor a.val) U

section Composition
universe a b c d e f
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  {B : Type c} [Category.{d} B] [Abelian B] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
  {D : Type e} [Category.{f} D] [Abelian D] [HasCountableProducts D]
  [HasLimitsOfShape ℕᵒᵖ D] [HasDerivedCategory.{w} D]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ D)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) F)]
  [PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) F)]
  (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) G)]
  [PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) G)]
  (H : A ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) H)]
  [PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) H)]
  (LR : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
  (LS : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w} B)
  (LU : DerivedCategory.{w} (ℕᵒᵖ ⥤ D) ⥤ DerivedCategory.{w} D)
  (rhoR : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ LR)
  (rhoS : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ LS)
  (rhoU : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ LU)
  (cF : ScalarStrictLimitComparison F LR LS rhoR rhoS)
  (cG : ScalarStrictLimitComparison G LS LU rhoS rhoU)
  (cH : ScalarStrictLimitComparison H LR LU rhoR rhoU)
  (alpha : F ⋙ G ≅ H)
  (alphaT : projectionPost (I := ℕᵒᵖ) F ⋙ projectionPost (I := ℕᵒᵖ) G ≅
    projectionPost (I := ℕᵒᵖ) H)

private theorem comparison_path (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    G.mapDerivedCategory.map (cF.comparison.hom.app (DerivedCategory.Q.obj X)) ≫
      cG.comparison.hom.app
        ((projectionPost (I := ℕᵒᵖ) F).mapDerivedCategory.obj (DerivedCategory.Q.obj X)) ≫
      LU.map ((projectionPost (I := ℕᵒᵖ) G).mapDerivedCategory.map
        ((projectionPost (I := ℕᵒᵖ) F).mapDerivedCategoryFactors.hom.app X) ≫
        (projectionPost (I := ℕᵒᵖ) G).mapDerivedCategoryFactors.hom.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X)) ≫
      rhoU.inv.app (((projectionPost (I := ℕᵒᵖ) G).mapHomologicalComplex (.up ℤ)).obj
        (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X)) =
    G.mapDerivedCategory.map (F.mapDerivedCategory.map (rhoR.inv.app X)) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app (roosF.obj X)) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj (roosF.obj X)) ≫
      DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map (cF.cone.hom.app X) ≫
        cG.cone.hom.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X)) := by
  simp only [Functor.map_comp, Category.assoc]
  erw [← cG.comparison.hom.naturality_assoc]
  dsimp only [Functor.comp_map]
  erw [comparison_fac G LS LU rhoS rhoU cG]
  erw [← G.mapDerivedCategory.map_comp_assoc, ← G.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  erw [comparison_fac F LR LS rhoR rhoS cF]
  simp only [Functor.map_comp, Category.assoc]
  erw [G.mapDerivedCategoryFactors_hom_naturality_assoc]

private theorem comparison_comp
    (hF : ∀ X, cF.cone.hom.app X = roosAdditiveComparison F X)
    (hG : ∀ X, cG.cone.hom.app X = roosAdditiveComparison G X)
    (hH : ∀ X, cH.cone.hom.app X = roosAdditiveComparison H X)
    (ht : ∀ (X : ℕᵒᵖ ⥤ A) (n : ℕᵒᵖ),
      (alphaT.hom.app X).app n = alpha.hom.app (X.obj n))
    (K : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) :
    G.mapDerivedCategory.map (cF.comparison.hom.app K) ≫
        cG.comparison.hom.app ((projectionPost (I := ℕᵒᵖ) F).mapDerivedCategory.obj K) ≫
        LU.map ((Functor.mapDerivedCategoryCompNatIso alphaT).hom.app K) =
      (Functor.mapDerivedCategoryCompNatIso alpha).hom.app (LR.obj K) ≫
        cH.comparison.hom.app K := by
  have hc : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      (G.mapHomologicalComplex (.up ℤ)).map (cF.cone.hom.app X) ≫
        cG.cone.hom.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        roosF.map ((Functor.mapHomologicalComplexCompIsoHomOfIso alphaT) X) =
      (Functor.mapHomologicalComplexCompIsoHomOfIso alpha) (roosF.obj X) ≫
        cH.cone.hom.app X := by
    intro X
    rw [hF X, hG _, hH X]
    have ht' : Functor.mapHomologicalComplexCompIsoHomOfIso alphaT X =
        (NatTrans.mapHomologicalComplex
          ((Functor.whiskeringRight ℕᵒᵖ _ _).map alpha.hom) (.up ℤ)).app X := by
      apply HomologicalComplex.Hom.ext
      funext p
      apply NatTrans.ext
      funext n
      dsimp [Functor.mapHomologicalComplexCompIsoHomOfIso,
        Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
        NatTrans.mapHomologicalComplex]
      simpa using ht (X.X p) n
    have ha : Functor.mapHomologicalComplexCompIsoHomOfIso alpha (roosF.obj X) =
        (NatTrans.mapHomologicalComplex alpha.hom (.up ℤ)).app (roosF.obj X) := by
      apply HomologicalComplex.Hom.ext
      funext p
      simp
    rw [ht', ha]
    exact roosComparison_horizontal_coherence F G H alpha.hom X
  let lhs : LR ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶
      (projectionPost (I := ℕᵒᵖ) H).mapDerivedCategory ⋙ LU :=
    Functor.whiskerRight cF.comparison.hom G.mapDerivedCategory ≫
      Functor.whiskerLeft (projectionPost (I := ℕᵒᵖ) F).mapDerivedCategory cG.comparison.hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryCompNatIso alphaT).hom LU
  let rhs : LR ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶
      (projectionPost (I := ℕᵒᵖ) H).mapDerivedCategory ⋙ LU :=
    Functor.whiskerLeft LR (Functor.mapDerivedCategoryCompNatIso alpha).hom ≫ cH.comparison.hom
  have heq : lhs = rhs := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
    intro X
    change G.mapDerivedCategory.map (cF.comparison.hom.app (DerivedCategory.Q.obj X)) ≫
        cG.comparison.hom.app
          ((projectionPost (I := ℕᵒᵖ) F).mapDerivedCategory.obj (DerivedCategory.Q.obj X)) ≫
        LU.map ((Functor.mapDerivedCategoryCompNatIso alphaT).hom.app
          (DerivedCategory.Q.obj X)) =
      (Functor.mapDerivedCategoryCompNatIso alpha).hom.app
        (LR.obj (DerivedCategory.Q.obj X)) ≫ cH.comparison.hom.app (DerivedCategory.Q.obj X)
    apply (cancel_mono (LU.map
      ((projectionPost (I := ℕᵒᵖ) H).mapDerivedCategoryFactors.hom.app X) ≫
      rhoU.inv.app (((projectionPost (I := ℕᵒᵖ) H).mapHomologicalComplex (.up ℤ)).obj X))).1
    simp only [Category.assoc]
    rw [← LU.map_comp_assoc, Functor.mapDerivedCategoryCompNatIso_hom_app_Q]
    simp only [LU.map_comp, Category.assoc]
    have hn := rhoU.inv.naturality (Functor.mapHomologicalComplexCompIsoHomOfIso alphaT X)
    dsimp only [Functor.comp_map] at hn
    erw [hn]
    have hp := comparison_path F G LR LS LU rhoR rhoS rhoU cF cG X
    simp only [LU.map_comp, Category.assoc] at hp
    erw [reassoc_of% hp, comparison_fac H LR LU rhoR rhoU cH]
    have he := (Functor.mapDerivedCategoryCompNatIso alpha).hom.naturality (rhoR.inv.app X)
    dsimp only [Functor.comp_map] at he
    erw [← reassoc_of% he]
    erw [reassoc_of% Functor.mapDerivedCategoryCompNatIso_hom_app_Q alpha (roosF.obj X)]
    simp only [← DerivedCategory.Q.map_comp]
    apply congrArg (fun f ↦
      G.mapDerivedCategory.map (F.mapDerivedCategory.map (rhoR.inv.app X)) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app (roosF.obj X)) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj (roosF.obj X)) ≫ DerivedCategory.Q.map f)
    simpa only [Category.assoc] using hc X
  exact congr_app heq K

end Composition

private theorem finite_power_naturality
    {A : Type uB} [Category.{vB} A] [HasFiniteProducts A]
    {B : Type v} [Category B] (F : A ⥤ B) (U : B ⥤ A) (d : ℕ)
    (phi : F ⋙ U ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
    {M N : A} (f : M ⟶ N) (i : Fin d) :
    U.map (F.map f) ≫ phi.hom.app N ≫ Pi.π (fun _ : Fin d ↦ N) i =
      phi.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i ≫ f := by
  have h := congrArg (fun h ↦ h ≫
    limit.π ((Functor.const (Discrete (Fin d))).obj N) (Discrete.mk i))
      (phi.hom.naturality f)
  dsimp only [Functor.comp_map, lim_map] at h
  simp only [Category.assoc] at h
  erw [limMap_π] at h
  exact h

end FieldScalarStrictLimit

attribute [local irreducible] tensorFunctor tensorAdjunction scalarPure
attribute [local irreducible] roosF roosχ roosι DerivedCategory.Q
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
attribute [local irreducible] roosAdditiveComparison

/-- Finite-free scalar extension commutes canonically and coherently with strict total
unbounded derived inverse limits on a small model of a scheme's pro-etale site.

Source: blueprint sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.proof.md (1)
(blueprint: lem-sp-field-scalar-strict-limit).

Proof:
1. Apply lem-weil-pbc-finite-free-strict-tower-transport to the finite basis. It gives
exact scalar extension on modules and entire towers, and the canonical comparison from
ordinary limit/tensor. Exact-functor-derived-factorization computes derived tensor on
all complexes, without boundedness.
2. Pro-etale countable products are sectionwise and exact by
lem-weil-proetale-countable-products-exact. Apply lem-weil-strict-roos-comparison, using
injective-term K-injective tower resolutions, with the ordinary-limit inclusion as unit.
3. The nth projection of beta is tensor of the nth projection. Finite basis coordinates
therefore give precisely ((x_i,n)_n)_i mapped to ((x_i,n)_i)_n. The inverse regroups the
same entries. Projections show beta F(s) = s beta and hence beta F(1-s) = (1-s) beta.
Apply beta on both signed cone coordinates to obtain the natural S-linear chain iso.
4. On a resolved tower I, the cone map sends F(j_I) to j_FI beta-limit. For a target
resolution FI to J, naturality sends this to j_J lim(FI to J) beta-limit. The normalized
Roos identification is therefore exactly the derived ordinary comparison. Localization
and resolutions extend the equality to every roof of entire tower complexes. The map
contains no choice of basis and is linear in the target coefficient sheaf.
5. For R to S to U the balanced associator sends t tensor (s tensor x) to b(s)t tensor x,
with insertion-of-one inverse. Both product comparisons give (b(s)t tensor x_n)_n.
These formulas commute with restriction and the signed cone differential, so the two
actual cone maps agree. The identity unitor sends r tensor x to rx on both coordinates.
6. Localize these equal chain maps using exact-functor factorization. Conjugate by the
normalized Roos isomorphisms; the intervening rho-inverse rho pairs cancel. Naturality
moves the tower associator through the limit functor. This gives the composition and
identity equations below on the derived category of entire towers. No constructibility,
completeness, normalization or cohomological bound is used; rank zero is included.
-/
theorem fieldScalarStrictLimit (T : AlgebraicGeometry.Scheme.{t})
    (e : C ≌ T.ProEt)
    (hJ : J = e.functor.inducedTopology
      (AlgebraicGeometry.Scheme.ProEt.topology T)) :
    (∀ {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S),
      PreservesFiniteLimits (tensorFunctor a.val)) ∧
    (∀ {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S),
      PreservesFiniteColimits (tensorFunctor a.val)) ∧
    (∀ {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S),
      PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) (tensorFunctor a.val))) ∧
    (∀ {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S),
      PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) (tensorFunctor a.val))) ∧
    ∀ (hlim : ∀ {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S),
        PreservesFiniteLimits (tensorFunctor a.val))
      (hcolim : ∀ {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S),
        PreservesFiniteColimits (tensorFunctor a.val))
      (htlim : ∀ {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S),
        PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) (tensorFunctor a.val)))
      (htcolim : ∀ {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S),
        PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) (tensorFunctor a.val))),
    ∃ (L : ∀ R : Sheaf J CommRingCat.{u},
        DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u} (ringSheaf R)))
      (rho : ∀ R : Sheaf J CommRingCat.{u},
        roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ L R),
      (∀ R : Sheaf J CommRingCat.{u},
        (L R).IsRightDerivedFunctor (roosDerivedUnit (rho R))
          (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R)) (.up ℤ))) ∧
      ∃ cmp : ∀ {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S),
          @ScalarStrictLimitComparison _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (tensorFunctor a.val) _ (hlim a) (hcolim a) (htlim a) (htcolim a)
            (L R) (L S) (rho R) (rho S),
        (∀ {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S)
          (d : ℕ) (theta : (∏ᶜ fun _ : Fin d ↦ unit (ringSheaf R)) ≅
            (restriction a.val).obj (unit (ringSheaf S))),
          ∃ phi : tensorFunctor a.val ⋙ restriction a.val ≅
              Functor.const (Discrete (Fin d)) ⋙ lim,
            (∀ (M : SheafOfModules.{u} (ringSheaf R)) (V : Cᵒᵖ)
              (s : S.obj.obj V) (m : M.val.obj V) (i : Fin d),
              (phi.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i).val.app V
                  (scalarPure a.val M V s m) =
                (theta.inv ≫ Pi.π (fun _ : Fin d ↦ unit (ringSheaf R)) i).val.app V s
                  • m) ∧
            (∀ (M : SheafOfModules.{u} (ringSheaf R)) (V : Cᵒᵖ)
              (x : ((Functor.const (Discrete (Fin d)) ⋙ lim).obj M).val.obj V),
              (phi.inv.app M).val.app V x =
                ∑ i : Fin d, scalarPure a.val M V
                  ((Pi.lift (fun j : Fin d ↦ if i = j then 𝟙 _ else 0) ≫ theta.hom).val.app V
                    (@id ((unit (ringSheaf R)).val.obj V) (1 : R.obj.obj V)))
                  ((Pi.π (fun _ : Fin d ↦ M) i).val.app V x)) ∧
            ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R)) ℤ)
              (p : ℤ) (n : ℕ) (i : Fin d),
              (restriction a.val).map
                  (((cmp a).beta X).hom.f p ≫
                    (Pi.π (fun k : ℕ ↦
                      (((projectionPost (I := ℕᵒᵖ) (tensorFunctor a.val)).mapHomologicalComplex
                        (.up ℤ)).obj X).asFunctor.obj (op k)) n).f p) ≫
                    phi.hom.app ((X.X p).obj (op n)) ≫
                      Pi.π (fun _ : Fin d ↦ (X.X p).obj (op n)) i =
                phi.hom.app ((roosP X).X p) ≫
                  Pi.π (fun _ : Fin d ↦ (roosP X).X p) i ≫
                  (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f p) ∧
        (∀ {R S U : Sheaf J CommRingCat.{u}}
          (a : FiniteFreeScalarArrow J R S) (b : FiniteFreeScalarArrow J S U),
          ∃ (ab : FiniteFreeScalarArrow J R U) (_hab : ab.val = a.val ≫ b.val)
            (A : tensorFunctor a.val ⋙ tensorFunctor b.val ≅ tensorFunctor ab.val)
            (AT : projectionPost (I := ℕᵒᵖ) (tensorFunctor a.val) ⋙
                projectionPost (I := ℕᵒᵖ) (tensorFunctor b.val) ≅
                  projectionPost (I := ℕᵒᵖ) (tensorFunctor ab.val)),
            (∀ (M : ringedSiteModules.{u} (ringSheaf R)) (V : Cᵒᵖ)
              (s : S.obj.obj V) (z : U.obj.obj V) (x : M.val.obj V),
              (A.hom.app M).val.app V
                  (scalarPure b.val ((tensorFunctor a.val).obj M) V z
                    (scalarPure a.val M V s x)) =
                scalarPure ab.val M V (b.val.hom.app V s * z) x) ∧
            (∀ (M : ringedSiteModules.{u} (ringSheaf R)) (V : Cᵒᵖ)
              (z : U.obj.obj V) (x : M.val.obj V),
              (A.inv.app M).val.app V (scalarPure ab.val M V z x) =
                scalarPure b.val ((tensorFunctor a.val).obj M) V z
                  (scalarPure a.val M V 1 x)) ∧
            (∀ (X : ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R)) (n : ℕᵒᵖ),
              (AT.hom.app X).app n = A.hom.app (X.obj n)) ∧
            ∀ K : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R)),
              (exactDerived (tensorFunctor b.val) (hlim b) (hcolim b)).map
                  ((cmp a).comparison.hom.app K) ≫
                (cmp b).comparison.hom.app
                  ((exactDerived (projectionPost (I := ℕᵒᵖ) (tensorFunctor a.val))
                    (htlim a) (htcolim a)).obj K) ≫
                (L U).map ((exactDerivedComp (htlim a) (htcolim a) (htlim b) (htcolim b)
                  (htlim ab) (htcolim ab) AT).hom.app K) =
              (exactDerivedComp (hlim a) (hcolim a) (hlim b) (hcolim b)
                (hlim ab) (hcolim ab) A).hom.app ((L R).obj K) ≫
                (cmp ab).comparison.hom.app K) ∧
        (∀ R : Sheaf J CommRingCat.{u},
          ∃ (a : FiniteFreeScalarArrow J R R) (_ha : a.val = 𝟙 R)
            (U : tensorFunctor a.val ≅ 𝟭 (ringedSiteModules.{u} (ringSheaf R)))
            (UT : projectionPost (I := ℕᵒᵖ) (tensorFunctor a.val) ≅
              𝟭 (ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R))),
            (∀ (M : ringedSiteModules.{u} (ringSheaf R)) (V : Cᵒᵖ)
              (r : R.obj.obj V) (x : M.val.obj V),
              (U.hom.app M).val.app V (scalarPure a.val M V r x) = r • x) ∧
            (∀ (X : ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R)) (n : ℕᵒᵖ),
              (UT.hom.app X).app n = U.hom.app (X.obj n)) ∧
            ∀ K : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R)),
              (cmp a).comparison.hom.app K ≫
                  (L R).map ((exactDerivedUnit (htlim a) (htcolim a) UT).hom.app K) =
                (exactDerivedUnit (hlim a) (hcolim a) U).hom.app ((L R).obj K)) := by
  classical
  have hexa {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S) :
      PreservesFiniteLimits (tensorFunctor a.val) := by
    let := (scalar_exact J a).1
    infer_instance
  have hexc {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S) :
      PreservesFiniteColimits (tensorFunctor a.val) := (scalar_exact J a).2
  have hexat {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S) :
      PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) (tensorFunctor a.val)) := by
    let := hexa a
    exact ⟨fun _ _ _ ↦ whiskeringRight_preservesLimitsOfShape _⟩
  have hexct {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S) :
      PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) (tensorFunctor a.val)) := by
    let := hexc a
    exact ⟨fun _ _ _ ↦ whiskeringRight_preservesColimitsOfShape _⟩
  refine ⟨hexa, hexc, hexat, hexct, ?_⟩
  intro hlim hcolim htlim htcolim
  have models (R : Sheaf J CommRingCat.{u}) :
      ∃ (L : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u} (ringSheaf R)))
        (rho : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ L),
        L.IsRightDerivedFunctor (roosDerivedUnit rho)
          (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R))
            (.up ℤ)) := by
    let := smallProEtaleExactProducts J T e hJ R
    obtain ⟨L, rho, hL, _⟩ := strictRoosDerivation.{u, u, u, w} J (ringSheaf R)
      (by intro V x y; exact @mul_comm (R.obj.obj V) _ x y)
    exact ⟨L, rho, hL⟩
  choose L rho hL using models
  have comparisons {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S) :
      ∃ c : @ScalarStrictLimitComparison _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (tensorFunctor a.val) _ (hlim a) (hcolim a) (htlim a) (htcolim a)
        (L R) (L S) (rho R) (rho S),
        ∀ X, c.cone.hom.app X = roosAdditiveComparison (tensorFunctor a.val) X := by
    let := hlim a
    let := hcolim a
    let := htlim a
    let := htcolim a
    let := scalar_products J a
    obtain ⟨c, hc⟩ := comparison_exists (tensorFunctor a.val) (L R) (L S) (rho R) (rho S)
    exact ⟨c, fun _ ↦ by rw [hc]; rfl⟩
  choose cmp₀ hcmp₀ using (fun (R S : Sheaf J CommRingCat.{u})
    (a : FiniteFreeScalarArrow J R S) ↦ comparisons a)
  let cmp {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S) := cmp₀ R S a
  have hcmp {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S) := hcmp₀ R S a
  refine ⟨L, rho, hL, cmp, ?_, ?_, ?_⟩
  · intro R S a d theta
    obtain ⟨phi, hp, hi⟩ := (fieldScalarOrdinaryCoordinates J).1 a d theta
    refine ⟨phi, hp, hi, ?_⟩
    intro X p n i
    have hb := congrArg (fun f ↦ f.f p) ((cmp a).beta_projection X n)
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hb
    rw [hb]
    exact finite_power_naturality (tensorFunctor a.val) (restriction a.val) d phi
      ((Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f p) i
  · intro R S U a b
    obtain ⟨ab, hab, A, AT, hA, hAi, hAT⟩ :=
      (fieldScalarOrdinaryCoordinates J).2.1 a b
    refine ⟨ab, hab, A, AT, hA, hAi, hAT, ?_⟩
    let := hlim a
    let := hcolim a
    let := htlim a
    let := htcolim a
    let := hlim b
    let := hcolim b
    let := htlim b
    let := htcolim b
    let := hlim ab
    let := hcolim ab
    let := htlim ab
    let := htcolim ab
    exact comparison_comp (tensorFunctor a.val) (tensorFunctor b.val)
      (tensorFunctor ab.val) (L R) (L S) (L U) (rho R) (rho S) (rho U)
      (cmp a) (cmp b) (cmp ab) A AT (hcmp₀ R S a) (hcmp₀ S U b) (hcmp₀ R U ab) hAT
  · intro R
    obtain ⟨a, ha, U, UT, hU, hUT⟩ := (fieldScalarOrdinaryCoordinates J).2.2 R
    refine ⟨a, ha, U, UT, hU, hUT, ?_⟩
    let := hlim a
    let := hcolim a
    let := htlim a
    let := htcolim a
    exact comparison_unit (tensorFunctor a.val) (L R) (rho R) U UT hUT (cmp a) (hcmp a)

end SheafOfModules

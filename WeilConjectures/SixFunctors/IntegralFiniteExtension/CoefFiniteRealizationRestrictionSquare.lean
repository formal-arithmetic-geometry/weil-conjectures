/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefScalarReductionExchange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Realization of a coefficient restriction square

Source: lem-coef-integral-finite-extension, quotient compatibility, and
lem-coef-finite-dualizing, normalized comparison-site realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 3000]
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension
attribute [local implicit_reducible] finiteDualizingIntrinsicRes
  finiteDualizingIntrinsicRingMap pbcDerivedRestrict sfIntrinsicDerivedEquivalence
  integralCoefficientSheaf integralCoefficientCommRingSheaf
private theorem ulift_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ) :
    RingHom.ulift.{u + 1, u + 1} χ =
      (RingHom.ulift.{u + 1, u + 1} ψ).comp (RingHom.ulift.{u + 1, u + 1} φ) := by
  apply RingHom.ext
  intro x
  apply ULift.ext
  exact congrArg (fun f ↦ f x.down) h

private theorem scalarUnit_surjective (Y : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    (M : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (W : Y.ProEtᵒᵖ) :
    Function.Surjective (sfIntrinsicRealizationUnit Y A M W) := by
  let α := ProEtale.finiteCoefficientIntrinsicScalarMap Y A
  let N := (ProEtale.finiteCoefficientModulePresheaf Y.ProEt
    (ULift.{u + 1, u} A)).obj M.obj
  let η := (PresheafOfModules.sheafificationAdjunction α).unit.app N
  have : IsIso η := by
    dsimp only [η, α, N]
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology Y)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})).obj
        M).property
  have : IsIso (η.app W) := inferInstanceAs
    (IsIso ((PresheafOfModules.evaluation _ W).map η))
  exact (ConcreteCategory.bijective_of_isIso (η.app W)).surjective

private theorem scalarUnit_naturality (Y : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    {M N : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (f : M ⟶ N) (W : Y.ProEtᵒᵖ) (x : M.obj.obj W) :
    (((sfIntrinsicModuleEquivalence Y A).functor.map f).val.app W)
        (sfIntrinsicRealizationUnit Y A M W x) =
      sfIntrinsicRealizationUnit Y A N W (f.hom.app W x) := by
  exact (ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app W)
      ((PresheafOfModules.sheafificationAdjunction
        (ProEtale.finiteCoefficientIntrinsicScalarMap Y A)).unit.naturality
          ((ProEtale.finiteCoefficientModulePresheaf Y.ProEt
            (ULift.{u + 1, u} A)).map f.hom))) x).symm

private abbrev ordinaryIntrinsicComparison (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :=
  (finiteDualizingRestriction_existsUnique Y φ).choose

private theorem ordinaryIntrinsicComparison_apply (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (M : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (W : Y.ProEtᵒᵖ) (x : M.obj.obj W) :
    ((ordinaryIntrinsicComparison Y φ).hom.app M).val.app W
        (sfIntrinsicRealizationUnit Y B M W x) =
      sfIntrinsicRealizationUnit Y A
        ((Sheaf.restrictScalars (ProEt.topology Y)
          (RingHom.ulift.{u + 1, u + 1} φ)).obj M) W x := by
  exact eq_of_heq ((finiteDualizingRestriction_existsUnique Y φ).choose_spec.1 M W x)

private abbrev coefficientSheafMap (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    proEtaleConstantRing Y A ⟶ proEtaleConstantRing Y B :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ))

private theorem coefficientSheafMap_comp (Y : Scheme.{u})
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ) :
    coefficientSheafMap Y φ ≫ coefficientSheafMap Y ψ = coefficientSheafMap Y χ := by
  subst χ
  rw [coefficientSheafMap, coefficientSheafMap, ← Functor.map_comp]
  rfl

private theorem ordinaryIntrinsicComparison_comp (Y : Scheme.{u})
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    (M : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} C))) :
    (ordinaryIntrinsicComparison Y χ).hom.app M ≫
      (sfIntrinsicModuleEquivalence Y A).functor.map
        ((Sheaf.restrictScalarsCompIso (ProEt.topology Y)
          (RingHom.ulift.{u + 1, u + 1} φ) (RingHom.ulift.{u + 1, u + 1} ψ)
          (RingHom.ulift.{u + 1, u + 1} χ)
          (ulift_comp φ ψ χ h)).inv.app M) =
    (pbcRestrictComp (coefficientSheafMap Y φ) (coefficientSheafMap Y ψ)
        (coefficientSheafMap Y χ) (coefficientSheafMap_comp Y φ ψ χ h)).inv.app
        ((sfIntrinsicModuleEquivalence Y C).functor.obj M) ≫
      (finiteDualizingIntrinsicRes Y φ).map
        ((ordinaryIntrinsicComparison Y ψ).hom.app M) ≫
      (ordinaryIntrinsicComparison Y φ).hom.app
        ((Sheaf.restrictScalars (ProEt.topology Y) (RingHom.ulift.{u + 1, u + 1} ψ)).obj M) := by
  let e := pbcRestrictComp (coefficientSheafMap Y φ) (coefficientSheafMap Y ψ)
    (coefficientSheafMap Y χ) (coefficientSheafMap_comp Y φ ψ χ h)
  apply (cancel_epi (e.hom.app ((sfIntrinsicModuleEquivalence Y C).functor.obj M))).mp
  simp only [e, Iso.hom_inv_id_app_assoc]
  ext W x
  obtain ⟨x, rfl⟩ := scalarUnit_surjective Y C M W x
  have he := (pbcRestrictComp_exists (coefficientSheafMap Y φ) (coefficientSheafMap Y ψ)
    (coefficientSheafMap Y χ) (coefficientSheafMap_comp Y φ ψ χ h)).exists.choose_spec
      ((sfIntrinsicModuleEquivalence Y C).functor.obj M) W
        (sfIntrinsicRealizationUnit Y C M W x)
  change (((sfIntrinsicModuleEquivalence Y A).functor.map _).val.app W)
      (((ordinaryIntrinsicComparison Y χ).hom.app M).val.app W
        ((e.hom.app _).val.app W (sfIntrinsicRealizationUnit Y C M W x))) =
    ((ordinaryIntrinsicComparison Y φ).hom.app _).val.app W
      (((ordinaryIntrinsicComparison Y ψ).hom.app M).val.app W
        (sfIntrinsicRealizationUnit Y C M W x))
  change (e.hom.app ((sfIntrinsicModuleEquivalence Y C).functor.obj M)).val.app W
      (sfIntrinsicRealizationUnit Y C M W x) =
    sfIntrinsicRealizationUnit Y C M W x at he
  rw [he, ordinaryIntrinsicComparison_apply, ordinaryIntrinsicComparison_apply,
    ordinaryIntrinsicComparison_apply, scalarUnit_naturality]
  rfl

private theorem intrinsicComparison_comp (Y : Scheme.{u})
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    (K : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} C)))) :
    (sfIntrinsicDerivedEquivalence Y A).functor.map
        ((Sheaf.derivedRestrictScalarsCompIso (ProEt.topology Y)
          (ulift_comp φ ψ χ h)).inv.app K) ≫
      (finiteDualizingGenericDerivedRestriction Y φ).inv.app
        ((Sheaf.derivedRestrictScalars (ProEt.topology Y) (RingHom.ulift.{u + 1, u + 1} ψ)).obj K) ≫
      (finiteDualizingIntrinsicRes Y φ).mapDerivedCategory.map
        ((finiteDualizingGenericDerivedRestriction Y ψ).inv.app K) =
    (finiteDualizingGenericDerivedRestriction Y χ).inv.app K ≫
      (pbcDerivedRestrictComp (coefficientSheafMap Y φ) (coefficientSheafMap Y ψ)
        (coefficientSheafMap Y χ) (coefficientSheafMap_comp Y φ ψ χ h)).inv.app
          ((sfIntrinsicDerivedEquivalence Y C).functor.obj K) := by
  have hd := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (ordinaryIntrinsicComparison Y ψ) (ordinaryIntrinsicComparison Y φ)
    (ordinaryIntrinsicComparison Y χ)
    (pbcRestrictComp (coefficientSheafMap Y φ) (coefficientSheafMap Y ψ)
      (coefficientSheafMap Y χ) (coefficientSheafMap_comp Y φ ψ χ h)).symm
    (Sheaf.restrictScalarsCompIso (ProEt.topology Y)
          (RingHom.ulift.{u + 1, u + 1} φ) (RingHom.ulift.{u + 1, u + 1} ψ)
          (RingHom.ulift.{u + 1, u + 1} χ)
      (ulift_comp φ ψ χ h)).symm (ordinaryIntrinsicComparison_comp Y φ ψ χ h) K
  change (finiteDualizingGenericDerivedRestriction Y χ).hom.app K ≫
      (sfIntrinsicDerivedEquivalence Y A).functor.map
        ((Sheaf.derivedRestrictScalarsCompIso (ProEt.topology Y)
          (ulift_comp φ ψ χ h)).inv.app K) =
    (pbcDerivedRestrictComp (coefficientSheafMap Y φ) (coefficientSheafMap Y ψ)
        (coefficientSheafMap Y χ) (coefficientSheafMap_comp Y φ ψ χ h)).inv.app
        ((sfIntrinsicDerivedEquivalence Y C).functor.obj K) ≫
      (finiteDualizingIntrinsicRes Y φ).mapDerivedCategory.map
        ((finiteDualizingGenericDerivedRestriction Y ψ).hom.app K) ≫
      (finiteDualizingGenericDerivedRestriction Y φ).hom.app
        ((Sheaf.derivedRestrictScalars (ProEt.topology Y)
          (RingHom.ulift.{u + 1, u + 1} ψ)).obj K) at hd
  apply (cancel_epi ((finiteDualizingGenericDerivedRestriction Y χ).hom.app K)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, ← Category.assoc, hd]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

open AlgebraicGeometry.ProEtale

private theorem ordinaryComparison_comp (T : Scheme.{u})
    {R S V : Type (u + 1)} [CommRing R] [CommRing S] [CommRing V]
    (φ : R →+* S) (ψ : S →+* V) (χ : R →+* V) (h : χ = ψ.comp φ) :
    (pbcComparisonRestrict T χ).hom ≫
      Functor.whiskerRight (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ χ h).inv
        (comparisonUpperStar (ModuleCat.{u + 1} R) T) =
    Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} V) T)
        (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) φ ψ χ h).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (pbcComparisonRestrict T ψ).hom
        (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Sheaf.restrictScalars T.smallEtaleTopology ψ)
        (pbcComparisonRestrict T φ).hom ≫ (Functor.associator _ _ _).inv := by
  let aR := comparisonAdjunction (ModuleCat.{u + 1} R) T
  let aS := comparisonAdjunction (ModuleCat.{u + 1} S) T
  let aV := comparisonAdjunction (ModuleCat.{u + 1} V) T
  let eφ := Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ
  let eψ := Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology ψ
  let eχ := Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology χ
  let pφ := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ
  let pψ := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) ψ
  let pχ := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) χ
  apply (conjugateEquiv ((eψ.comp eφ).comp aR) (aV.comp pχ)).injective
  rw [← conjugateEquiv_comp _ (eχ.comp aR)]
  rw [← conjugateEquiv_comp _ (aV.comp (pψ.comp pφ))]
  rw [← conjugateEquiv_comp _ ((aV.comp pψ).comp pφ)]
  rw [← conjugateEquiv_comp _ ((eψ.comp aS).comp pφ)]
  rw [← conjugateEquiv_comp _ (eψ.comp (aS.comp pφ))]
  rw [← conjugateEquiv_comp _ (eψ.comp (eφ.comp aR))]
  have hc {U V : Type (u + 1)} [CommRing U] [CommRing V] (f : U →+* V) :
      conjugateEquiv
        ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology f).comp
          (comparisonAdjunction (ModuleCat.{u + 1} U) T))
        ((comparisonAdjunction (ModuleCat.{u + 1} V) T).comp
          (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) f))
        (pbcComparisonRestrict T f).hom = 𝟙 _ := by
    change (conjugateEquiv _ _)
      ((conjugateEquiv _ _).symm (𝟙 _)) = _
    exact Equiv.apply_symm_apply _ _
  simp only [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
    conjugateEquiv_associator_hom, conjugateEquiv_associator_inv]
  dsimp only [aR, aS, aV, eφ, eψ, eχ, pφ, pψ, pχ]
  rw [hc, hc, hc]
  ext X : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.id_app,
    Category.comp_id, Category.id_comp]
  ext U : 3
  rfl

private theorem derivedComparison_comp (T : Scheme.{u})
    {R S V : Type (u + 1)} [CommRing R] [CommRing S] [CommRing V]
    (φ : R →+* S) (ψ : S →+* V) (χ : R →+* V) (h : χ = ψ.comp φ)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} V))) :
    (pbcDerivedComparisonRestrict T χ).hom.app K ≫
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.map
        ((Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology h).inv.app K) =
    (Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology T) h).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} V) T).mapDerivedCategory.obj K) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ).map
        ((pbcDerivedComparisonRestrict T ψ).hom.app K) ≫
      (pbcDerivedComparisonRestrict T φ).hom.app
        ((Sheaf.derivedRestrictScalars T.smallEtaleTopology ψ).obj K) := by
  have ho (X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} V)) :=
    congr_app (ordinaryComparison_comp T φ ψ χ h) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Category.comp_id, Category.id_comp] at ho
  have hd := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (pbcComparisonRestrict T ψ) (pbcComparisonRestrict T φ)
    (pbcComparisonRestrict T χ)
    (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) φ ψ χ h).symm
    (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ χ h).symm ho K
  exact hd

private theorem comparison_comp_inv (Y : Scheme.{u})
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        ((Sheaf.derivedRestrictScalarsCompIso Y.smallEtaleTopology h).inv.app K) ≫
      (pbcDerivedComparisonRestrict Y φ).inv.app
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology ψ).obj K) ≫
      (Sheaf.derivedRestrictScalars (ProEt.topology Y) φ).map
        ((pbcDerivedComparisonRestrict Y ψ).inv.app K) =
    (pbcDerivedComparisonRestrict Y χ).inv.app K ≫
      (Sheaf.derivedRestrictScalarsCompIso (ProEt.topology Y) h).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} C) Y).mapDerivedCategory.obj K) := by
  have hd := derivedComparison_comp Y φ ψ χ h K
  apply (cancel_epi ((pbcDerivedComparisonRestrict Y χ).hom.app K)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, ← Category.assoc, hd]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private abbrev realization (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence Y A).functor

private def realizationRestriction (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    realization Y B ⋙ (finiteDualizingIntrinsicRes Y φ).mapDerivedCategory ≅
      Sheaf.derivedRestrictScalars Y.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1} φ) ⋙ realization Y A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (finiteDualizingGenericDerivedRestriction Y φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (pbcDerivedComparisonRestrict Y (RingHom.ulift.{u + 1, u + 1} φ)) _ ≪≫
    Functor.associator _ _ _

private theorem realizationRestriction_comp (Y : Scheme.{u})
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} C)))) :
    (realization Y A).map
        ((Sheaf.derivedRestrictScalarsCompIso Y.smallEtaleTopology
          (ulift_comp φ ψ χ h)).inv.app K) ≫
      (realizationRestriction Y φ).inv.app
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology
          (RingHom.ulift.{u + 1, u + 1} ψ)).obj K) ≫
      (finiteDualizingIntrinsicRes Y φ).mapDerivedCategory.map
        ((realizationRestriction Y ψ).inv.app K) =
    (realizationRestriction Y χ).inv.app K ≫
      (pbcDerivedRestrictComp (coefficientSheafMap Y φ) (coefficientSheafMap Y ψ)
        (coefficientSheafMap Y χ) (coefficientSheafMap_comp Y φ ψ χ h)).inv.app
          ((realization Y C).obj K) := by
  have hn := (finiteDualizingGenericDerivedRestriction Y φ).inv.naturality
    ((pbcDerivedComparisonRestrict Y (RingHom.ulift.{u + 1, u + 1} ψ)).inv.app K)
  dsimp only [Functor.comp_map] at hn
  have hp := congrArg (fun f ↦ (sfIntrinsicDerivedEquivalence Y A).functor.map f)
    (comparison_comp_inv Y (RingHom.ulift.{u + 1, u + 1} φ)
      (RingHom.ulift.{u + 1, u + 1} ψ) (RingHom.ulift.{u + 1, u + 1} χ)
      (ulift_comp φ ψ χ h) K)
  simp only [Functor.map_comp] at hp
  unfold realizationRestriction
  simp only [realization, Functor.comp_obj, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Iso.symm_inv, Category.assoc, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.comp_id, Category.id_comp, Functor.comp_map,
    Functor.map_comp]
  rw [← reassoc_of% hn, reassoc_of% hp]
  exact congrArg (fun f ↦
    (sfIntrinsicDerivedEquivalence Y A).functor.map
      ((pbcDerivedComparisonRestrict Y (RingHom.ulift.{u + 1, u + 1} χ)).inv.app K) ≫ f)
    (intrinsicComparison_comp Y φ ψ χ h
      ((comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} C)) Y).mapDerivedCategory.obj K))

private theorem realizationRestriction_square (Y : Scheme.{u})
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Finite A] [Finite B] [Finite C] [Finite D]
    (qA : A →+* B) (iB : B →+* D) (iA : A →+* C) (qB : C →+* D)
    (h : qB.comp iA = iB.comp qA)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} D)))) :
    (realization Y A).map
        (((Sheaf.derivedRestrictScalarsCompIso Y.smallEtaleTopology
          (ulift_comp qA iB (qB.comp iA) h)).hom ≫
          (Sheaf.derivedRestrictScalarsCompIso Y.smallEtaleTopology
            (ulift_comp iA qB (qB.comp iA) rfl)).inv).app K) ≫
      (realizationRestriction Y iA).inv.app
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology
          (RingHom.ulift.{u + 1, u + 1} qB)).obj K) ≫
      (finiteDualizingIntrinsicRes Y iA).mapDerivedCategory.map
        ((realizationRestriction Y qB).inv.app K) =
    (realizationRestriction Y qA).inv.app
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology
          (RingHom.ulift.{u + 1, u + 1} iB)).obj K) ≫
      (finiteDualizingIntrinsicRes Y qA).mapDerivedCategory.map
        ((realizationRestriction Y iB).inv.app K) ≫
      ((pbcDerivedRestrictComp (coefficientSheafMap Y qA) (coefficientSheafMap Y iB)
          (coefficientSheafMap Y (qB.comp iA))
          (coefficientSheafMap_comp Y qA iB (qB.comp iA) h)).hom ≫
        (pbcDerivedRestrictComp (coefficientSheafMap Y iA) (coefficientSheafMap Y qB)
          (coefficientSheafMap Y (qB.comp iA))
          (coefficientSheafMap_comp Y iA qB (qB.comp iA) rfl)).inv).app
            ((realization Y D).obj K) := by
  have he := realizationRestriction_comp Y qA iB (qB.comp iA) h K
  have hl := realizationRestriction_comp Y iA qB (qB.comp iA) rfl K
  apply (cancel_epi ((realization Y A).map
    ((Sheaf.derivedRestrictScalarsCompIso Y.smallEtaleTopology
      (ulift_comp qA iB (qB.comp iA) h)).inv.app K))).mp
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hl]
  have he' := congrArg (fun f ↦ f ≫
    (pbcDerivedRestrictComp (coefficientSheafMap Y qA) (coefficientSheafMap Y iB)
      (coefficientSheafMap Y (qB.comp iA))
      (coefficientSheafMap_comp Y qA iB (qB.comp iA) h)).hom.app
        ((realization Y D).obj K) ≫
    (pbcDerivedRestrictComp (coefficientSheafMap Y iA) (coefficientSheafMap Y qB)
      (coefficientSheafMap Y (qB.comp iA))
      (coefficientSheafMap_comp Y iA qB (qB.comp iA) rfl)).inv.app
        ((realization Y D).obj K)) he
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using he'.symm

private theorem restrictionSquare_congr {Y : Scheme.{u}}
    {R S T U : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (a : R ⟶ T) (b : T ⟶ U)
    (χ χ' : R ⟶ U) (hc : χ = χ')
    (hφ : φ ≫ ψ = χ) (ha : a ≫ b = χ)
    (hφ' : φ ≫ ψ = χ') (ha' : a ≫ b = χ') :
    (pbcDerivedRestrictComp φ ψ χ hφ).hom ≫
        (pbcDerivedRestrictComp a b χ ha).inv =
      (pbcDerivedRestrictComp φ ψ χ' hφ').hom ≫
        (pbcDerivedRestrictComp a b χ' ha').inv := by
  subst χ'
  rfl

private theorem transport_square
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    (FA : A ⥤ A') (FB : B ⥤ B') (FC : C ⥤ C') (FD : D ⥤ D')
    (RAB : B ⥤ A) (RBD : D ⥤ B) (RAC : C ⥤ A) (RCD : D ⥤ C)
    (RA RA' : B' ⥤ A') (RB RB' : D' ⥤ C') (RC : C' ⥤ A') (RD : D' ⥤ B')
    (hA : RA = RA') (hB : RB = RB')
    (a : FB ⋙ RA ≅ RAB ⋙ FA) (a' : FB ⋙ RA' ≅ RAB ⋙ FA)
    (b : FD ⋙ RB ≅ RCD ⋙ FC) (b' : FD ⋙ RB' ≅ RCD ⋙ FC)
    (ha : HEq a a') (hb : HEq b b')
    (c : FC ⋙ RC ≅ RAC ⋙ FA) (d : FD ⋙ RD ≅ RBD ⋙ FB)
    (J : D ⥤ A) (T : D' ⥤ A')
    (η : RBD ⋙ RAB ≅ J) (η' : RCD ⋙ RAC ≅ J)
    (θ : RD ⋙ RA' ≅ T) (θ' : T ≅ RB' ⋙ RC)
    (δ : RD ⋙ RA ≅ RB ⋙ RC)
    (hδ : δ = Functor.isoWhiskerLeft RD (eqToIso hA) ≪≫ θ ≪≫ θ' ≪≫
      Functor.isoWhiskerRight (eqToIso hB.symm) RC)
    (K : D)
    (h : FA.map ((η.hom ≫ η'.inv).app K) ≫
        c.inv.app (RCD.obj K) ≫ RC.map (b'.inv.app K) =
      a'.inv.app (RBD.obj K) ≫ RA'.map (d.inv.app K) ≫
        (θ.hom ≫ θ'.hom).app (FD.obj K)) :
    FA.map ((η.hom ≫ η'.inv).app K) ≫
      c.inv.app (RCD.obj K) ≫ RC.map (b.inv.app K) =
      a.inv.app (RBD.obj K) ≫ RA.map (d.inv.app K) ≫
        δ.hom.app (FD.obj K) := by
  rw [hδ]
  subst RA'
  subst RB'
  cases eq_of_heq ha
  cases eq_of_heq hb
  simpa only [eqToIso_refl, Functor.isoWhiskerLeft_refl, Functor.isoWhiskerRight_refl,
    Iso.refl_trans, Iso.trans_refl, Iso.trans_hom] using h

private theorem paste_heq
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (U : C ⥤ B) (V : A ⥤ D) (G : D ⥤ F) (H : B ⥤ E)
    (S : A ⥤ C) (T : D ⥤ B) (R R' : F ⥤ E)
    (p : V ⋙ T ≅ S ⋙ U)
    (q : G ⋙ R ≅ T ⋙ H) (q' : G ⋙ R' ≅ T ⋙ H)
    (hr : R = R') (hq : HEq q q') :
    HEq
      (Functor.associator V G R ≪≫ Functor.isoWhiskerLeft V q ≪≫
        (Functor.associator V T H).symm ≪≫ Functor.isoWhiskerRight p H ≪≫
        Functor.associator S U H)
      (Functor.associator V G R' ≪≫ Functor.isoWhiskerLeft V q' ≪≫
        (Functor.associator V T H).symm ≪≫ Functor.isoWhiskerRight p H ≪≫
        Functor.associator S U H) := by
  subst R'
  cases eq_of_heq hq
  rfl

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})

private theorem quotientRestriction_heq {m n : ℕ} (h : n ≤ m) :
    HEq (finiteDualizingRealizationRestriction l E X h)
      (realizationRestriction X (finiteDualizingQuotientBase l E h)) := by
  exact paste_heq _ _ _ _ _ _ _ _ _ _ _
    (scalarQuotient_restrict l E X h)
    (finiteDualizingIntrinsicRestriction_existsUnique l E X h).choose_spec.1

/-- The comparison-site realization preserves the square of coefficient restrictions.
This is a statement for an arbitrary finite-coefficient object, without any
exceptional functor, dualizing term, counit comparison or scalar-extension mate.

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md, quotient compatibility, paragraphs 2--3;
lem-coef-finite-dualizing.proof.md, final realization sentence.
(blueprint: lem-sf-finite-realization-restriction-square)

Proof: the two coefficient maps in hq agree on residue representatives. Before
localization, restriction precomposes the scalar action and leaves sections
unchanged. The four intrinsic restriction comparisons and the two ordinary
comparison-site restriction comparisons are normalized by this identity on
sections. Pasting around either side therefore gives the same ordinary square,
with restriction composition accounting for the two factorizations of the ring
map. Apply the exact derived localization functors; their composition comparisons
are precisely derivedRestrictScalarsCompIso. Whisker the intrinsic and
comparison-site squares and use associator naturality. The resulting outer
boundary is the displayed equation. The definition of scalarRestrictionSquare
uses these same derived restriction compositors and the equalities
scalarQuotient_restrict, so it has the required normalization. This works for
arbitrary K, repeated levels and identity field maps; no coefficient map is
assumed flat and no exceptional adjunction is invoked. -/
theorem finiteRealization_restriction_square {m n : ℕ} (h : n ≤ m)
    (hq : (finiteDualizingQuotient l L h).comp
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι m)) =
      (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)).comp
        (finiteDualizingQuotient l E h))
    (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l L n) X) :
    (finiteDualizingRealization l E X m).map
        (((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology hq).hom ≫
          (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
            (rfl : (finiteDualizingQuotient l L h).comp
                (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι m)) =
              (finiteDualizingQuotient l L h).comp
                (RingHom.ulift.{u + 1, u + 1}
                  (integralScalarQuotientMap l E L ι m)))).inv).app K) ≫
      (finiteRealizationRestriction l E L ι X m).inv.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
          (finiteDualizingQuotient l L h)).obj K) ≫
      (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X m)).map
        ((finiteDualizingRealizationRestriction l L X h).inv.app K) =
    (finiteDualizingRealizationRestriction l E X h).inv.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
          (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))).obj K) ≫
      (normalizedDVRRes l E X h).map
        ((finiteRealizationRestriction l E L ι X n).inv.app K) ≫
      (scalarRestrictionSquare l E L ι X h).hom.app
        ((finiteDualizingRealization l L X n).obj K) := by
  let qE := finiteDualizingQuotientBase l E h
  let qL := finiteDualizingQuotientBase l L h
  let iM := integralScalarQuotientMap l E L ι m
  let iN := integralScalarQuotientMap l E L ι n
  have hb : qL.comp iM = iN.comp qE := by
    apply RingHom.ext
    intro x
    exact congrArg (fun f ↦ (f (ULift.up x)).down) hq
  have hs := realizationRestriction_square X qE iN iM qL hb K
  have hθ := restrictionSquare_congr
    (scalarQuotient l E X h) (integralScalarQuotientSheafMap l E L ι X n)
    (integralScalarQuotientSheafMap l E L ι X m) (scalarQuotient l L X h)
    (coefficientSheafMap X (qL.comp iM))
    (integralScalarQuotientSheafMap l E L ι X m ≫ scalarQuotient l L X h)
    (coefficientSheafMap_comp X iM qL (qL.comp iM) rfl).symm
    (coefficientSheafMap_comp X qE iN (qL.comp iM) hb)
    (coefficientSheafMap_comp X iM qL (qL.comp iM) rfl)
    (scalarQuotient_square l E L ι X h).symm rfl
  erw [hθ] at hs
  have hrE : normalizedDVRRes l E X h =
      pbcDerivedRestrict (scalarQuotient l E X h) :=
    scalarQuotient_restrict l E X h
  have hrL : normalizedDVRRes l L X h =
      pbcDerivedRestrict (scalarQuotient l L X h) :=
    scalarQuotient_restrict l L X h
  let η := Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology hq
  let η' := Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
      (rfl : (finiteDualizingQuotient l L h).comp
          (RingHom.ulift.{u + 1, u + 1} iM) =
        (finiteDualizingQuotient l L h).comp
          (RingHom.ulift.{u + 1, u + 1} iM))
  let θ := pbcDerivedRestrictComp (scalarQuotient l E X h)
      (integralScalarQuotientSheafMap l E L ι X n)
      (integralScalarQuotientSheafMap l E L ι X m ≫ scalarQuotient l L X h)
      (scalarQuotient_square l E L ι X h).symm
  let θ' := (pbcDerivedRestrictComp (integralScalarQuotientSheafMap l E L ι X m)
      (scalarQuotient l L X h) _ rfl).symm
  have he :
      (Functor.isoWhiskerLeft
          (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n))
          (eqToIso hrE) ≪≫ θ ≪≫ θ' ≪≫
        Functor.isoWhiskerRight (eqToIso hrL.symm)
          (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X m))) =
      scalarRestrictionSquare l E L ι X h := rfl
  have ht := transport_square
    (FA := finiteDualizingRealization l E X m)
    (FB := finiteDualizingRealization l E X n)
    (FC := finiteDualizingRealization l L X m)
    (FD := finiteDualizingRealization l L X n)
    (RAB := Sheaf.derivedRestrictScalars X.smallEtaleTopology
      (finiteDualizingQuotient l E h))
    (RBD := Sheaf.derivedRestrictScalars X.smallEtaleTopology
      (RingHom.ulift.{u + 1, u + 1} iN))
    (RAC := Sheaf.derivedRestrictScalars X.smallEtaleTopology
      (RingHom.ulift.{u + 1, u + 1} iM))
    (RCD := Sheaf.derivedRestrictScalars X.smallEtaleTopology
      (finiteDualizingQuotient l L h))
    (RA := normalizedDVRRes l E X h)
    (RA' := pbcDerivedRestrict (scalarQuotient l E X h))
    (RB := normalizedDVRRes l L X h)
    (RB' := pbcDerivedRestrict (scalarQuotient l L X h))
    (RC := pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X m))
    (RD := pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n))
    (hA := hrE) (hB := hrL)
    (a := finiteDualizingRealizationRestriction l E X h)
    (a' := realizationRestriction X qE)
    (b := finiteDualizingRealizationRestriction l L X h)
    (b' := realizationRestriction X qL)
    (c := finiteRealizationRestriction l E L ι X m)
    (d := finiteRealizationRestriction l E L ι X n)
    (η := η) (η' := η') (θ := θ) (θ' := θ')
    (δ := scalarRestrictionSquare l E L ι X h) (hδ := he.symm) (K := K)
    (ha := quotientRestriction_heq l E X h)
    (hb := quotientRestriction_heq l L X h) (h := hs)
  exact ht

end WeilConjectures.IntegralFiniteExtension

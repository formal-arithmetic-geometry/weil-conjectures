/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import Submission.WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Transport of supplied constant complexes on a slice

Source: Stacks Project, proetale.tex, Tags 099R, 099Y and 09AL
(blueprint: lem-weil-pbc-finite-coefficient-slice-model-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

namespace SliceModelTransportProof

section Scalars
universe a b
variable {C : Type a} [Category.{b} C] (J : GrothendieckTopology C)
  (Λ : Type (max a b)) [CommRing Λ]

/-- Restriction to constant scalars preserves the underlying additive sheaf exactly. -/
private def scalarRestriction (R : Sheaf J RingCat.{max a b})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj) :
    SheafOfModules.{max a b} R ⥤
      Sheaf J (ModuleCat.{max a b} Λ) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars α).obj M.val
    let F : Cᵒᵖ ⥤ ModuleCat.{max a b} Λ :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
      (forget₂ (ModuleCat.{max a b} Λ) AddCommGrpCat.{max a b}) M.isSheaf⟩
  map φ := ⟨{
    app U := ((PresheafOfModules.restrictScalars
      α).map φ.val).app U
    naturality _ _ f := by
      ext x
      exact ConcreteCategory.congr_hom (φ.val.naturality f) x }⟩
  map_id M := by ext U x; rfl
  map_comp φ ψ := by ext U x; rfl

private def constantModulePresheaf :
    (Cᵒᵖ ⥤ ModuleCat.{max a b} Λ) ⥤
      PresheafOfModules.{max a b}
        ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) where
  obj F :=
    { obj := F.obj
      map f := F.map f
      map_id U := by ext x; exact ConcreteCategory.congr_hom (F.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map φ :=
    { app := φ.app
      naturality f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }

private noncomputable def constantModuleFullyFaithful :
    (constantModulePresheaf (C := C) Λ).FullyFaithful where
  preimage φ :=
    { app := φ.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

private noncomputable instance : (constantModulePresheaf (C := C) Λ).Full :=
  (constantModuleFullyFaithful (C := C) Λ).full

private noncomputable instance : (constantModulePresheaf (C := C) Λ).Faithful :=
  (constantModuleFullyFaithful (C := C) Λ).faithful

private noncomputable def moduleEmbedding :=
  sheafToPresheaf J (ModuleCat.{max a b} Λ) ⋙
    constantModulePresheaf (C := C) Λ

private noncomputable instance : (moduleEmbedding J Λ).Full :=
  inferInstanceAs (sheafToPresheaf J
    (ModuleCat.{max a b} Λ) ⋙ constantModulePresheaf (C := C) Λ).Full

private noncomputable instance : (moduleEmbedding J Λ).Faithful :=
  inferInstanceAs (sheafToPresheaf J
    (ModuleCat.{max a b} Λ) ⋙ constantModulePresheaf (C := C) Λ).Faithful

variable (R : Sheaf J RingCat.{max a b})
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasSheafify J AddCommGrpCat.{max a b}] [J.WEqualsLocallyBijective AddCommGrpCat.{max a b}]

private noncomputable instance restriction_full : (scalarRestriction J Λ R α).Full := by
  exact Functor.Full.of_comp_faithful_iso
    (G := moduleEmbedding J Λ)
    (H := SheafOfModules.forget _ ⋙
      PresheafOfModules.restrictScalars α) (Iso.refl _)

private noncomputable instance restriction_faithful :
    (scalarRestriction J Λ R α).Faithful := by
  exact Functor.Faithful.of_comp_iso
    (G := moduleEmbedding J Λ)
    (H := SheafOfModules.forget _ ⋙
      PresheafOfModules.restrictScalars α) (Iso.refl _)

private noncomputable instance restriction_essSurj :
    (scalarRestriction J Λ R α).EssSurj where
  mem_essImage F := by
    let P := (moduleEmbedding J Λ).obj F
    let adj := PresheafOfModules.sheafificationAdjunction.{max a b}
      α
    have hη : IsIso (adj.unit.app P) := by
      rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
      change IsIso (toSheafify J P.presheaf)
      exact isIso_toSheafify J
        ((sheafCompose J
          (forget₂ (ModuleCat.{max a b} Λ)
            AddCommGrpCat.{max a b})).obj F).property
    refine ⟨(PresheafOfModules.sheafification.{max a b} α).obj P, ⟨?_⟩⟩
    exact (Functor.FullyFaithful.ofFullyFaithful (moduleEmbedding J Λ)).preimageIso
      (asIso (adj.unit.app P)).symm

private instance scalarRestriction_equivalence :
    (scalarRestriction J Λ R α).IsEquivalence := by
  exact {}

private def constantExtension := moduleEmbedding J Λ ⋙
  PresheafOfModules.sheafification.{max a b} α

private def scalarCounit : scalarRestriction J Λ R α ⋙ constantExtension J Λ R α ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ asIso ((PresheafOfModules.sheafificationAdjunction.{max a b} α).counit.app M))
    (fun f ↦ (PresheafOfModules.sheafificationAdjunction.{max a b} α).counit.naturality f)

private instance constantExtension_equivalence :
    (constantExtension J Λ R α).IsEquivalence := by
  have : (scalarRestriction J Λ R α ⋙ constantExtension J Λ R α).IsEquivalence :=
    Functor.isEquivalence_of_iso (scalarCounit J Λ R α).symm
  exact Functor.isEquivalence_of_comp_left (scalarRestriction J Λ R α) _

private def scalarUnit : constantExtension J Λ R α ⋙ scalarRestriction J Λ R α ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (constantExtension J Λ R α)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (scalarCounit J Λ R α) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

variable [HasSheafify J (ModuleCat.{max a b} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{max a b} Λ)]

private def constantExtensionMap :
    ((Functor.const Cᵒᵖ) ⋙ constantModulePresheaf (C := C) Λ) ⋙
      PresheafOfModules.sheafification.{max a b} α ⟶
    constantSheaf J (ModuleCat.{max a b} Λ) ⋙ constantExtension J Λ R α :=
  Functor.whiskerRight (Functor.whiskerRight
    (Functor.whiskerLeft (Functor.const Cᵒᵖ)
      (sheafificationAdjunction J (ModuleCat.{max a b} Λ)).unit)
        (constantModulePresheaf (C := C) Λ))
    (PresheafOfModules.sheafification.{max a b} α)

private instance constantExtensionMap_isIso : IsIso (constantExtensionMap J Λ R α) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hw : (J.W.inverseImage (PresheafOfModules.toPresheaf.{max a b} _))
      ((constantModulePresheaf (C := C) Λ).map
        (toSheafify J ((Functor.const Cᵒᵖ).obj M))) := by
    change J.W (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
      (forget₂ (ModuleCat.{max a b} Λ) AddCommGrpCat.{max a b}))
    have : Presheaf.IsLocallyInjective J
        (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (forget₂ (ModuleCat.{max a b} Λ) AddCommGrpCat.{max a b})) := by
      apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
      change Presheaf.IsLocallyInjective J
        (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (CategoryTheory.forget (ModuleCat.{max a b} Λ)))
      infer_instance
    have : Presheaf.IsLocallySurjective J
        (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (forget₂ (ModuleCat.{max a b} Λ) AddCommGrpCat.{max a b})) := by
      apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
      change Presheaf.IsLocallySurjective J
        (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (CategoryTheory.forget (ModuleCat.{max a b} Λ)))
      infer_instance
    exact J.W_of_isLocallyBijective _
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms α] at hw
  exact hw

end Scalars

section Coordinates

attribute [local irreducible] completedAdicChangeData pbcDerivedScalarAdjunction

variable (X : Scheme.{t}) (B : Type t) [CommRing B]
  (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
  (φ : adicConstantRing X B ⟶ R)

private abbrev moduleRing :=
  (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R

private def scalarMap :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{t + 1} B)) ⟶
      (moduleRing X R).obj :=
  koszulConstantUnit X B ≫
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ).hom

private def sliceCoordinates (W : X.Etale) :
    SheafOfModules.{t + 1} ((moduleRing X R).over ((toProEt X).obj W)) ⥤
      Sheaf (ProEt.topology W.left) (ModuleCat.{t + 1} (ULift.{t + 1} B)) := by
  let U := (toProEt X).obj W
  have : (ProEt.sliceEquiv X U).inverse.IsDenseSubsite
      (ProEt.topology W.left) ((ProEt.topology X).over U) := ProEt.sliceDense X U
  exact scalarRestriction ((ProEt.topology X).over U) (ULift.{t + 1} B)
    ((moduleRing X R).over U) (Functor.whiskerLeft (Over.forget U).op (scalarMap X B R φ)) ⋙
    ((ProEt.sliceEquiv X U).sheafCongr ((ProEt.topology X).over U)
      (ProEt.topology W.left) (ModuleCat.{t + 1} (ULift.{t + 1} B))).functor

private instance sliceCoordinates_equivalence [IsIso φ] (W : X.Etale) :
    (sliceCoordinates X B R φ W).IsEquivalence := by
  let U := (toProEt X).obj W
  have := ProEt.sliceDense X U
  have := (koszulConstantUnit_local X B).1
  have := (koszulConstantUnit_local X B).2
  have : Presheaf.IsLocallyInjective (ProEt.topology X) (scalarMap X B R φ) := by
    unfold scalarMap
    infer_instance
  have : Presheaf.IsLocallySurjective (ProEt.topology X) (scalarMap X B R φ) := by
    unfold scalarMap
    infer_instance
  have := Presheaf.isLocallyInjective_whisker ((ProEt.topology X).over U)
    (ProEt.topology X) (Over.forget U) (scalarMap X B R φ)
  have := Presheaf.isLocallySurjective_whisker ((ProEt.topology X).over U)
    (ProEt.topology X) (Over.forget U) (scalarMap X B R φ)
  dsimp only [sliceCoordinates]
  infer_instance

private instance sliceCoordinates_additive [IsIso φ] (W : X.Etale) :
    (sliceCoordinates X B R φ W).Additive :=
  Functor.additive_of_preserves_binary_products _

private instance over_additive (W : X.Etale) :
    (SheafOfModules.overFunctor.{t + 1} (moduleRing X R) ((toProEt X).obj W)).Additive where
  map_add := by intros; rfl

private def globalScalarIso :
    SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ) ⋙
      proEtaleModuleRestriction X B ≅
        scalarRestriction (ProEt.topology X) (ULift.{t + 1} B)
          (moduleRing X R) (scalarMap X B R φ) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private instance scalarRestrictionIso_equivalence [IsIso φ] :
    (SheafOfModules.restrictScalars.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)
    ).IsEquivalence := by
  have := (koszulConstantUnit_local X B).1
  have := (koszulConstantUnit_local X B).2
  have : Presheaf.IsLocallyInjective (ProEt.topology X) (scalarMap X B R φ) := by
    unfold scalarMap
    infer_instance
  have : Presheaf.IsLocallySurjective (ProEt.topology X) (scalarMap X B R φ) := by
    unfold scalarMap
    infer_instance
  have := proEtaleModuleRestriction_isEquivalence X B
  have := Functor.isEquivalence_of_iso (globalScalarIso X B R φ).symm
  exact Functor.isEquivalence_of_comp_right _ (proEtaleModuleRestriction X B)

end Coordinates

end SliceModelTransportProof

end AlgebraicGeometry.Scheme

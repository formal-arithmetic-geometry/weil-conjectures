/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Sheaf.AlgebraicGeometry.ComparisonDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.CategoryTheory.AdditiveDerivedPlusUnitNormalization
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Ordinary intrinsic direct image and its bounded-below comparison

Source: Bhatt--Scholze, Lemma 5.4.3 and Remark 5.4.4; Stacks Tags 070K, 070J and 099R
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison).

All categories below are intrinsic constant-ring module categories. The original sites
have object universe u+1 and morphism universe u; modules live in u+1. Thus these sites
are small relative to their module universe, without identifying the two site universes.
The existing AsSmall comparison data is the equivalent small-model presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry
open Scheme

/-- Intrinsic etale modules, using the recorded constant-ring realization.
Source: Stacks 03CV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev Etale.intrinsicConstantModules (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  SheafOfModules.{u + 1} (Scheme.etaleConstantModuleRing X (ULift.{u + 1, u} B))

/-- Use the recorded continuity of etale base change at the named small topology.
Source: Stacks 03D6 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance Etale.intrinsicBaseChange_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology :=
  Etale.isContinuous_overPullback f

/-- The actual etale scalar map: extend the identical constant sections by sheafification.
Source: Stacks 03D6 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def Etale.intrinsicConstantRingMap {X Y : Scheme.{u}} (f : X ⟶ Y) (B : Type u) [CommRing B] :
    Scheme.etaleConstantModuleRing Y (ULift.{u + 1, u} B) ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        RingCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).obj
          (Scheme.etaleConstantModuleRing X (ULift.{u + 1, u} B)) :=
  ((sheafificationAdjunction Y.smallEtaleTopology RingCat.{u + 1}).homEquiv _ _).symm
    (Functor.whiskerLeft (MorphismProperty.Over.pullback @Etale ⊤ f).op
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B)))))

/-- Intrinsic etale direct image, sectionwise base change and the specified scalar action.
Source: Stacks 03D6 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev Etale.intrinsicModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) (B : Type u) [CommRing B] :
    Etale.intrinsicConstantModules X B ⥤ Etale.intrinsicConstantModules Y B :=
  @SheafOfModules.pushforward.{u + 1} Y.Etale _ X.Etale _
    Y.smallEtaleTopology X.smallEtaleTopology (MorphismProperty.Over.pullback @Etale ⊤ f)
    (Scheme.etaleConstantModuleRing Y (ULift.{u + 1, u} B))
    (Scheme.etaleConstantModuleRing X (ULift.{u + 1, u} B))
    (Etale.intrinsicBaseChange_continuous f) (Etale.intrinsicConstantRingMap f B)

/-- Additivity is the existing sectionwise pushforward construction.
Source: Stacks 03D6 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance Etale.intrinsicModuleDirectImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Type u) [CommRing B] : (Etale.intrinsicModuleDirectImage f B).Additive where
  map_add := rfl

/-- Use the standard localization of the intrinsic etale module category.
Source: Stacks 05RU (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance Etale.intrinsicConstantModules_hasDerivedCategory (X : Scheme.{u})
    (B : Type u) [CommRing B] :
    HasDerivedCategory (Etale.intrinsicConstantModules X B) := HasDerivedCategory.standard _

/-- Enough injectives follows from the published Grothendieck module-sheaf construction.
Source: Stacks 079P (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance Etale.intrinsicConstantModules_grothendieck (X : Scheme.{u}) (B : Type u) [CommRing B] :
    IsGrothendieckAbelian.{u + 1} (Etale.intrinsicConstantModules X B) :=
  SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, u + 1}
    X.smallEtaleTopology (Scheme.etaleConstantModuleRing X (ULift.{u + 1, u} B))

/-- The usual bounded-below derived direct image of intrinsic modules; its unit is
intrinsicModuleDirectImage.rightDerivedFunctorPlusUnit. This is the same localization
and injective-resolution construction as in the recorded abelian presentation.
Source: Stacks 071J, 05TI (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev Etale.intrinsicRightDerivedModuleDirectImagePlus {X Y : Scheme.{u}}
    (f : X ⟶ Y) (B : Type u) [CommRing B] :=
  (Etale.intrinsicModuleDirectImage f B).rightDerivedFunctorPlus

end AlgebraicGeometry

namespace AlgebraicGeometry.SfbOrdinaryComparison
open Scheme

/-- Intrinsic pro-etale modules, with the published commutative constant ring sheaf.
Source: Stacks 03CV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev ProEtale.intrinsicConstantModules (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X B)

/-- Enough injectives on the original pro-etale site, in its module universe.
Source: Stacks 079P (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance proEtale.intrinsicConstantModules_grothendieck (X : Scheme.{u}) (B : Type u) [CommRing B] :
    IsGrothendieckAbelian.{u + 1} (ProEtale.intrinsicConstantModules X B) :=
  SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, u + 1}
    (ProEt.topology X) ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X B))

/-- The intrinsic constant-section ring map for nu, on the original sites. It is the
original-site version of constructibleComparisonRingMap on the equivalent AsSmall sites.
Source: Stacks 099R, 03D2
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def comparisonRingMap (X : Scheme.{u}) (B : Type u) [CommRing B] :
    Scheme.etaleConstantModuleRing X (ULift.{u + 1, u} B) ⟶
      ((toProEt X).sheafPushforwardContinuous RingCat.{u + 1}
        X.smallEtaleTopology (Scheme.ProEt.topology X)).obj
          ((sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (Scheme.proEtaleConstantRing X B)) :=
  ((sheafificationAdjunction X.smallEtaleTopology RingCat.{u + 1}).homEquiv _ _).symm
    (Functor.whiskerLeft (toProEt X).op (ProEtale.finiteCoefficientIntrinsicScalarMap X B))

/-- The sectionwise intrinsic module direct image nu_*.
Source: Stacks 03D6 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev comparisonPushforward (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  SheafOfModules.pushforward.{u + 1} (F := toProEt X)
    (J := X.smallEtaleTopology) (K := ProEt.topology X) (comparisonRingMap X B)

private abbrev proAbSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  letI : EssentiallySmall.{u + 1} X.ProEt :=
    EssentiallySmall.mk' (AsSmall.equiv : X.ProEt ≌ AsSmall.{0} X.ProEt)
  hasSheafifyEssentiallySmallSite _ _

private abbrev proAbLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  letI : EssentiallySmall.{u + 1} X.ProEt :=
    EssentiallySmall.mk' (AsSmall.equiv : X.ProEt ≌ AsSmall.{0} X.ProEt)
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

private theorem presheafPushforward_isRightAdjoint
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) (RX : Dᵒᵖ ⥤ RingCat.{u + 1}) (RY : Cᵒᵖ ⥤ RingCat.{u + 1})
    (ψ : RY ⟶ G.op ⋙ RX) : (PresheafOfModules.pushforward.{u + 1} ψ).IsRightAdjoint := by
  let eX : PresheafOfModules.{u + 1} RX ≌
      PresheafOfModules.{u + 1} ((AsSmall.down.{u, u + 1, 0} (C := D)).op ⋙ RX) :=
    { functor := PresheafOfModules.pushforward₀ (AsSmall.down.{u, u + 1, 0} (C := D)) RX
      inverse := PresheafOfModules.pushforward₀ (AsSmall.up.{u, u + 1, 0} (C := D)) _
      unitIso := Iso.refl _
      counitIso := Iso.refl _ }
  let eY : PresheafOfModules.{u + 1} RY ≌
      PresheafOfModules.{u + 1} ((AsSmall.down.{u, u + 1, 0} (C := C)).op ⋙ RY) :=
    { functor := PresheafOfModules.pushforward₀ (AsSmall.down.{u, u + 1, 0} (C := C)) RY
      inverse := PresheafOfModules.pushforward₀ (AsSmall.up.{u, u + 1, 0} (C := C)) _
      unitIso := Iso.refl _
      counitIso := Iso.refl _ }
  let F := AsSmall.down.{u, u + 1, 0} (C := C) ⋙ G ⋙
    AsSmall.up.{u, u + 1, 0} (C := D)
  let φ : (AsSmall.down.{u, u + 1, 0} (C := C)).op ⋙ RY ⟶
      F.op ⋙ (AsSmall.down.{u, u + 1, 0} (C := D)).op ⋙ RX :=
    Functor.whiskerLeft (AsSmall.down.{u, u + 1, 0} (C := C)).op ψ
  have : (PresheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint := inferInstance
  have : eX.functor.IsRightAdjoint := eX.symm.toAdjunction.isRightAdjoint
  have : eY.inverse.IsRightAdjoint := eY.toAdjunction.isRightAdjoint
  have : (eX.functor ⋙ PresheafOfModules.pushforward φ ⋙ eY.inverse).IsRightAdjoint :=
    inferInstance
  exact this

/-- The canonical comparison module pushforward admits its intrinsic left adjoint.
Source: Stacks 03D2--03D3
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison).

Proof: transport both sites by their AsSmall equivalences to object and morphism
universe u+1, without changing any ring or module sections. On the models the module
presheaf pushforward has the tensor/Kan-extension left adjoint; follow it by module
sheafification. The sheafification adjunction restricts its hom equivalence to module
sheaves. Transport that adjunction back through the two module-site equivalences.
Its right adjoint is the displayed sectionwise pushforward, by the actual ring map
comparisonRingMap. Thus its left adjoint is determined up to the unique adjunction
isomorphism. This is the original-site transport of lem-pe-coefficient-comparison-data. -/
@[instance]
theorem comparisonPushforward_isRightAdjoint (X : Scheme.{u}) (B : Type u) [CommRing B] :
    (comparisonPushforward X B).IsRightAdjoint := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    proAbSheafify X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    proAbLocallyBijective X
  let := presheafPushforward_isRightAdjoint (toProEt X) _ _
    (comparisonRingMap X B).hom
  exact (SheafOfModules.PullbackConstruction.adjunction.{u + 1}
    (comparisonRingMap X B)).isRightAdjoint

/-- The intrinsic module inverse image nu^*, with its specified constant-section map.
Source: Stacks 03D2 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev comparisonPullback (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  SheafOfModules.pullback.{u + 1} (F := toProEt X)
    (J := X.smallEtaleTopology) (K := ProEt.topology X) (comparisonRingMap X B)

section ScalarRestriction

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  (Λ : Type (u + 1)) [CommRing Λ] (R : Sheaf J RingCat.{u + 1})
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

private def scalarRestriction : SheafOfModules.{u + 1} R ⥤
    Sheaf J (ModuleCat.{u + 1} Λ) where
  obj M :=
    let P := (PresheafOfModules.restrictScalars α).obj M.val
    ⟨{ obj := P.obj
       map f := P.map f
       map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
       map_comp f g := by
         ext x
         exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x },
      Presheaf.isSheaf_of_isSheaf_comp J _
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map f :=
    { hom :=
      { app U := (ModuleCat.restrictScalars (α.app U).hom).map (f.val.app U)
        naturality _ _ g := by
          ext x
          exact PresheafOfModules.naturality_apply f.val g x } }

private def scalarHomEquiv (M : Sheaf J (ModuleCat.{u + 1} Λ))
    (N : SheafOfModules.{u + 1} R) :
    ((ProEtale.finiteCoefficientModulePresheaf C Λ).obj M.obj ⟶
      (PresheafOfModules.restrictScalars α).obj N.val) ≃
      (M ⟶ (scalarRestriction J Λ R α).obj N) where
  toFun f :=
    { hom :=
      { app := f.app
        naturality _ _ g := by
          ext x
          exact PresheafOfModules.naturality_apply f g x } }
  invFun f :=
    { app := f.hom.app
      naturality g := by
        ext x
        exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  left_inv f := by ext U x; rfl
  right_inv f := by ext U x; rfl

private def scalarAdjunction :
    (sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
      ProEtale.finiteCoefficientModulePresheaf C Λ ⋙
        PresheafOfModules.sheafification.{u + 1} α) ⊣ scalarRestriction J Λ R α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦
        ((PresheafOfModules.sheafificationAdjunction.{u + 1} α).homEquiv _ _).trans
          (scalarHomEquiv J Λ R α M N)
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        apply (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map_injective
        have h :=
          (PresheafOfModules.sheafificationAdjunction.{u + 1} α).homEquiv_naturality_left_symm
            ((ProEtale.finiteCoefficientModulePresheaf C Λ).map f.hom)
            ((scalarHomEquiv J Λ R α M' N).symm g)
        exact congrArg ((SheafOfModules.forget R ⋙
          PresheafOfModules.toPresheaf R.obj).map) h
      homEquiv_naturality_right := by
        intro M N N' f g
        ext U x
        rfl }

private theorem scalarRealization_equivalence :
    (sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
      ProEtale.finiteCoefficientModulePresheaf C Λ ⋙
        PresheafOfModules.sheafification.{u + 1} α).IsEquivalence := by
  let P := ProEtale.finiteCoefficientModulePresheaf C Λ
  have hP : P.FullyFaithful :=
    { preimage := fun f ↦
        { app := f.app
          naturality _ _ g := by
            ext x
            exact PresheafOfModules.naturality_apply f g x }
      map_preimage := fun f ↦ by ext U x; rfl
      preimage_map := fun f ↦ by ext U x; rfl }
  have : P.Full := hP.full
  have : P.Faithful := hP.faithful
  let E := sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙ P
  let S := PresheafOfModules.sheafification.{u + 1} α
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α
  have hunit (M : Sheaf J (ModuleCat.{u + 1} Λ)) :
      IsIso ((PresheafOfModules.sheafificationAdjunction α).unit.app (E.obj M)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose J
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M).property
  let η : E ⟶ (E ⋙ S) ⋙ G :=
    Functor.whiskerLeft E (PresheafOfModules.sheafificationAdjunction α).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hunit
  have : (E ⋙ S).Faithful := Functor.Faithful.of_comp_iso (asIso η).symm
  have : (E ⋙ S).Full := Functor.Full.of_comp_faithful_iso (asIso η).symm
  have : (E ⋙ S).EssSurj := by
    refine ⟨fun M ↦ ?_⟩
    refine ⟨(scalarRestriction J Λ R α).obj M, ⟨?_⟩⟩
    exact asIso ((PresheafOfModules.sheafificationAdjunction α).counit.app M)
  change (E ⋙ S).IsEquivalence
  exact Functor.IsEquivalence.mk

private theorem scalarRestriction_equivalence : (scalarRestriction J Λ R α).IsEquivalence := by
  have := scalarRealization_equivalence J Λ R α
  exact (scalarAdjunction J Λ R α).isEquivalence_right_of_isEquivalence_left

end ScalarRestriction

section ScalarDirect

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (Λ : Type (u + 1)) [CommRing Λ]
  (R : Sheaf J RingCat.{u + 1}) (S : Sheaf K RingCat.{u + 1})
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
  (β : (Functor.const Dᵒᵖ).obj (RingCat.of Λ) ⟶ S.obj)
  (F : C ⥤ D) [F.IsContinuous J K]
  (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S)
  (h : ∀ (U : Cᵒᵖ) (a : Λ), (φ.hom.app U) (α.app U a) = β.app (F.op.obj U) a)

private def scalarDirectComparison :
    SheafOfModules.pushforward.{u + 1} φ ⋙ scalarRestriction J Λ R α ≅
      scalarRestriction K Λ S β ⋙ F.sheafPushforwardContinuous (ModuleCat.{u + 1} Λ) J K := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine { hom := ?_, inv := ?_, hom_inv_id := ?_, inv_hom_id := ?_ }
    · refine ⟨{ app := fun U ↦ ?_, naturality := ?_ }⟩
      · refine ConcreteCategory.ofHom (C := ModuleCat Λ)
          { toFun := id
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun a x ↦ ?_ }
        change (φ.hom.app U) (α.app U a) • (show M.val.obj (F.op.obj U) from x) = _
        rw [h]
        rfl
      · intros
        ext x
        rfl
    · refine ⟨{ app := fun U ↦ ?_, naturality := ?_ }⟩
      · refine ConcreteCategory.ofHom (C := ModuleCat Λ)
          { toFun := id
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun a x ↦ ?_ }
        change _ = (φ.hom.app U) (α.app U a) • (show M.val.obj (F.op.obj U) from x)
        rw [h]
        rfl
      · intros
        ext x
        rfl
    · ext U x
      rfl
    · ext U x
      rfl
  · intros
    ext U x
    rfl

variable [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [Presheaf.IsLocallyInjective K β] [Presheaf.IsLocallySurjective K β]
  [HasSheafify J AddCommGrpCat.{u + 1}] [HasSheafify K AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [(SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint]

private def scalarPullComparison :
    SheafOfModules.pullback.{u + 1} φ ⋙ scalarRestriction K Λ S β ≅
      scalarRestriction J Λ R α ⋙
        Functor.sheafPullbackConstruction.sheafPullback F (ModuleCat.{u + 1} Λ) J K := by
  have := scalarRestriction_equivalence J Λ R α
  have := scalarRestriction_equivalence K Λ S β
  let a := SheafOfModules.pullbackPushforwardAdjunction.{u + 1} φ
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    F (ModuleCat.{u + 1} Λ) J K
  let e := scalarDirectComparison J K Λ R S α β F φ h
  let t := ((mateEquiv a b).symm e.hom).natTrans
  have : IsIso t := isIso_inverseMate_of_equivalences a b e
  exact (asIso t).symm

end ScalarDirect

private abbrev etaleRestriction (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  scalarRestriction X.smallEtaleTopology (ULift.{u + 1, u} B)
    (etaleConstantModuleRing X (ULift.{u + 1, u} B))
    (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B))))

private abbrev proEtaleRestriction (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  scalarRestriction (ProEt.topology X) (ULift.{u + 1, u} B)
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing X B)) (ProEtale.finiteCoefficientIntrinsicScalarMap X B)

private instance etaleRestriction_equivalence (X : Scheme.{u}) (B : Type u) [CommRing B] :
    (etaleRestriction X B).IsEquivalence := scalarRestriction_equivalence _ _ _ _

private instance proEtaleRestriction_equivalence (X : Scheme.{u}) (B : Type u) [CommRing B] :
    (proEtaleRestriction X B).IsEquivalence := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    proAbSheafify X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    proAbLocallyBijective X
  have := (proEtaleConstantRingUnit_locallyBijective X B).1
  have := (proEtaleConstantRingUnit_locallyBijective X B).2
  exact scalarRestriction_equivalence _ _ _ _

private theorem comparisonRingMap_unit (X : Scheme.{u}) (B : Type u) [CommRing B]
    (U : X.Etaleᵒᵖ) (a : ULift.{u + 1, u} B) :
    (comparisonRingMap X B).hom.app U
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B)))).app U a) =
      (ProEtale.finiteCoefficientIntrinsicScalarMap X B).app ((toProEt X).op.obj U) a := by
  have h :
      toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B))) ≫
        (comparisonRingMap X B).hom =
      Functor.whiskerLeft (toProEt X).op (ProEtale.finiteCoefficientIntrinsicScalarMap X B) := by
    exact (sheafificationAdjunction X.smallEtaleTopology RingCat.{u + 1}).homEquiv
      ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B)))
      (((toProEt X).sheafPushforwardContinuous RingCat.{u + 1}
        X.smallEtaleTopology (ProEt.topology X)).obj _) |>.apply_symm_apply _
  exact congrArg (fun t ↦ (t.app U) a) h

private def comparisonRestrictionIso (X : Scheme.{u}) (B : Type u) [CommRing B] :
    comparisonPushforward X B ⋙ etaleRestriction X B ≅
      proEtaleRestriction X B ⋙
        ProEtale.comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X :=
  scalarDirectComparison _ _ _ _ _ _ _ _ _ (comparisonRingMap_unit X B)

private def comparisonPullRestrictionIso (X : Scheme.{u}) (B : Type u) [CommRing B] :
    comparisonPullback X B ⋙ proEtaleRestriction X B ≅
      etaleRestriction X B ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    proAbSheafify X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    proAbLocallyBijective X
  have := (proEtaleConstantRingUnit_locallyBijective X B).1
  have := (proEtaleConstantRingUnit_locallyBijective X B).2
  exact scalarPullComparison _ _ _ _ _ _ _ _ _ (comparisonRingMap_unit X B)

/-- Exactness of the intrinsic comparison inverse image.
Source: Stacks 00YV, 03D2 and 09AL
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison).

Proof: step 6 identifies the inverse-image constant ring using constant sections and
lem-pe-constant-left-module-inverse-image. The module inverse-image unit comparison
identifies the underlying abelian functor and unit. Exactness of geometric inverse
image therefore gives finite-limit preservation; the module adjunction gives finite
colimits and additivity. This is lem-pe-coefficient-comparison-derived-functor on the
original sites, transported through their AsSmall equivalences. -/
theorem comparisonPullback_exact (X : Scheme.{u}) (B : Type u) [CommRing B] :
    (comparisonPullback X B).Additive ∧
      PreservesFiniteLimits (comparisonPullback X B) ∧
      PreservesFiniteColimits (comparisonPullback X B) := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    proAbSheafify X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    proAbLocallyBijective X
  have := (proEtaleConstantRingUnit_locallyBijective X B).1
  have := (proEtaleConstantRingUnit_locallyBijective X B).2
  have : (etaleRestriction X B).IsEquivalence :=
    scalarRestriction_equivalence _ _ _ _
  have : (proEtaleRestriction X B).IsEquivalence :=
    scalarRestriction_equivalence _ _ _ _
  have : PreservesFiniteLimits (comparisonPullback X B ⋙ proEtaleRestriction X B) :=
    preservesFiniteLimits_of_natIso (comparisonPullRestrictionIso X B).symm
  have : PreservesFiniteLimits (comparisonPullback X B) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (proEtaleRestriction X B)
  have : PreservesFiniteColimits (comparisonPullback X B) := inferInstance
  have : (comparisonPullback X B).Additive := Functor.additive_of_preserves_binary_products _
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Published exactness, for termwise localization.
Source: Stacks 09AL (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance comparisonPullback_additive (X : Scheme.{u}) (B : Type u) [CommRing B] :
    (comparisonPullback X B).Additive := (comparisonPullback_exact X B).1

/-- Published left exactness of the canonical inverse image.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance comparisonPullback_limits (X : Scheme.{u}) (B : Type u) [CommRing B] :
    PreservesFiniteLimits (comparisonPullback X B) := (comparisonPullback_exact X B).2.1

/-- Published right exactness of the canonical inverse image.
Source: Stacks 03D3 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance comparisonPullback_colimits (X : Scheme.{u}) (B : Type u) [CommRing B] :
    PreservesFiniteColimits (comparisonPullback X B) := (comparisonPullback_exact X B).2.2

/-- The existing etale realization, without a copied category or scalar action.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev etaleRealization (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  Scheme.etaleConstantModuleFunctor X (ULift.{u + 1, u} B)

/-- The existing equivalence theorem supplies the coefficient realization structure.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance etaleRealization_equivalence (X : Scheme.{u}) (B : Type u) [CommRing B] :
    (etaleRealization X B).IsEquivalence :=
  Scheme.etaleConstantModuleFunctor_isEquivalence X (ULift.{u + 1, u} B)

/-- Additivity follows from preservation of binary products by the equivalence.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance etaleRealization_additive (X : Scheme.{u}) (B : Type u) [CommRing B] :
    (etaleRealization X B).Additive := Functor.additive_of_preserves_binary_products _

/-- The inverse of the existing etale coefficient equivalence, with its actual unit.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def etaleEquivalence (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  (etaleRealization X B).asEquivalence

/-- Constant-section inverse image in the fixed-scalar presentation, transported through
both published coefficient equivalences.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def transportedComparison (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B] :=
  (etaleEquivalence X B).inverse ⋙
    ProEtale.finiteCoefficientIntrinsicComparison X B

/-- The canonical module-sheafification unit of pro-etale coefficient realization.
Source: Stacks 03CV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def proEtaleRealizationUnit (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
  (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap X B)).unit.app
      ((ProEtale.finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} B)).obj M.obj)

private def comparisonTransportedAdjunction (X : Scheme.{u}) (B : Type u)
    [CommRing B] [Finite B] : transportedComparison X B ⊣ comparisonPushforward X B := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    proAbSheafify X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    proAbLocallyBijective X
  let a := (scalarAdjunction (ProEt.topology X) (ULift.{u + 1, u} B)
    _ (ProEtale.finiteCoefficientIntrinsicScalarMap X B))
  let c : etaleRestriction X B ⋙ etaleRealization X B ≅ 𝟭 _ :=
    Scheme.etaleConstantModuleCounitIso X (ULift.{u + 1, u} B)
  let e : proEtaleRestriction X B ⋙
      ProEtale.comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X ⋙
        etaleRealization X B ≅ comparisonPushforward X B :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (comparisonRestrictionIso X B).symm _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ c ≪≫ Functor.rightUnitor _
  let adj := ((etaleEquivalence X B).symm.toAdjunction.comp
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X)).comp a
  exact adj.ofNatIsoRight e

private theorem comparisonTransportedAdjunction_sections (X : Scheme.{u}) (B : Type u)
    [CommRing B] [Finite B]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (V : X.Etaleᵒᵖ) (x : M.obj.obj V) :
    ((comparisonTransportedAdjunction X B).unit.app ((etaleRealization X B).obj M)).val.app
        V x =
      (proEtaleRealizationUnit X B
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).obj
          ((etaleEquivalence X B).inverse.obj ((etaleRealization X B).obj M)))).app
        ((toProEt X).op.obj V)
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).map
          ((etaleEquivalence X B).unitIso.hom.app M)).hom.app ((toProEt X).op.obj V)
          (((ProEtale.comparisonAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).unit.app M).hom.app V x)) := by
  let E := etaleEquivalence X B
  let N := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).obj (E.inverse.obj (E.functor.obj M))
  let y := ((ProEtale.comparisonAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).unit.app
      (E.inverse.obj (E.functor.obj M))).hom.app V
        ((E.counitIso.inv.app (E.functor.obj M)).val.app V x)
  have hc (T : Etale.intrinsicConstantModules X B) (t : T.val.obj V) :
      ((Scheme.etaleConstantModuleCounitIso X (ULift.{u + 1, u} B)).hom.app T).val.app V t =
        t := by
    exact congrArg (fun k ↦ k.app V t)
      (Scheme.etaleConstantModuleCounitHom_underlying X (ULift.{u + 1, u} B) T)
  have hfirst :
      ((comparisonTransportedAdjunction X B).unit.app ((etaleRealization X B).obj M)).val.app
          V x = (proEtaleRealizationUnit X B N).app ((toProEt X).op.obj V) y := by
    simp only [comparisonTransportedAdjunction, Adjunction.ofNatIsoRight_unit,
      NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_unit_app,
      Iso.trans_hom, Iso.symm_hom, Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.rightUnitor_hom_app, Category.id_comp]
    change ((Scheme.etaleConstantModuleCounitIso X (ULift.{u + 1, u} B)).hom.app
      ((comparisonPushforward X B).obj
        ((transportedComparison X B).obj ((etaleRealization X B).obj M)))).val.app
      V ((proEtaleRealizationUnit X B N).app ((toProEt X).op.obj V) y) = _
    exact hc _ _
  rw [hfirst]
  congr 1
  have hE : E.counitIso.inv.app (E.functor.obj M) = E.functor.map (E.unitIso.hom.app M) := by
    apply (cancel_mono (E.counitIso.hom.app (E.functor.obj M))).mp
    rw [Iso.inv_hom_id_app]
    exact (E.functor_unitIso_comp M).symm
  dsimp [y]
  rw [hE]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.hom.app V)
      ((ProEtale.comparisonAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).unit.naturality
          (E.unitIso.hom.app M))) x

attribute [local irreducible] comparisonTransportedAdjunction

private theorem etaleRingMap_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Type u) [CommRing B] (U : Y.Etaleᵒᵖ) (a : ULift.{u + 1, u} B) :
    (Etale.intrinsicConstantRingMap f B).hom.app U
      ((toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B)))).app U a) =
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B)))).app
          ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U) a := by
  have h :
      toSheafify Y.smallEtaleTopology
          ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B))) ≫
        (Etale.intrinsicConstantRingMap f B).hom =
      Functor.whiskerLeft (MorphismProperty.Over.pullback @Etale ⊤ f).op
        (toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B)))) := by
    exact (sheafificationAdjunction Y.smallEtaleTopology RingCat.{u + 1}).homEquiv
      ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B)))
      (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous RingCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology).obj _) |>.apply_symm_apply _
  exact congrArg (fun t ↦ (t.app U) a) h

private def etaleDirectRestrictionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Type u) [CommRing B] :
    Etale.intrinsicModuleDirectImage f B ⋙ etaleRestriction Y B ≅
      etaleRestriction X B ⋙ Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f :=
  letI := Etale.intrinsicBaseChange_continuous f
  scalarDirectComparison.{u} Y.smallEtaleTopology X.smallEtaleTopology
    (ULift.{u + 1, u} B) _ _ _ _ (MorphismProperty.Over.pullback @Etale ⊤ f)
    (Etale.intrinsicConstantRingMap f B) (etaleRingMap_unit f B)

private def etaleDirectRealizationIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Type u) [CommRing B] :
    Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f ⋙ etaleRealization Y B ≅
      etaleRealization X B ⋙ Etale.intrinsicModuleDirectImage f B := by
  let eX : etaleRealization X B ⋙ etaleRestriction X B ≅ 𝟭 _ :=
    (Scheme.etaleConstantModuleUnitIso X (ULift.{u + 1, u} B)).symm
  let eY : etaleRealization Y B ⋙ etaleRestriction Y B ≅ 𝟭 _ :=
    (Scheme.etaleConstantModuleUnitIso Y (ULift.{u + 1, u} B)).symm
  let F := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f
  let e : (F ⋙ etaleRealization Y B) ⋙ etaleRestriction Y B ≅
      (etaleRealization X B ⋙ Etale.intrinsicModuleDirectImage f B) ⋙ etaleRestriction Y B :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft F eY ≪≫ Functor.rightUnitor F ≪≫
      (Functor.leftUnitor F).symm ≪≫ isoWhiskerRight eX.symm F ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (etaleDirectRestrictionIso f B).symm ≪≫
      (Functor.associator _ _ _).symm
  exact Functor.fullyFaithfulCancelRight (etaleRestriction Y B) e

private theorem etaleDirectRealizationIso_sections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Type u) [CommRing B]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (U : Y.Etaleᵒᵖ)
    (x : M.obj.obj ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U)) :
    ((etaleDirectRealizationIso f B).hom.app M).val.app U x = x := by
  change (((etaleRestriction Y B).map
    ((etaleDirectRealizationIso f B).hom.app M)).hom.app U) x = x
  simp only [etaleDirectRealizationIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Category.id_comp, Category.comp_id]
  change ((Scheme.etaleConstantModuleUnitIso Y (ULift.{u + 1, u} B)).inv.app
    ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj M)).hom.app U x = x
  exact congrArg (fun t ↦ t.hom.app U x)
    ((Scheme.etaleConstantModuleUnitIso Y (ULift.{u + 1, u} B)).hom_inv_id_app
      ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj M))

attribute [local irreducible] etaleDirectRealizationIso

attribute [local irreducible] Functor.rightDerivedFunctorPlus Functor.rightDerivedFunctorPlusUnit
  Functor.mapDerivedCategoryPlus Functor.mapDerivedCategory
  Functor.rightDerivedFunctorOfQuasiIsoResolutions
  Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit
  Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso

-- Preserve the generated API below, using direct proofs instead of expensive
-- automatically generated injectivity proofs for the derived-normalization bundle.
set_option genInjectivity false

/-- All parts of a total-derived/bounded-below identification, including its units.
This is a bundle of the clauses of this node, rather than a new derived category.
Source: Stacks 070K, 070J and 05TI
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
structure RightDerivedNormalization {C : Type a} {D : Type b}
    [Category.{c} C] [Category.{d} D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] where
  resolutions : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s
  plusIso : DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions resolutions ≅
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι
  unit_eq : ∀ K : HomotopyCategory.Plus C,
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit resolutions).app K.obj ≫
      plusIso.hom.app (DerivedCategory.Plus.Qh.obj K) =
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K)
  plus_computes : ∀ (K : HomotopyCategory.Plus C),
    (∀ n : ℤ, Injective (K.obj.as.X n)) → IsIso (F.rightDerivedFunctorPlusUnit.app K)

set_option genInjectivity true

section NormalizationInjectivity
variable {C : Type a} {D : Type b} [Category.{c} C] [Category.{d} D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives C] {F : C ⥤ D} [F.Additive]
  (h h' : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
  (e : DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h ≅
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
  (e' : DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h' ≅
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
  (he : ∀ K : HomotopyCategory.Plus C,
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app K.obj ≫
      e.hom.app (DerivedCategory.Plus.Qh.obj K) =
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K))
  (he' : ∀ K : HomotopyCategory.Plus C,
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h').app K.obj ≫
      e'.hom.app (DerivedCategory.Plus.Qh.obj K) =
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K))
  (hc hc' : ∀ K : HomotopyCategory.Plus C,
    (∀ n : ℤ, Injective (K.obj.as.X n)) → IsIso (F.rightDerivedFunctorPlusUnit.app K))

/-- Constructor equality for the normalization bundle, retaining the generated simp API.
Source: proof irrelevance and structure equality
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
@[simp] theorem RightDerivedNormalization.mk.injEq :
    (RightDerivedNormalization.mk h e he hc = RightDerivedNormalization.mk h' e' he' hc') =
      (e = e') := by
  apply propext
  constructor
  · intro q
    cases q
    rfl
  · intro q
    cases q
    rfl

/-- Constructor injectivity for the normalization bundle, retaining the generated API.
Source: structure equality
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
theorem RightDerivedNormalization.mk.inj
    {h h' : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s}
    {e : DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h ≅
      F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι}
    {e' : DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h' ≅
      F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι}
    {he : ∀ K : HomotopyCategory.Plus C,
      (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app K.obj ≫
        e.hom.app (DerivedCategory.Plus.Qh.obj K) =
          DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K)}
    {he' : ∀ K : HomotopyCategory.Plus C,
      (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h').app K.obj ≫
        e'.hom.app (DerivedCategory.Plus.Qh.obj K) =
          DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K)}
    {hc hc' : ∀ K : HomotopyCategory.Plus C,
      (∀ n : ℤ, Injective (K.obj.as.X n)) → IsIso (F.rightDerivedFunctorPlusUnit.app K)} :
    RightDerivedNormalization.mk h e he hc = RightDerivedNormalization.mk h' e' he' hc' →
      e = e' := by
  intro q
  cases q
  rfl

end NormalizationInjectivity

private theorem rightDerivedNormalization_exists
    {C : Type a} {D : Type b} [Category.{c} C] [Category.{d} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s) :
    Nonempty (RightDerivedNormalization F) := by
  obtain ⟨θ, hθ, _, _, hJ⟩ :=
    (F.additiveDerivedPlus_unit_normalization h F.rightDerivedFunctorPlus
      F.rightDerivedFunctorPlusUnit).2.2
  refine ⟨⟨h, θ, hθ, ?_⟩⟩
  intro K hK
  obtain ⟨_, hα, _⟩ := hJ K hK
  exact hα

/-- Use exactly the recorded ordinary right derived functor, on arbitrary K-injective
resolutions. Its published unit, universal property and computation are unchanged.
Source: Stacks 070K (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev RightDerivedNormalization.full {C : Type a} {D : Type b}
    [Category.{c} C] [Category.{d} D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    {F : C ⥤ D} [F.Additive] (r : RightDerivedNormalization F) :=
  F.rightDerivedFunctorOfQuasiIsoResolutions r.resolutions

/-- The canonical value on every quasi-isomorphism to a K-injective, without a mono
hypothesis: use the recorded resolution comparison, RF(Qs) followed by the inverse unit.
Source: Stacks 070K (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev RightDerivedNormalization.resolutionIso {C : Type a} {D : Type b}
    [Category.{c} C] [Category.{d} D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    {F : C ⥤ D} [F.Additive] (r : RightDerivedNormalization F)
    {M I : CochainComplex C ℤ} (s : M ⟶ I) [QuasiIso s] [I.IsKInjective] :
    r.full.obj (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) :=
  F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso r.resolutions s

/-- Unit-preserving identification of the two inverse-image presentations, as left
adjoints to exactly the same sectionwise intrinsic module direct image. The unit on
sections is the fixed comparison unit followed by coefficient realization, fixing
the adjunction as well as the isomorphism.
Source: Stacks 03D2--03D3
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
structure ComparisonIdentification (X : Scheme.{u}) (B : Type u)
    [CommRing B] [Finite B] where
  adjunction : transportedComparison X B ⊣ comparisonPushforward X B
  unit_sections : ∀ (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) (V : X.Etaleᵒᵖ) (x : M.obj.obj V),
    (adjunction.unit.app ((etaleRealization X B).obj M)).val.app V x =
      (proEtaleRealizationUnit X B
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).obj
          ((etaleEquivalence X B).inverse.obj ((etaleRealization X B).obj M)))).app
        ((toProEt X).op.obj V)
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).map
          ((etaleEquivalence X B).unitIso.hom.app M)).hom.app ((toProEt X).op.obj V)
          (((ProEtale.comparisonAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).unit.app M).hom.app V x))
  iso : comparisonPullback X B ≅ transportedComparison X B
  unit_eq : ∀ M : Etale.intrinsicConstantModules X B,
    (SheafOfModules.pullbackPushforwardAdjunction (comparisonRingMap X B)).unit.app M ≫
      (comparisonPushforward X B).map (iso.hom.app M) = adjunction.unit.app M
  unique : ∀ e : comparisonPullback X B ≅ transportedComparison X B,
    (∀ M : Etale.intrinsicConstantModules X B,
      (SheafOfModules.pullbackPushforwardAdjunction (comparisonRingMap X B)).unit.app M ≫
        (comparisonPushforward X B).map (e.hom.app M) = adjunction.unit.app M) → e = iso

private theorem comparisonIdentification_exists (X : Scheme.{u}) (B : Type u)
    [CommRing B] [Finite B] : Nonempty (ComparisonIdentification X B) := by
  let adj := comparisonTransportedAdjunction X B
  let adj₀ := SheafOfModules.pullbackPushforwardAdjunction (comparisonRingMap X B)
  let e := adj₀.leftAdjointUniq adj
  refine ⟨⟨adj, comparisonTransportedAdjunction_sections X B, e,
    adj₀.unit_leftAdjointUniq_hom_app adj, ?_⟩⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (adj₀.homEquiv _ _).injective
  simpa only [Adjunction.homEquiv_unit] using
    (he' M).trans (adj₀.unit_leftAdjointUniq_hom_app adj M).symm

/-- Cancel the existing etale realization equivalence in the inverse-image identification.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def realizedComparisonIso (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (i : ComparisonIdentification X B) :
    etaleRealization X B ⋙ comparisonPullback X B ≅
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X ⋙
        ProEtale.finiteCoefficientIntrinsicRealization X B :=
  isoWhiskerLeft (etaleRealization X B) i.iso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (etaleEquivalence X B).unitIso.symm _ ≪≫ Functor.leftUnitor _

/-- Termwise localization of this exact coefficient identification on D+.
Source: Stacks 09AL (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def realizedComparisonPlusIso (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (i : ComparisonIdentification X B) :
    (etaleRealization X B).mapDerivedCategoryPlus ⋙
        (comparisonPullback X B).mapDerivedCategoryPlus ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).mapDerivedCategoryPlus ⋙
          (ProEtale.finiteCoefficientIntrinsicRealization X B).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (realizedComparisonIso X B i) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The direct-image changes of coefficient presentation, normalized on sections, and
exactly their derived base-change transformations, rather than chosen derived isomorphisms.
Source: Stacks 03D6, 05TI, 099R
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
structure CoefficientNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Type u) [CommRing B] [Finite B] where
  etale : Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f ⋙
      etaleRealization Y B ≅ etaleRealization X B ⋙ Etale.intrinsicModuleDirectImage f B
  etale_sections : ∀ (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) (V : Y.Etaleᵒᵖ)
      (x : M.obj.obj ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj V)),
    (etale.hom.app M).val.app V x = x
  proetale : ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f ⋙
      ProEtale.finiteCoefficientIntrinsicRealization Y B ≅
    ProEtale.finiteCoefficientIntrinsicRealization X B ⋙
      Scheme.proEtaleConstantModuleDirectImage f B
  proetale_sections : ∀ (M : Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) (V : Y.ProEtᵒᵖ)
      (x : M.obj.obj ((Scheme.proEtaleBaseChange f).op.obj V)),
    (proetale.hom.app M).val.app V
      ((proEtaleRealizationUnit Y B
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj M)).app V x) =
      (proEtaleRealizationUnit X B M).app ((Scheme.proEtaleBaseChange f).op.obj V) x
  etalePlus :
    (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).rightDerivedFunctorPlus ⋙
        (etaleRealization Y B).mapDerivedCategoryPlus ≅
      (etaleRealization X B).mapDerivedCategoryPlus ⋙
        (Etale.intrinsicModuleDirectImage f B).rightDerivedFunctorPlus
  etalePlus_eq : etalePlus.hom = Functor.rightDerivedFunctorPlusBaseChange etale.hom
  proetalePlus :
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).rightDerivedFunctorPlus ⋙
        (ProEtale.finiteCoefficientIntrinsicRealization Y B).mapDerivedCategoryPlus ≅
      (ProEtale.finiteCoefficientIntrinsicRealization X B).mapDerivedCategoryPlus ⋙
        (Scheme.proEtaleConstantModuleDirectImage f B).rightDerivedFunctorPlus
  proetalePlus_eq : proetalePlus.hom = Functor.rightDerivedFunctorPlusBaseChange proetale.hom

private theorem coefficientNormalization_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Type u) [CommRing B] [Finite B] : Nonempty (CoefficientNormalization f B) := by
  let := Etale.intrinsicBaseChange_continuous f
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} := proAbSheafify X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    proAbLocallyBijective X
  let e := etaleDirectRealizationIso f B
  obtain ⟨p, hp, _⟩ := Scheme.sfIntrinsicDirectImageComparison_existsUnique f B
  have heR : (Etale.intrinsicModuleDirectImage f B).IsRightAdjoint := by
    let := presheafPushforward_isRightAdjoint (MorphismProperty.Over.pullback @Etale ⊤ f)
      _ _ (Etale.intrinsicConstantRingMap f B).hom
    exact (SheafOfModules.PullbackConstruction.adjunction.{u + 1}
      (Etale.intrinsicConstantRingMap f B)).isRightAdjoint
  have hpR : (Scheme.proEtaleConstantModuleDirectImage f B).IsRightAdjoint := by
    let φ := (show (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (Scheme.proEtaleConstantRing Y B) ⟶
      ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (Scheme.proEtaleConstantRing X B)) from
      ⟨Functor.whiskerRight (Scheme.proEtaleCoefficientDirectImageMap f B).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)
    let := presheafPushforward_isRightAdjoint (Scheme.proEtaleBaseChange f) _ _ φ.hom
    exact (SheafOfModules.PullbackConstruction.adjunction.{u + 1} φ).isRightAdjoint
  have heI (I : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) [Injective I] :
      (Etale.intrinsicModuleDirectImage f B).rightAcyclic ((etaleRealization X B).obj I) := by
    have : Injective ((etaleRealization X B).obj I) :=
      (etaleEquivalence X B).symm.toAdjunction.map_injective I inferInstance
    exact Functor.rightAcyclic_of_injective _
  have hpI (I : Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) [Injective I] :
      (Scheme.proEtaleConstantModuleDirectImage f B).rightAcyclic
        ((ProEtale.finiteCoefficientIntrinsicRealization X B).obj I) := by
    have : Injective ((ProEtale.finiteCoefficientIntrinsicRealization X B).obj I) :=
      (Scheme.sfIntrinsicModuleEquivalence X B).symm.toAdjunction.map_injective I inferInstance
    exact Functor.rightAcyclic_of_injective _
  have he : IsIso (Functor.rightDerivedFunctorPlusBaseChange e.hom) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic e heI
  have hp' : IsIso (Functor.rightDerivedFunctorPlusBaseChange p.inv) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic p.symm hpI
  refine ⟨⟨e, etaleDirectRealizationIso_sections f B, p.symm, ?_,
    asIso (Functor.rightDerivedFunctorPlusBaseChange e.hom), rfl,
    asIso (Functor.rightDerivedFunctorPlusBaseChange p.inv), rfl⟩⟩
  intro M V x
  change (p.inv.app M).val.app V
    (Scheme.sfIntrinsicRealizationUnit Y B
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj M) V x) =
    Scheme.sfIntrinsicRealizationUnit X B M ((Scheme.proEtaleBaseChange f).op.obj V) x
  rw [← hp M V x]
  exact congrArg (fun t ↦ t.val.app V
    (Scheme.sfIntrinsicRealizationUnit X B M ((Scheme.proEtaleBaseChange f).op.obj V) x))
    (p.hom_inv_id_app M)

private theorem mapDerivedPlus_equivalence
    {C : Type a} {D : Type b} [Category.{c} C] [Category.{d} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ≌ D) [E.functor.Additive] [E.inverse.Additive] :
    E.functor.mapDerivedCategoryPlus.IsEquivalence := by
  let h : 𝟭 (DerivedCategory.Plus C) ≅
      E.functor.mapDerivedCategoryPlus ⋙ E.inverse.mapDerivedCategoryPlus :=
    (Functor.mapDerivedCategoryPlusIdIso C).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso E.unitIso ≪≫
      Functor.mapDerivedCategoryPlusCompIso _ _
  let k : E.inverse.mapDerivedCategoryPlus ⋙ E.functor.mapDerivedCategoryPlus ≅
      𝟭 (DerivedCategory.Plus D) :=
    (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso E.counitIso ≪≫ Functor.mapDerivedCategoryPlusIdIso D
  exact (CategoryTheory.Equivalence.mk _ _ h k).isEquivalence_functor

section ComparisonTransport

variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Category D₁] [Category D₂] [Category D₃] [Category D₄]
  (E : C₁ ⥤ D₁) [E.IsEquivalence] (EY : C₂ ⥤ D₂)
  (PX : C₃ ⥤ D₃) (PY : C₄ ⥤ D₄)
  (A : C₁ ⥤ C₂) (Q : C₃ ⥤ C₄) (C : C₁ ⥤ C₃) (D : C₂ ⥤ C₄)
  (F : D₁ ⥤ D₂) (P : D₃ ⥤ D₄) (L : D₁ ⥤ D₃) (R : D₂ ⥤ D₄)
  (e : A ⋙ EY ≅ E ⋙ F) (q : Q ⋙ PY ≅ PX ⋙ P)
  (x : E ⋙ L ≅ C ⋙ PX) (y : EY ⋙ R ≅ D ⋙ PY) (b : A ⋙ D ≅ C ⋙ Q)

private def comparisonTransportIso : E ⋙ (F ⋙ R) ≅ E ⋙ (L ⋙ P) :=
    (Functor.associator E F R).symm ≪≫ isoWhiskerRight e.symm R ≪≫
      Functor.associator A EY R ≪≫ isoWhiskerLeft A y ≪≫
      (Functor.associator A D PY).symm ≪≫ isoWhiskerRight b PY ≪≫
      Functor.associator C Q PY ≪≫ isoWhiskerLeft C q ≪≫
      (Functor.associator C PX P).symm ≪≫ isoWhiskerRight x.symm P ≪≫
      Functor.associator E L P

private def transportedComparisonIso : F ⋙ R ≅ L ⋙ P :=
  ((whiskeringLeft _ _ _).obj E).preimageIso
    (comparisonTransportIso E EY PX PY A Q C D F P L R e q x y b)

private theorem transportedComparisonIso_app (G : C₁) :
    (transportedComparisonIso E EY PX PY A Q C D F P L R e q x y b).hom.app (E.obj G) =
      R.map (e.inv.app G) ≫ y.hom.app (A.obj G) ≫ PY.map (b.hom.app G) ≫
        q.hom.app (C.obj G) ≫ P.map (x.inv.app G) := by
  have h := congrArg (fun t ↦ t.app G)
    (((whiskeringLeft _ _ _).obj E).map_preimage
      (comparisonTransportIso E EY PX PY A Q C D F P L R e q x y b).hom)
  simp only [comparisonTransportIso, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.comp_obj, Category.id_comp,
    Category.comp_id] at h
  exact h.trans (Category.id_comp _)

end ComparisonTransport

attribute [local irreducible] scalarAdjunction scalarDirectComparison scalarPullComparison
  transportedComparisonIso
  comparisonTransportIso

/-- Ordinary total derived direct images, their unit-normalized bounded-below restrictions,
and the specified etale/pro-etale comparison after inclusion in the full derived category.
Source: Bhatt--Scholze, Lemma 5.4.3 and Remark 5.4.4; Stacks 070K, 070J, 099R
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison).

Proof, following all seven steps of the DAG node:
1. Apply prop-pur-kinjective-resolutions-exist to the intrinsic constant-ring module
   categories on the small sites. They are Grothendieck abelian and have K-injective
   resolutions; lem-sp-grothendieck-enough-injectives gives ordinary injectives.
2. Direct image is the actual sectionwise pushforward through
   Etale.intrinsicConstantRingMap, respectively proEtaleCoefficientDirectImageMap.
   Kernels and products are sectionwise, so these
   additive functors are left exact. Their coefficient-presentation isomorphisms carry
   constant scalar sections to themselves; this gives CoefficientNormalization.
3. Apply the functors degreewise and then Qh. Additivity preserves homotopies, cones and
   shifts. Apply lem-weil-pbc-kinjective-total-derived in the sense of
   def-sfb-right-derived-functor: its recorded functor, unit, universal property and
   computation give full. For every
   resolution M -> I, resolutionIso is RF(Qs) followed by the inverse unit at I.
4. By lem-weil-pbc-dplus-injective-representative every bounded-below derived object is
   represented by a bounded-below injective complex, which is K-injective. Both full and
   bounded-below functors therefore compute Q(f_*I), using
   lem-weil-pbc-right-derived-plus-injective. This gives plusIso and plus_computes.
5. Lemma lem-weil-pbc-kinjective-hom-derived identifies all maps between injective models
   with unique homotopy classes. Thus plusIso is natural. On a bounded-below complex use
   lem-sc-bounded-below-injective-resolution-existence to compare with its injective
   resolution; naturality of both units gives exactly unit_eq.
6. The fixed-scalar and intrinsic inverse images are adjoint to the same sectionwise
   module direct image: their ring actions agree on constants, hence after sheafification.
   Use lem-pe-constant-left-module-inverse-image and
   lem-weil-pbc-module-inverse-image-unit-comparison. Adjunction bijections construct the
   unique inverse-image isomorphism carrying one unit to the other. Exactness and
   lem-pe-coefficient-comparison-derived-functor descend it termwise, giving the displayed
   realizedComparisonPlusIso and preserving D+.
7. Apply prop-weil-pbc-comparison-direct-image with u=f, Lambda=ULift B. Conjugate its
   specified rightDerivedFunctorPlusBaseChange by the coefficient identifications to get
   plus, with the explicit component equation below. Conjugate plus by the unit-normalized
   plusIso and exact inverse-image inclusion compatibility to get fullComparison. Every
   factor is a natural isomorphism. No unbounded-below etale comparison is asserted. -/
theorem ordinary_proEtale_direct_image_plus_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (B : Type u) [CommRing B] [Finite B] :
    ∃ (rE : RightDerivedNormalization (Etale.intrinsicModuleDirectImage f B))
      (rP : RightDerivedNormalization (Scheme.proEtaleConstantModuleDirectImage f B))
      (iX : ComparisonIdentification X B) (iY : ComparisonIdentification Y B)
      (k : CoefficientNormalization f B)
      (plus : (Etale.intrinsicModuleDirectImage f B).rightDerivedFunctorPlus ⋙
          (comparisonPullback Y B).mapDerivedCategoryPlus ≅
        (comparisonPullback X B).mapDerivedCategoryPlus ⋙
          (Scheme.proEtaleConstantModuleDirectImage f B).rightDerivedFunctorPlus),
      (∀ G : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))),
        plus.hom.app ((etaleRealization X B).mapDerivedCategoryPlus.obj G) =
          (comparisonPullback Y B).mapDerivedCategoryPlus.map (k.etalePlus.inv.app G) ≫
          (realizedComparisonPlusIso Y B iY).hom.app
            ((Etale.lowerStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).rightDerivedFunctorPlus.obj G) ≫
          (ProEtale.finiteCoefficientIntrinsicRealization Y B).mapDerivedCategoryPlus.map
            ((Functor.rightDerivedFunctorPlusBaseChange
              (ProEtale.lowerStarComparisonUpperStarBaseChange f
                (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))).app G) ≫
          k.proetalePlus.hom.app ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).mapDerivedCategoryPlus.obj G) ≫
          (Scheme.proEtaleConstantModuleDirectImage f B).rightDerivedFunctorPlus.map
            ((realizedComparisonPlusIso X B iX).inv.app G)) ∧
      ∃ fullComparison : DerivedCategory.Plus.ι ⋙ rE.full ⋙
            (comparisonPullback Y B).mapDerivedCategory ≅
          (comparisonPullback X B).mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙ rP.full,
        ∀ G : DerivedCategory.Plus (Etale.intrinsicConstantModules X B),
          fullComparison.hom.app G =
            (comparisonPullback Y B).mapDerivedCategory.map (rE.plusIso.hom.app G) ≫
            (comparisonPullback Y B).mapDerivedCategoryPlusCompatibility.inv.app
              ((Etale.intrinsicModuleDirectImage f B).rightDerivedFunctorPlus.obj G) ≫
            DerivedCategory.Plus.ι.map (plus.hom.app G) ≫
            rP.plusIso.inv.app ((comparisonPullback X B).mapDerivedCategoryPlus.obj G) := by
  classical
  let rE := Classical.choice (rightDerivedNormalization_exists
    (Etale.intrinsicModuleDirectImage f B) (fun K ↦ by
      obtain ⟨I, hI, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
      exact ⟨I, s, hI, hs⟩))
  let rP := Classical.choice (rightDerivedNormalization_exists
    (Scheme.proEtaleConstantModuleDirectImage f B) (fun K ↦ by
      obtain ⟨I, hI, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
      exact ⟨I, s, hI, hs⟩))
  let iX := Classical.choice (comparisonIdentification_exists X B)
  let iY := Classical.choice (comparisonIdentification_exists Y B)
  let k := Classical.choice (coefficientNormalization_exists f B)
  let E := (etaleRealization X B).mapDerivedCategoryPlus
  let F := (Etale.intrinsicModuleDirectImage f B).rightDerivedFunctorPlus
  let P := (Scheme.proEtaleConstantModuleDirectImage f B).rightDerivedFunctorPlus
  let L := (comparisonPullback X B).mapDerivedCategoryPlus
  let R := (comparisonPullback Y B).mapDerivedCategoryPlus
  let A := (Etale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).rightDerivedFunctorPlus
  let C := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).mapDerivedCategoryPlus
  let T := (ProEtale.finiteCoefficientIntrinsicRealization Y B).mapDerivedCategoryPlus
  have : (etaleEquivalence X B).functor.Additive :=
    inferInstanceAs ((etaleRealization X B).Additive)
  have : (etaleEquivalence X B).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : E.IsEquivalence := mapDerivedPlus_equivalence (etaleEquivalence X B)
  have := ProEtale.isIso_comparisonDirectImagePlus (ULift.{u + 1, u} B) f
  let b := asIso (Functor.rightDerivedFunctorPlusBaseChange
    (ProEtale.lowerStarComparisonUpperStarBaseChange f
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
  let plus : F ⋙ R ≅ L ⋙ P := transportedComparisonIso E
    (etaleRealization Y B).mapDerivedCategoryPlus
    (ProEtale.finiteCoefficientIntrinsicRealization X B).mapDerivedCategoryPlus T
    A (ProEtale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).rightDerivedFunctorPlus C
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategoryPlus
    F P L R k.etalePlus k.proetalePlus
    (realizedComparisonPlusIso X B iX) (realizedComparisonPlusIso Y B iY) b
  refine ⟨rE, rP, iX, iY, k, plus, ?_, ?_⟩
  · exact transportedComparisonIso_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · let fullComparison : DerivedCategory.Plus.ι ⋙ rE.full ⋙
          (comparisonPullback Y B).mapDerivedCategory ≅
        L ⋙ DerivedCategory.Plus.ι ⋙ rP.full :=
      (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight rE.plusIso (comparisonPullback Y B).mapDerivedCategory ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft F (comparisonPullback Y B).mapDerivedCategoryPlusCompatibility.symm ≪≫
        (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight plus DerivedCategory.Plus.ι ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft L rP.plusIso.symm
    refine ⟨fullComparison, ?_⟩
    intro G
    simp only [fullComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp]
    rfl

end AlgebraicGeometry.SfbOrdinaryComparison

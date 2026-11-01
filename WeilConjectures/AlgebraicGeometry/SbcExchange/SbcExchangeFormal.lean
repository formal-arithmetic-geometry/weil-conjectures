/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePullbackStalkCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePullbackStalkCoherence
import WeilConjectures.CategoryTheory.ExchangeFormalism.PushforwardBaseChange
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Formal laws of ordinary pro-etale exchange

Source: literature/blueprint/latest/blueprint/sec-smooth-base-change/
sk-lem-sbc-exchange-compatibility/det-sbc-exchange-formal.md, clauses (1)--(3);
Stacks Project, Tags 07A7, 0E46 and 0E47 (blueprint: det-sbc-exchange-formal).

The exchange is the published `proEtaleAmbientRingedExchange`, specialized to the
constant coefficient sheaves and their canonical constant-section identifications.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.SbcExchange

/-- The recorded ordinary unbounded direct image, specialized to constant coefficients.
Source: blueprint det-sbc-exchange-formal, opening paragraph, and Stacks Tag 07A7
(blueprint: det-sbc-exchange-formal). This abbreviation introduces no new operation. -/
abbrev directImage (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory Y A :=
  proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A)

/-- The ambient ringed exchange specialized to constant coefficients. The coefficient
identifications are the canonical constant-section comparisons, and the `HEq` witness
is their canonical equality for the commutative square. Source: blueprint
`det-sbc-exchange-formal`, opening paragraph, and Stacks Tag 07A7
(blueprint: det-sbc-exchange-formal). -/
abbrev exchange (Λ : Type u) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) :
    directImage Λ f ⋙ proEtaleConstantRingDerivedPullback Λ g ⟶
      proEtaleConstantRingDerivedPullback Λ g' ⋙ directImage Λ f' :=
  proEtaleAmbientRingedExchange sq
    (proEtaleConstantRing X Λ) (proEtaleConstantRing Y Λ)
    (proEtaleConstantRing X' Λ) (proEtaleConstantRing Y' Λ)
    (proEtaleConstantRingComparison f Λ) (proEtaleConstantRingComparison g Λ)
    (proEtaleConstantRingComparison g' Λ) (proEtaleConstantRingComparison f' Λ)
    ((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq g' f Λ)).trans
      ((congr_arg_heq (fun q : X' ⟶ Y ↦ proEtaleConstantRingComparison q Λ) sq.w).trans
        (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq f' g Λ)).symm))

/-- The specified tensor-unit-normalized derived adjunction for the constant ring.
Source: blueprint det-sbc-exchange-formal, opening paragraph, and Stacks Tag 07A7
(blueprint: det-sbc-exchange-formal). -/
abbrev adjunction (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingDerivedPullback A f ⊣ directImage A f :=
  proEtaleRingDerivedAdjunction f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A)

/-- The direct-image compositor, conjugate to the canonical pullback compositor.
The latter is fixed by the ordinary sectionwise fibre-product comparison. The derived
composition-adjunction normalization theorem identifies this conjugate with the usual
K-injective direct-image comparison, so it is not an arbitrary endpoint isomorphism.
Source: blueprint det-sbc-exchange-formal, clause (3), and Stacks Tag 0D6E
(blueprint: det-sbc-exchange-formal). -/
def directImageComposition (A : Type u) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Z) :
    directImage A (f ≫ e) ≅ directImage A f ⋙ directImage A e :=
  conjugateIsoEquiv (adjunction A (f ≫ e)) ((adjunction A e).comp (adjunction A f))
    (proEtaleConstantRingPullbackComposition f e A)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] proEtaleRingModulePullback proEtaleConstantRingComparison
  proEtaleRingModuleAdjunctionNormalized proEtaleCanonicalPullbackComposition

-- Fibre-product unit calculations, as in OverAdjunction and the generic component
-- calculations of StrictTowerDirectImageCoherence; no tower operations are imported.
private theorem restriction_eq
    {C : Type*} [Category C] {S : Cᵒᵖ ⥤ RingCat} (N : _root_.PresheafOfModules S)
    {U V : C} (a b : U ⟶ V) (h : a = b) (m : N.obj (Opposite.op V)) :
    N.map a.op m = N.map b.op m := by
  cases h
  rfl


private theorem site_right_unit
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y : C} (f : X ⟶ Y) (U : P.Over Q Y) :
    eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U)
        (Category.comp_id f).symm) ≫
      (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f (𝟙 Y)).hom.app U =
      (MorphismProperty.Over.pullback P Q f).map
        ((MorphismProperty.Over.pullbackId P Q Y).inv.app U) := by
  have h := NatTrans.congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_id_right (P := P) (Q := Q) f (f ≫ 𝟙 Y) rfl)) U
  rw [site_congr_transport] at h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app,
    eqToIso.hom, eqToHom_app] at h
  rw [h]
  simp


-- Exact-functor localization carries the two ordinary unit equations to derived ones.
private theorem identity_eq (A : Type u) [CommRing A] (X : Scheme.{u}) :
    proEtaleStalkIdentityPullback A X =
      Adjunction.leftAdjointIdIso (normalizedAdj (𝟙 X) A) (identityDirect A X) := by
  have hn := normalizedAdj_eq (𝟙 X) A (proEtaleConstantRingAdjunction A (𝟙 X))
    (moduleAdj_normalized (𝟙 X) _ _ _)
  rw [← hn]
  apply (proEtaleStalkIdentityPullback_existsUnique A X).unique
  · exact Classical.choose_spec (proEtaleStalkIdentityPullback_existsUnique A X).exists
  · intro M V a
    simp only [Adjunction.leftAdjointIdIso, conjugateIsoEquiv_symm_apply_inv,
      conjugateEquiv_symm_apply_app, Adjunction.id_counit, NatTrans.id_app,
      Iso.symm_inv]
    exact identityDirect_hom A X _ V _

private theorem direct_left_unit (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    directComp (𝟙 X) f A ≪≫
        eqToIso (congrArg (proEtaleConstantRingPushforward A) (Category.id_comp f)) =
      Functor.isoWhiskerRight (identityDirect A X) (proEtaleConstantRingPushforward A f) ≪≫
        Functor.leftUnitor (proEtaleConstantRingPushforward A f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [directImage_map_apply f A ((identityDirect A X).hom.app N) U]
  erw [identityDirect_hom A X N ((Scheme.proEtaleBaseChange f).obj U)]
  erw [directImage_transport (Category.id_comp f) A N U]
  erw [directComp_hom_apply (𝟙 X) f A N U]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  exact restriction_eq N.val _ _
    (site_left_unit
      (P := @WeaklyEtale) (Q := ⊤) f U) x

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_right_unit (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    directComp f (𝟙 Y) A ≪≫
        eqToIso (congrArg (proEtaleConstantRingPushforward A) (Category.comp_id f)) =
      Functor.isoWhiskerLeft (proEtaleConstantRingPushforward A f) (identityDirect A Y) ≪≫
        Functor.rightUnitor (proEtaleConstantRingPushforward A f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [identityDirect_hom A Y ((proEtaleConstantRingPushforward A f).obj N) U]
  erw [directImage_obj_map_apply f A N
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).inv.app U)]
  erw [directImage_transport (Category.comp_id f) A N U]
  erw [directComp_hom_apply f (𝟙 Y) A N U]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  exact restriction_eq N.val _ _
    (site_right_unit
      (P := @WeaklyEtale) (Q := ⊤) f U) x


private theorem ordinary_left_unit (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (eqToIso (congrArg (proEtaleConstantRingPullback A) (Category.id_comp f).symm)).hom.app M ≫
        (ordinaryComp (𝟙 X) f A).hom.app M ≫
        (proEtaleStalkIdentityPullback A X).hom.app ((proEtaleConstantRingPullback A f).obj M)
          = 𝟙 _ := by
  have h := Adjunction.leftAdjointCompIso_comp_id (normalizedAdj f A) (normalizedAdj (𝟙 X) A)
    (directComp (𝟙 X) f A ≪≫
      eqToIso (congrArg (proEtaleConstantRingPushforward A) (Category.id_comp f)))
    (identityDirect A X) (direct_left_unit A f)
  rw [mate_transport (proEtaleConstantRingPullback A) (proEtaleConstantRingPushforward A)
    (fun q ↦ normalizedAdj q A) (normalizedAdj f A) (normalizedAdj (𝟙 X) A)
      (Category.id_comp f) (directComp (𝟙 X) f A)] at h
  have hi := NatTrans.congr_app (congrArg Iso.inv h) M
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app] at hi
  have he : (eqToIso (congrArg (proEtaleConstantRingPullback A)
    (Category.id_comp f).symm)).hom.app M ≫
      (ordinaryComp (𝟙 X) f A).hom.app M =
      𝟙 _ ≫ (proEtaleStalkIdentityPullback A X).inv.app
        ((proEtaleConstantRingPullback A f).obj M) := by
    simpa only [ordinaryComp_eq, identity_eq, Iso.symm_hom, eqToIso.inv, eqToIso.hom,
      Functor.comp_obj, Functor.id_obj] using hi
  rw [← Category.assoc, he]
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_right_unit (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (eqToIso (congrArg (proEtaleConstantRingPullback A) (Category.comp_id f).symm)).hom.app M ≫
        (ordinaryComp f (𝟙 Y) A).hom.app M ≫
        (proEtaleConstantRingPullback A f).map ((proEtaleStalkIdentityPullback A Y).hom.app M)
          = 𝟙 _ := by
  have h := Adjunction.leftAdjointCompIso_id_comp (normalizedAdj (𝟙 Y) A) (normalizedAdj f A)
    (directComp f (𝟙 Y) A ≪≫
      eqToIso (congrArg (proEtaleConstantRingPushforward A) (Category.comp_id f)))
    (identityDirect A Y) (direct_right_unit A f)
  rw [mate_transport (proEtaleConstantRingPullback A) (proEtaleConstantRingPushforward A)
    (fun q ↦ normalizedAdj q A) (normalizedAdj (𝟙 Y) A) (normalizedAdj f A)
      (Category.comp_id f) (directComp f (𝟙 Y) A)] at h
  have hi := NatTrans.congr_app (congrArg Iso.inv h) M
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app] at hi
  have he : (eqToIso (congrArg (proEtaleConstantRingPullback A)
    (Category.comp_id f).symm)).hom.app M ≫
      (ordinaryComp f (𝟙 Y) A).hom.app M =
      𝟙 _ ≫ (proEtaleConstantRingPullback A f).map
        ((proEtaleStalkIdentityPullback A Y).inv.app M) := by
    simpa only [ordinaryComp_eq, identity_eq, Iso.symm_hom, eqToIso.inv, eqToIso.hom,
      Functor.comp_obj, Functor.id_obj] using hi
  rw [← Category.assoc, he]
  simp [← Functor.map_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem derived_left_unit (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) (Category.id_comp f).symm)).hom ≫
        ((proEtaleConstantRingPullbackComposition (𝟙 X) f A).symm).hom ≫
        Functor.whiskerLeft (proEtaleConstantRingDerivedPullback A f)
          (proEtaleStalkDerivedIdentityPullback A X).hom = 𝟙 _ := by
  have ho : eqToIso (congrArg (proEtaleConstantRingPullback A) (Category.id_comp f).symm) ≪≫
      ordinaryComp (𝟙 X) f A ≪≫
      Functor.isoWhiskerLeft (proEtaleConstantRingPullback A f)
        (proEtaleStalkIdentityPullback A X) ≪≫
      Functor.rightUnitor (proEtaleConstantRingPullback A f) = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Iso.refl_hom,
      NatTrans.id_app, Functor.comp_obj, Functor.id_obj, Category.comp_id,
      Category.assoc] using ordinary_left_unit A f M
  have hh := descend_left_unit
    (proEtaleConstantRingPullback A f) (proEtaleConstantRingPullback A (𝟙 X ≫ f))
      (proEtaleConstantRingPullback A (𝟙 X))
    (eqToIso (congrArg (proEtaleConstantRingPullback A) (Category.id_comp f).symm))
    (ordinaryComp (𝟙 X) f A) (proEtaleStalkIdentityPullback A X) ho
  rw [derived_transport (Category.id_comp f).symm A] at hh
  simpa only [constantComparison_eq, proEtaleStalkDerivedIdentityPullback, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc]
    using hh

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem derived_right_unit (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) (Category.comp_id f).symm)).hom ≫
        ((proEtaleConstantRingPullbackComposition f (𝟙 Y) A).symm).hom ≫
        Functor.whiskerRight (proEtaleStalkDerivedIdentityPullback A Y).hom
          (proEtaleConstantRingDerivedPullback A f) = 𝟙 _ := by
  have ho : eqToIso (congrArg (proEtaleConstantRingPullback A) (Category.comp_id f).symm) ≪≫
      ordinaryComp f (𝟙 Y) A ≪≫
      Functor.isoWhiskerRight (proEtaleStalkIdentityPullback A Y)
        (proEtaleConstantRingPullback A f) ≪≫
      Functor.leftUnitor (proEtaleConstantRingPullback A f) = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Iso.refl_hom,
      NatTrans.id_app, Functor.comp_obj, Functor.id_obj, Category.comp_id,
      Category.assoc] using ordinary_right_unit A f M
  have hh := descend_right_unit
    (proEtaleConstantRingPullback A f) (proEtaleConstantRingPullback A (f ≫ 𝟙 Y))
      (proEtaleConstantRingPullback A (𝟙 Y))
    (eqToIso (congrArg (proEtaleConstantRingPullback A) (Category.comp_id f).symm))
    (ordinaryComp f (𝟙 Y) A) (proEtaleStalkIdentityPullback A Y) ho
  rw [derived_transport (Category.comp_id f).symm A] at hh
  simpa only [constantComparison_eq, proEtaleStalkDerivedIdentityPullback, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc]
    using hh


-- The existing comparison proof is independent of the finite-ring hypothesis on its
-- public corollary. Reuse its normalized ordinary and localization calculations.
private theorem composition_coherence
    {X Y Z W : Scheme.{u}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (A : Type u) [CommRing A] (M : proEtaleDerivedCategory X A) :
    (proEtaleConstantRingPullbackComposition j (h ≫ k) A).inv.app M ≫
        (proEtaleConstantRingDerivedPullback A j).map
          ((proEtaleConstantRingPullbackComposition h k A).inv.app M) =
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A)
        (Category.assoc j h k).symm)).hom.app M ≫
        (proEtaleConstantRingPullbackComposition (j ≫ h) k A).inv.app M ≫
        (proEtaleConstantRingPullbackComposition j h A).inv.app
          ((proEtaleConstantRingDerivedPullback A k).obj M) := by
  let F := proEtaleConstantRingPullback A k
  let G := proEtaleConstantRingPullback A h
  let H := proEtaleConstantRingPullback A j
  let F02 := proEtaleConstantRingPullback A (h ≫ k)
  let F13 := proEtaleConstantRingPullback A (j ≫ h)
  let a02 := (ordinaryComp h k A)
  let a13 := (ordinaryComp j h A)
  let a0 := (ordinaryComp j (h ≫ k) A)
  let a1 := (ordinaryComp (j ≫ h) k A)
  let e := eqToIso (congrArg (proEtaleConstantRingPullback A)
    (Category.assoc j h k).symm)
  have ho : a0 ≪≫ Functor.isoWhiskerRight a02 H =
      e ≪≫ a1 ≪≫ Functor.isoWhiskerLeft F a13 := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    exact ordinary_coherence j h k A N
  have hh := descend_coherence F G H F02 F13
    (proEtaleConstantRingPullback A (j ≫ h ≫ k))
    (proEtaleConstantRingPullback A ((j ≫ h) ≫ k)) a02 a13 a0 a1 e ho
  have hm := NatTrans.congr_app hh M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hm
  have he := congrArg (fun t ↦ t.app M)
    (derived_transport (Category.assoc j h k).symm A)
  change (Functor.mapDerivedCategoryNatIso e).hom.app M = _ at he
  rw [he] at hm
  change ((proEtaleConstantRingPullbackComposition j (h ≫ k) A).symm).hom.app M ≫
      (proEtaleConstantRingDerivedPullback A j).map
        (((proEtaleConstantRingPullbackComposition h k A).symm).hom.app M) =
    (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A)
      (Category.assoc j h k).symm)).hom.app M ≫
      ((proEtaleConstantRingPullbackComposition (j ≫ h) k A).symm).hom.app M ≫
      ((proEtaleConstantRingPullbackComposition j h A).symm).hom.app
        ((proEtaleConstantRingDerivedPullback A k).obj M)
  simp only [constantComparison_eq, Iso.trans_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  exact hm


private theorem formalism_assoc (A : Type u) [CommRing A]
    {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : proEtaleDerivedCategory W A) :
    (proEtaleConstantRingPullbackComposition (f ≫ g) h A).inv.app M ≫
        (proEtaleConstantRingPullbackComposition f g A).inv.app
          ((proEtaleConstantRingDerivedPullback A h).obj M) =
      eqToHom (congrArg (fun q ↦ (proEtaleConstantRingDerivedPullback A q).obj M)
        (Category.assoc f g h)) ≫
        (proEtaleConstantRingPullbackComposition f (g ≫ h) A).inv.app M ≫
        (proEtaleConstantRingDerivedPullback A f).map
          ((proEtaleConstantRingPullbackComposition g h A).inv.app M) := by
  have hh := composition_coherence f g h A M
  apply (cancel_epi ((eqToIso (congrArg (proEtaleConstantRingDerivedPullback A)
    (Category.assoc f g h).symm)).hom.app M)).1
  simpa only [Category.assoc, eqToIso.hom, eqToHom_app, eqToHom_trans,
    eqToHom_refl, NatTrans.id_app, Iso.symm_hom, Category.id_comp,
    Category.comp_id] using hh.symm

private theorem formalism_left_unit (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : proEtaleDerivedCategory Y A) :
    (proEtaleConstantRingPullbackComposition (𝟙 X) f A).inv.app M ≫
        (proEtaleStalkDerivedIdentityPullback A X).hom.app
          ((proEtaleConstantRingDerivedPullback A f).obj M) =
      eqToHom (congrArg (fun q ↦ (proEtaleConstantRingDerivedPullback A q).obj M)
        (Category.id_comp f)) := by
  have hh := congr_app (derived_left_unit A f) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hh
  apply (cancel_epi ((eqToIso (congrArg (proEtaleConstantRingDerivedPullback A)
    (Category.id_comp f).symm)).hom.app M)).1
  simpa only [Category.assoc, eqToIso.hom, eqToHom_app, eqToHom_trans,
    eqToHom_refl, NatTrans.id_app, Iso.symm_hom, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, Category.comp_id] using hh

private theorem formalism_right_unit (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : proEtaleDerivedCategory Y A) :
    (proEtaleConstantRingPullbackComposition f (𝟙 Y) A).inv.app M ≫
        (proEtaleConstantRingDerivedPullback A f).map
          ((proEtaleStalkDerivedIdentityPullback A Y).hom.app M) =
      eqToHom (congrArg (fun q ↦ (proEtaleConstantRingDerivedPullback A q).obj M)
        (Category.comp_id f)) := by
  have hh := congr_app (derived_right_unit A f) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hh
  apply (cancel_epi ((eqToIso (congrArg (proEtaleConstantRingDerivedPullback A)
    (Category.comp_id f).symm)).hom.app M)).1
  simpa only [Category.assoc, eqToIso.hom, eqToHom_app, eqToHom_trans,
    eqToHom_refl, NatTrans.id_app, Iso.symm_hom, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, Category.comp_id] using hh

private def data_associativity (C : Scheme.{u} → Type w)
    [∀ X, Category.{v} (C X)]
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C Y ⥤ C X)
    (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      P g ⋙ P f ≅ P (f ≫ g)) : Prop :=
  ∀ {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : C W),
    (c (f ≫ g) h).inv.app M ≫ (c f g).inv.app ((P h).obj M) =
      eqToHom (congrArg (fun q ↦ (P q).obj M) (Category.assoc f g h)) ≫
        (c f (g ≫ h)).inv.app M ≫ (P f).map ((c g h).inv.app M)

private def data_left_unit (C : Scheme.{u} → Type w) [∀ X, Category.{v} (C X)]
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C Y ⥤ C X)
    (I : ∀ X, P (𝟙 X) ≅ 𝟭 (C X))
    (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      P g ⋙ P f ≅ P (f ≫ g)) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : C Y),
    (c (𝟙 X) f).inv.app M ≫ (I X).hom.app ((P f).obj M) =
      eqToHom (congrArg (fun q ↦ (P q).obj M) (Category.id_comp f))

private def data_right_unit (C : Scheme.{u} → Type w) [∀ X, Category.{v} (C X)]
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C Y ⥤ C X)
    (I : ∀ X, P (𝟙 X) ≅ 𝟭 (C X))
    (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      P g ⋙ P f ≅ P (f ≫ g)) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : C Y),
    (c f (𝟙 Y)).inv.app M ≫ (P f).map ((I Y).hom.app M) =
      eqToHom (congrArg (fun q ↦ (P q).obj M) (Category.comp_id f))

private noncomputable def dataFormalism (C : Scheme.{u} → Type w)
    [∀ X, Category.{v} (C X)]
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C Y ⥤ C X)
    (I : ∀ X, P (𝟙 X) ≅ 𝟭 (C X))
    (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      P g ⋙ P f ≅ P (f ≫ g))
    (R : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C X ⥤ C Y)
    (a : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f ⊣ R f)
    (hc : data_associativity C P c)
    (hl : data_left_unit C P I c) (hr : data_right_unit C P I c) :
    ExchangeFormalism Scheme.{u} ⊥ where
  obj := C
  pb := P
  pbId := I
  pbComp f g := (c f g).symm
  pbComp_assoc f g h M := by
    simpa only [Iso.symm_hom] using hc f g h M
  pbId_comp f M := by
    simpa only [Iso.symm_hom] using hl f M
  pbComp_id f M := by
    simpa only [Iso.symm_hom] using hr f M
  pf := R
  adj := a
  sh j := False.elim (show False from (‹Fact ((⊥ : MorphismProperty Scheme) j)›).out)
  shAdj j := False.elim (show False from (‹Fact ((⊥ : MorphismProperty Scheme) j)›).out)

local notation "formalismFor[" A "]" =>
  dataFormalism (fun X ↦ proEtaleDerivedCategory X A)
    (proEtaleConstantRingDerivedPullback A) (proEtaleStalkDerivedIdentityPullback A)
    (fun f g ↦ proEtaleConstantRingPullbackComposition f g A)
    (directImage A) (adjunction A)
    (formalism_assoc A) (formalism_left_unit A) (formalism_right_unit A)

-- Both choices retain the same normalization, which determines the comparison uniquely.
private theorem canonical_comparison_eq
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ) :
    proEtaleCanonicalDerivedPullbackComparison h k RV RW RZ ck ch =
      proEtaleCanonicalPullbackComposition h k RV RW RZ ck ch := by
  unfold proEtaleCanonicalDerivedPullbackComparison proEtaleCanonicalPullbackComposition
  rfl


private theorem sigma_comparison_transport
    {I C : Type*} [Category C] (D : I → Type*) (F : (Σ i, D i) → C)
    (s : ∀ i, D i) {i j : I} (w : i = j) (a : D i) (b : D j)
    (ha : a = s i) (hb : b = s j) (hab : HEq a b) :
    eqToIso (congrArg F (Sigma.ext w hab)) =
      eqToIso (congrArg (fun x ↦ F ⟨i, x⟩) ha) ≪≫
        eqToIso (congrArg (fun x ↦ F ⟨x, s x⟩) w) ≪≫
        (eqToIso (congrArg (fun x ↦ F ⟨j, x⟩) hb)).symm := by
  subst a b
  cases w
  simp

private theorem square_comparison_eq (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare u f' f g) :
    proEtaleAmbientRingedPullbackComparison sq
        (proEtaleConstantRing X A) (proEtaleConstantRing Y A)
        (proEtaleConstantRing X' A) (proEtaleConstantRing Y' A)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison g A)
        (proEtaleConstantRingComparison u A) (proEtaleConstantRingComparison f' A)
        ((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq u f A)).trans
          ((congr_arg_heq (fun q : X' ⟶ Y ↦ proEtaleConstantRingComparison q A) sq.w).trans
            (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq f' g A)).symm)) =
      ((formalismFor[A]).sqIso u f' f g sq.w).symm := by
  let D := fun q : X' ⟶ Y ↦
    (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj (proEtaleConstantRing Y A) ≅
      proEtaleConstantRing X' A
  let F := fun z : (Σ q, D q) ↦
    proEtaleRingDerivedPullback z.1 (proEtaleConstantRing Y A)
      (proEtaleConstantRing X' A) z.2
  have ht := sigma_comparison_transport D F (fun q ↦ proEtaleConstantRingComparison q A)
    sq.w.symm
    (proEtaleRingCompositeCoefficients f' g _ _ _
      (proEtaleConstantRingComparison g A) (proEtaleConstantRingComparison f' A))
    (proEtaleRingCompositeCoefficients u f _ _ _
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison u A))
    (proEtaleConstantRingCompositeCoefficients_eq f' g A)
    (proEtaleConstantRingCompositeCoefficients_eq u f A)
    (((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq u f A)).trans
      ((congr_arg_heq (fun q : X' ⟶ Y ↦ proEtaleConstantRingComparison q A) sq.w).trans
        (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq f' g A)).symm)).symm)
  unfold proEtaleAmbientRingedPullbackComparison
  dsimp only
  rw [canonical_comparison_eq, canonical_comparison_eq]
  rw [ht]
  simp only [ExchangeFormalism.sqIso, ExchangeFormalism.pbComp',
    eqToIso_refl, Iso.refl_trans]
  change _ = (proEtaleConstantRingPullbackComposition u f A ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) sq.w) ≪≫
      (proEtaleConstantRingPullbackComposition f' g A).symm).symm
  rw [proEtaleConstantRingPullbackComposition_eq, proEtaleConstantRingPullbackComposition_eq]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv]

private theorem exchange_eq (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare u f' f g) :
    exchange A sq = ((formalismFor[A]).pfBaseChange u f' f g sq.w).natTrans := by
  unfold exchange proEtaleAmbientRingedExchange
  rw [square_comparison_eq]
  rfl

private theorem direct_composition_eq (A : Type u) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Z) :
    (formalismFor[A]).pfComp' f e (f ≫ e) rfl = directImageComposition A f e := by
  simp only [ExchangeFormalism.pfComp', ExchangeFormalism.pbComp',
    eqToIso_refl, Iso.refl_trans]
  rfl

-- Do the component simplifications with an abstract formalism. In particular its
-- category instances remain syntactically identical throughout each calculation.
private theorem identity_component (F : ExchangeFormalism Scheme.{u} ⊥)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : 𝟙 X ≫ f = f ≫ 𝟙 Y) (K : F.obj X) :
    (F.pfBaseChange (𝟙 X) f f (𝟙 Y) w).natTrans.app K =
      (F.pbId Y).hom.app ((F.pf f).obj K) ≫
        (F.pf f).map ((F.pbId X).inv.app K) := by
  have hh := congrArg (fun t ↦ t.natTrans.app K) (F.pfBaseChange_id_horiz f w)
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Category.id_comp, Category.assoc] at hh
  refine hh.trans ?_
  exact congrArg (fun z ↦ (F.pbId Y).hom.app ((F.pf f).obj K) ≫ z)
    (Category.id_comp ((F.pf f).map ((F.pbId X).inv.app K)))

private theorem horizontal_component (F : ExchangeFormalism Scheme.{u} ⊥)
    {X'' X' X Y'' Y' Y : Scheme.{u}} (u : X' ⟶ X) (u' : X'' ⟶ X')
    (f : X ⟶ Y) (f' : X' ⟶ Y') (f'' : X'' ⟶ Y'')
    (g : Y' ⟶ Y) (h : Y'' ⟶ Y')
    (w₁ : u ≫ f = f' ≫ g) (w₂ : u' ≫ f' = f'' ≫ h)
    (w : (u' ≫ u) ≫ f = f'' ≫ (h ≫ g)) (K : F.obj X) :
    (F.pfBaseChange (u' ≫ u) f'' f (h ≫ g) w).natTrans.app K =
      (F.pbComp h g).hom.app ((F.pf f).obj K) ≫
        (F.pb h).map ((F.pfBaseChange u f' f g w₁).natTrans.app K) ≫
        (F.pfBaseChange u' f'' f' h w₂).natTrans.app ((F.pb u).obj K) ≫
        (F.pf f'').map ((F.pbComp u' u).inv.app K) := by
  have hh := congrArg (fun t ↦ t.natTrans.app K)
    (F.pfBaseChange_paste_horiz u' u f'' f' f h g
      (u' ≫ u) (h ≫ g) w₂ w₁ rfl rfl w)
  simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc, ExchangeFormalism.pbComp',
    eqToIso_refl, Iso.refl_trans] using hh

private theorem vertical_component (F : ExchangeFormalism Scheme.{u} ⊥)
    {X' X Y' Y Z' Z : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (v : Y' ⟶ Y) (e' : Y' ⟶ Z') (e : Y ⟶ Z) (g : Z' ⟶ Z)
    (w₁ : u ≫ f = f' ≫ v) (w₂ : v ≫ e = e' ≫ g)
    (w : u ≫ (f ≫ e) = (f' ≫ e') ≫ g) (K : F.obj X) :
    (F.pfBaseChange u (f' ≫ e') (f ≫ e) g w).natTrans.app K =
      (F.pb g).map ((F.pfComp' f e (f ≫ e) rfl).hom.app K) ≫
        (F.pfBaseChange v e' e g w₂).natTrans.app ((F.pf f).obj K) ≫
        (F.pf e').map ((F.pfBaseChange u f' f v w₁).natTrans.app K) ≫
        (F.pfComp' f' e' (f' ≫ e') rfl).inv.app ((F.pb u).obj K) := by
  have hh := congrArg (fun t ↦ t.natTrans.app K)
    (F.pfBaseChange_paste_vert u v g f' f e' e
      (f' ≫ e') (f ≫ e) w₁ w₂ rfl rfl w)
  simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] using hh

private theorem horizontal_component_of_eq (F : ExchangeFormalism Scheme.{u} ⊥)
    {X'' X' X Y'' Y' Y : Scheme.{u}} (u : X' ⟶ X) (u' : X'' ⟶ X')
    (f : X ⟶ Y) (f' : X' ⟶ Y') (f'' : X'' ⟶ Y'')
    (g : Y' ⟶ Y) (h : Y'' ⟶ Y')
    (w₁ : u ≫ f = f' ≫ g) (w₂ : u' ≫ f' = f'' ≫ h)
    (w : (u' ≫ u) ≫ f = f'' ≫ (h ≫ g))
    (a : F.pf f ⋙ F.pb (h ≫ g) ⟶ F.pb (u' ≫ u) ⋙ F.pf f'')
    (a₁ : F.pf f ⋙ F.pb g ⟶ F.pb u ⋙ F.pf f')
    (a₂ : F.pf f' ⋙ F.pb h ⟶ F.pb u' ⋙ F.pf f'')
    (ha : a = (F.pfBaseChange (u' ≫ u) f'' f (h ≫ g) w).natTrans)
    (ha₁ : a₁ = (F.pfBaseChange u f' f g w₁).natTrans)
    (ha₂ : a₂ = (F.pfBaseChange u' f'' f' h w₂).natTrans) (K : F.obj X) :
    a.app K = (F.pbComp h g).hom.app ((F.pf f).obj K) ≫
      (F.pb h).map (a₁.app K) ≫ a₂.app ((F.pb u).obj K) ≫
      (F.pf f'').map ((F.pbComp u' u).inv.app K) := by
  subst a a₁ a₂
  exact horizontal_component F u u' f f' f'' g h w₁ w₂ w K

private theorem vertical_component_of_eq (F : ExchangeFormalism Scheme.{u} ⊥)
    {X' X Y' Y Z' Z : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (v : Y' ⟶ Y) (e' : Y' ⟶ Z') (e : Y ⟶ Z) (g : Z' ⟶ Z)
    (w₁ : u ≫ f = f' ≫ v) (w₂ : v ≫ e = e' ≫ g)
    (w : u ≫ (f ≫ e) = (f' ≫ e') ≫ g)
    (a : F.pf (f ≫ e) ⋙ F.pb g ⟶ F.pb u ⋙ F.pf (f' ≫ e'))
    (a₁ : F.pf f ⋙ F.pb v ⟶ F.pb u ⋙ F.pf f')
    (a₂ : F.pf e ⋙ F.pb g ⟶ F.pb v ⋙ F.pf e')
    (d : F.pf (f ≫ e) ≅ F.pf f ⋙ F.pf e)
    (d' : F.pf (f' ≫ e') ≅ F.pf f' ⋙ F.pf e')
    (ha : a = (F.pfBaseChange u (f' ≫ e') (f ≫ e) g w).natTrans)
    (ha₁ : a₁ = (F.pfBaseChange u f' f v w₁).natTrans)
    (ha₂ : a₂ = (F.pfBaseChange v e' e g w₂).natTrans)
    (hd : (F.pfComp' f e (f ≫ e) rfl) = d)
    (hd' : (F.pfComp' f' e' (f' ≫ e') rfl) = d') (K : F.obj X) :
    a.app K = (F.pb g).map (d.hom.app K) ≫ a₂.app ((F.pf f).obj K) ≫
      (F.pf e').map (a₁.app K) ≫ d'.inv.app ((F.pb u).obj K) := by
  subst a a₁ a₂ d d'
  exact vertical_component F u f' f v e' e g w₁ w₂ w K

private theorem horizontal_from_data (C : Scheme.{u} → Type w) [∀ X, Category.{v} (C X)]
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C Y ⥤ C X)
    (I : ∀ X, P (𝟙 X) ≅ 𝟭 (C X))
    (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      P g ⋙ P f ≅ P (f ≫ g))
    (R : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C X ⥤ C Y)
    (a : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f ⊣ R f)
    (hc : data_associativity C P c)
    (hl : data_left_unit C P I c) (hr : data_right_unit C P I c)
    {X'' X' X Y'' Y' Y : Scheme.{u}} (u : X' ⟶ X) (u' : X'' ⟶ X')
    (f : X ⟶ Y) (f' : X' ⟶ Y') (f'' : X'' ⟶ Y'')
    (g : Y' ⟶ Y) (h : Y'' ⟶ Y')
    (w₁ : u ≫ f = f' ≫ g) (w₂ : u' ≫ f' = f'' ≫ h)
    (w : (u' ≫ u) ≫ f = f'' ≫ (h ≫ g))
    (t : R f ⋙ P (h ≫ g) ⟶ P (u' ≫ u) ⋙ R f'')
    (t₁ : R f ⋙ P g ⟶ P u ⋙ R f') (t₂ : R f' ⋙ P h ⟶ P u' ⋙ R f'')
    (ht : t = ((dataFormalism C P I c R a hc hl hr).pfBaseChange (u' ≫ u) f'' f (h ≫ g) w).natTrans)
    (ht₁ : t₁ = ((dataFormalism C P I c R a hc hl hr).pfBaseChange u f' f g w₁).natTrans)
    (ht₂ : t₂ = ((dataFormalism C P I c R a hc hl hr).pfBaseChange u' f'' f' h w₂).natTrans)
    (K : C X) :
    t.app K = (c h g).inv.app ((R f).obj K) ≫ (P h).map (t₁.app K) ≫
      t₂.app ((P u).obj K) ≫ (R f'').map ((c u' u).hom.app K) := by
  have hh := horizontal_component_of_eq (dataFormalism C P I c R a hc hl hr)
    u u' f f' f'' g h w₁ w₂ w t t₁ t₂ ht ht₁ ht₂ K
  simpa only [dataFormalism, Iso.symm_hom, Iso.symm_inv] using hh

private theorem vertical_from_data (C : Scheme.{u} → Type w) [∀ X, Category.{v} (C X)]
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C Y ⥤ C X)
    (I : ∀ X, P (𝟙 X) ≅ 𝟭 (C X))
    (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      P g ⋙ P f ≅ P (f ≫ g))
    (R : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C X ⥤ C Y)
    (a : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f ⊣ R f)
    (hc : data_associativity C P c)
    (hl : data_left_unit C P I c) (hr : data_right_unit C P I c)
    {X' X Y' Y Z' Z : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (v : Y' ⟶ Y) (e' : Y' ⟶ Z') (e : Y ⟶ Z) (g : Z' ⟶ Z)
    (w₁ : u ≫ f = f' ≫ v) (w₂ : v ≫ e = e' ≫ g)
    (w : u ≫ (f ≫ e) = (f' ≫ e') ≫ g)
    (t : R (f ≫ e) ⋙ P g ⟶ P u ⋙ R (f' ≫ e'))
    (t₁ : R f ⋙ P v ⟶ P u ⋙ R f') (t₂ : R e ⋙ P g ⟶ P v ⋙ R e')
    (d : R (f ≫ e) ≅ R f ⋙ R e) (d' : R (f' ≫ e') ≅ R f' ⋙ R e')
    (ht : t = ((dataFormalism C P I c R a hc hl hr).pfBaseChange u (f' ≫ e') (f ≫ e) g w).natTrans)
    (ht₁ : t₁ = ((dataFormalism C P I c R a hc hl hr).pfBaseChange u f' f v w₁).natTrans)
    (ht₂ : t₂ = ((dataFormalism C P I c R a hc hl hr).pfBaseChange v e' e g w₂).natTrans)
    (hd : (dataFormalism C P I c R a hc hl hr).pfComp' f e (f ≫ e) rfl = d)
    (hd' : (dataFormalism C P I c R a hc hl hr).pfComp' f' e' (f' ≫ e') rfl = d')
    (K : C X) :
    t.app K = (P g).map (d.hom.app K) ≫ t₂.app ((R f).obj K) ≫
      (R e').map (t₁.app K) ≫ d'.inv.app ((P u).obj K) := by
  exact vertical_component_of_eq (dataFormalism C P I c R a hc hl hr) u f' f v e' e g
    w₁ w₂ w t t₁ t₂ d d' ht ht₁ ht₂ hd hd' K

-- Cache the data specialization independently of the square and its transformations.
private theorem horizontal_specialized (A : Type u) [CommRing A] :
    ∀ {X'' X' X Y'' Y' Y : Scheme.{u}} (u : X' ⟶ X) (u' : X'' ⟶ X')
    (f : X ⟶ Y) (f' : X' ⟶ Y') (f'' : X'' ⟶ Y'')
    (g : Y' ⟶ Y) (h : Y'' ⟶ Y')
    (w₁ : u ≫ f = f' ≫ g) (w₂ : u' ≫ f' = f'' ≫ h)
    (w : (u' ≫ u) ≫ f = f'' ≫ (h ≫ g))
    (t : (directImage A) f ⋙ (proEtaleConstantRingDerivedPullback A) (h ≫ g) ⟶
      (proEtaleConstantRingDerivedPullback A) (u' ≫ u) ⋙ (directImage A) f'')
    (t₁ : (directImage A) f ⋙ (proEtaleConstantRingDerivedPullback A) g ⟶
      (proEtaleConstantRingDerivedPullback A) u ⋙ (directImage A) f')
    (t₂ : (directImage A) f' ⋙ (proEtaleConstantRingDerivedPullback A) h ⟶
      (proEtaleConstantRingDerivedPullback A) u' ⋙ (directImage A) f'')
    (_ht : t = ((formalismFor[A]).pfBaseChange (u' ≫ u) f'' f (h ≫ g) w).natTrans)
    (_ht₁ : t₁ = ((formalismFor[A]).pfBaseChange u f' f g w₁).natTrans)
    (_ht₂ : t₂ = ((formalismFor[A]).pfBaseChange u' f'' f' h w₂).natTrans)
    (K : proEtaleDerivedCategory X A),
    t.app K = (proEtaleConstantRingPullbackComposition h g A).inv.app (((directImage A) f).obj K) ≫
      ((proEtaleConstantRingDerivedPullback A) h).map (t₁.app K) ≫
      t₂.app (((proEtaleConstantRingDerivedPullback A) u).obj K) ≫
      ((directImage A) f'').map ((proEtaleConstantRingPullbackComposition u' u A).hom.app K) := by
  exact horizontal_from_data (fun X ↦ proEtaleDerivedCategory X A)
    (proEtaleConstantRingDerivedPullback A) (proEtaleStalkDerivedIdentityPullback A)
    (fun f g ↦ proEtaleConstantRingPullbackComposition f g A)
    (directImage A) (adjunction A)
    (formalism_assoc A) (formalism_left_unit A) (formalism_right_unit A)

private theorem vertical_specialized (A : Type u) [CommRing A] :
    ∀ {X' X Y' Y Z' Z : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (v : Y' ⟶ Y) (e' : Y' ⟶ Z') (e : Y ⟶ Z) (g : Z' ⟶ Z)
    (w₁ : u ≫ f = f' ≫ v) (w₂ : v ≫ e = e' ≫ g)
    (w : u ≫ (f ≫ e) = (f' ≫ e') ≫ g)
    (t : (directImage A) (f ≫ e) ⋙ (proEtaleConstantRingDerivedPullback A) g ⟶
      (proEtaleConstantRingDerivedPullback A) u ⋙ (directImage A) (f' ≫ e'))
    (t₁ : (directImage A) f ⋙ (proEtaleConstantRingDerivedPullback A) v ⟶
      (proEtaleConstantRingDerivedPullback A) u ⋙ (directImage A) f')
    (t₂ : (directImage A) e ⋙ (proEtaleConstantRingDerivedPullback A) g ⟶
      (proEtaleConstantRingDerivedPullback A) v ⋙ (directImage A) e')
    (d : (directImage A) (f ≫ e) ≅ (directImage A) f ⋙ (directImage A) e)
    (d' : (directImage A) (f' ≫ e') ≅ (directImage A) f' ⋙ (directImage A) e')
    (_ht : t = ((formalismFor[A]).pfBaseChange u (f' ≫ e') (f ≫ e) g w).natTrans)
    (_ht₁ : t₁ = ((formalismFor[A]).pfBaseChange u f' f v w₁).natTrans)
    (_ht₂ : t₂ = ((formalismFor[A]).pfBaseChange v e' e g w₂).natTrans)
    (_hd : (formalismFor[A]).pfComp' f e (f ≫ e) rfl = d)
    (_hd' : (formalismFor[A]).pfComp' f' e' (f' ≫ e') rfl = d')
    (K : proEtaleDerivedCategory X A),
    t.app K = ((proEtaleConstantRingDerivedPullback A) g).map (d.hom.app K) ≫
      t₂.app (((directImage A) f).obj K) ≫
      ((directImage A) e').map (t₁.app K) ≫
      d'.inv.app (((proEtaleConstantRingDerivedPullback A) u).obj K) := by
  exact vertical_from_data (fun X ↦ proEtaleDerivedCategory X A)
    (proEtaleConstantRingDerivedPullback A) (proEtaleStalkDerivedIdentityPullback A)
    (fun f g ↦ proEtaleConstantRingPullbackComposition f g A)
    (directImage A) (adjunction A)
    (formalism_assoc A) (formalism_left_unit A) (formalism_right_unit A)


attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem formal_naturality (A : Type u) [CommRing A] :
    (∀ {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
        {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare u f' f g)
        {K L : proEtaleDerivedCategory X A} (v : K ⟶ L),
      (proEtaleConstantRingDerivedPullback A g).map ((directImage A f).map v) ≫
          (exchange A sq).app L =
        (exchange A sq).app K ≫
          (directImage A f').map ((proEtaleConstantRingDerivedPullback A u).map v)) := by
  intros
  exact (exchange A _).naturality _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem formal_identity (A : Type u) [CommRing A] :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
        (sq : ChosenCartesianSquare (𝟙 X) f f (𝟙 Y))
        (K : proEtaleDerivedCategory X A),
      (exchange A sq).app K =
        (proEtaleStalkDerivedIdentityPullback A Y).hom.app ((directImage A f).obj K) ≫
          (directImage A f).map ((proEtaleStalkDerivedIdentityPullback A X).inv.app K)) := by
  intro X Y f sq K
  rw [exchange_eq]
  exact identity_component (formalismFor[A]) f sq.w K

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem formal_horizontal (A : Type u) [CommRing A] :
    (∀ {X'' X' X Y'' Y' Y : Scheme.{u}} {u : X' ⟶ X} {u' : X'' ⟶ X'}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
        {g : Y' ⟶ Y} {h : Y'' ⟶ Y'}
        (sq₁ : ChosenCartesianSquare u f' f g)
        (sq₂ : ChosenCartesianSquare u' f'' f' h)
        (outer : ChosenCartesianSquare (u' ≫ u) f'' f (h ≫ g))
        (K : proEtaleDerivedCategory X A),
      (exchange A outer).app K =
        (proEtaleConstantRingPullbackComposition h g A).inv.app ((directImage A f).obj K) ≫
          (proEtaleConstantRingDerivedPullback A h).map
            ((exchange A sq₁).app K) ≫
          (exchange A sq₂).app
            ((proEtaleConstantRingDerivedPullback A u).obj K) ≫
          (directImage A f'').map
            ((proEtaleConstantRingPullbackComposition u' u A).hom.app K)) := by
  intro X'' X' X Y'' Y' Y u u' f f' f'' g h sq₁ sq₂ outer K
  exact horizontal_specialized A
    u u' f f' f'' g h
    sq₁.w sq₂.w outer.w (exchange A outer) (exchange A sq₁) (exchange A sq₂)
    (exchange_eq A outer) (exchange_eq A sq₁) (exchange_eq A sq₂) K

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem formal_vertical (A : Type u) [CommRing A] :
    (∀ {X' X Y' Y Z' Z : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
        {f : X ⟶ Y} {v : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {g : Z' ⟶ Z}
        (sq₁ : ChosenCartesianSquare u f' f v)
        (sq₂ : ChosenCartesianSquare v e' e g)
        (outer : ChosenCartesianSquare u (f' ≫ e') (f ≫ e) g)
        (K : proEtaleDerivedCategory X A),
      (exchange A outer).app K =
        (proEtaleConstantRingDerivedPullback A g).map
            ((directImageComposition A f e).hom.app K) ≫
          (exchange A sq₂).app ((directImage A f).obj K) ≫
          (directImage A e').map ((exchange A sq₁).app K) ≫
          (directImageComposition A f' e').inv.app
            ((proEtaleConstantRingDerivedPullback A u).obj K)) := by
  intro X' X Y' Y Z' Z u f' f v e' e g sq₁ sq₂ outer K
  exact vertical_specialized A
    u f' f v e' e g sq₁.w sq₂.w outer.w
    (exchange A outer) (exchange A sq₁) (exchange A sq₂)
    (directImageComposition A f e) (directImageComposition A f' e')
    (exchange_eq A outer) (exchange_eq A sq₁) (exchange_eq A sq₂)
    (direct_composition_eq A f e) (direct_composition_eq A f' e') K

/-- Naturality, identity, and horizontal and vertical pasting of the specified exchange.
Source: blueprint det-sbc-exchange-formal, clauses (1)--(3), and Stacks Tags
07A7, 0E46, 0E47 (blueprint: det-sbc-exchange-formal).

Proof, following the seven steps of the node:
1. The ordinary direct-image comparisons restrict along the canonical flattening of
   iterated fibre products. Both scalar actions restrict the same section. The fibre-product
   universal property proves associativity and identity. Conjugation by the specified
   adjunctions gives the normalized ordinary inverse-image comparisons
   (def-pc-fibre-product, def-weil-pbc-adjunction-conjugate,
   def-weil-pbc-composite-adjunction, lem-weil-pbc-mate-pasting).
2. Exact pullback descends these maps termwise to the unbounded derived categories.
   Localization uniqueness transports associativity and identity. Expand each square
   comparison as a compositor, transport by commutativity, and inverse compositor;
   cancel adjacent inverse pairs to obtain both square-pasting equations
   (lem-weil-pbc-localization-universal-property).
3. Module sheaves on the small ringed site are Grothendieck abelian. Apply the derived
   composition-adjunction normalization to the ordinary pullback compositor. Its conjugate
   is the sectionwise direct-image comparison; therefore directImageComposition is the
   canonical derived direct-image comparison, on all unbounded inputs
   (lem-pur-ringed-site-grothendieck-abelian,
   lem-sfb-derived-composition-adjunction-normalization).
4. The ambient ringed exchange is precisely the mate of that square comparison.
   Its counit characterization is the transpose in the opening paragraph. Each of unit,
   comparison and counit is natural in K (def-weil-pbc-adjunction-mate).
5. The identity square comparison becomes the identity after the normalized identity
   pullbacks. The mate of the identity is the identity by the triangle identities;
   whiskering restores the two identity comparisons in the displayed equation
   (lem-weil-pbc-mate-pasting, lem-weil-pbc-mate-whisker).
6. For two base changes, mate pasting and the horizontal square-pasting equation of step 2
   give the two exchange factors. Whiskering moves the two inverse-image compositors to
   the ends, with inverse at the source and forward comparison at the target
   (lem-weil-pbc-mate-pasting, lem-weil-pbc-mate-whisker).
7. For two vertical maps, use the composite adjunction and its composite counit. Vertical
   mate pasting gives exchange for e at Rf_*K followed by Re'_* of exchange for f.
   Conjugation changes the composite adjunctions to the recorded ones, introducing the
   direct-image compositor at the source and its inverse at the target
   (lem-weil-pbc-mate-pasting).
-/
theorem formal (A : Type u) [CommRing A] :
    (∀ {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
        {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare u f' f g)
        {K L : proEtaleDerivedCategory X A} (v : K ⟶ L),
      (proEtaleConstantRingDerivedPullback A g).map ((directImage A f).map v) ≫
          (exchange A sq).app L =
        (exchange A sq).app K ≫
          (directImage A f').map ((proEtaleConstantRingDerivedPullback A u).map v)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
        (sq : ChosenCartesianSquare (𝟙 X) f f (𝟙 Y))
        (K : proEtaleDerivedCategory X A),
      (exchange A sq).app K =
        (proEtaleStalkDerivedIdentityPullback A Y).hom.app ((directImage A f).obj K) ≫
          (directImage A f).map ((proEtaleStalkDerivedIdentityPullback A X).inv.app K)) ∧
    (∀ {X'' X' X Y'' Y' Y : Scheme.{u}} {u : X' ⟶ X} {u' : X'' ⟶ X'}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
        {g : Y' ⟶ Y} {h : Y'' ⟶ Y'}
        (sq₁ : ChosenCartesianSquare u f' f g)
        (sq₂ : ChosenCartesianSquare u' f'' f' h)
        (outer : ChosenCartesianSquare (u' ≫ u) f'' f (h ≫ g))
        (K : proEtaleDerivedCategory X A),
      (exchange A outer).app K =
        (proEtaleConstantRingPullbackComposition h g A).inv.app ((directImage A f).obj K) ≫
          (proEtaleConstantRingDerivedPullback A h).map
            ((exchange A sq₁).app K) ≫
          (exchange A sq₂).app
            ((proEtaleConstantRingDerivedPullback A u).obj K) ≫
          (directImage A f'').map ((proEtaleConstantRingPullbackComposition u' u A).hom.app K)) ∧
    (∀ {X' X Y' Y Z' Z : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
        {f : X ⟶ Y} {v : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {g : Z' ⟶ Z}
        (sq₁ : ChosenCartesianSquare u f' f v)
        (sq₂ : ChosenCartesianSquare v e' e g)
        (outer : ChosenCartesianSquare u (f' ≫ e') (f ≫ e) g)
        (K : proEtaleDerivedCategory X A),
      (exchange A outer).app K =
        (proEtaleConstantRingDerivedPullback A g).map
            ((directImageComposition A f e).hom.app K) ≫
          (exchange A sq₂).app ((directImage A f).obj K) ≫
          (directImage A e').map ((exchange A sq₁).app K) ≫
          (directImageComposition A f' e').inv.app
            ((proEtaleConstantRingDerivedPullback A u).obj K)) := by
  exact ⟨formal_naturality A, formal_identity A, formal_horizontal A, formal_vertical A⟩

end AlgebraicGeometry.Scheme.SbcExchange

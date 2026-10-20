/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison

/-! # Proper coincidence with the identity-open normalization

Source: Stacks Project, more-etale.tex, proper compactification and Tag 0F7L;
blueprint cor-cbc-proper-coincidence
(blueprint: cor-cbc-proper-coincidence).
The identifications are constructed from the identity-open adjunction, rather than
selected from the recorded Nonempty isomorphism.

## Main definitions

* `Etale.properCoincidenceIdentityOpenPlus`, `ProEtale.properCoincidenceIdentityOpenPlus`:
  the specified identity-open identifications.
* `Etale.properCoincidenceCandidatePlus`, `Etale.properCoincidenceBaseChangedPlus`:
  their canonical candidate and base-change transports.

## Main statement

* `Etale.properCoincidence_exchange`: equality with the proper-base-change exchange.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Identity-open normalization of ordinary etale compact support for a proper map.
Source: Stacks, the proper compactification convention, Tag 0F7L
(blueprint: cor-cbc-proper-coincidence). -/
def Etale.properCoincidenceIdentityOpenPlus (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper f) ≅
      (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryPlusNatIso
          (Adjunction.leftAdjointIdIso
            (Etale.openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) (𝟙 X))
            (Etale.upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
        Functor.mapDerivedCategoryPlusIdIso _) _ ≪≫
    Functor.leftUnitor _

/-- The same identity-open normalization for pro-etale constant-module sheaves.
Source: blueprint proper coincidence, identity-open compactification
(blueprint: cor-cbc-proper-coincidence). -/
def ProEtale.properCoincidenceIdentityOpenPlus (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    ProEtale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper f) ≅
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryPlusNatIso
          (Adjunction.leftAdjointIdIso
            (ProEtale.openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) (𝟙 X))
            (ProEtale.upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
        Functor.mapDerivedCategoryPlusIdIso _) _ ≪≫
    Functor.leftUnitor _

/-- Canonical proper coincidence for any ordinary etale candidate, compared to the
identity-open model by the recorded compactification comparison.
Source: Stacks 0F7I and proper compactification convention
(blueprint: cor-cbc-proper-coincidence). -/
def Etale.properCoincidenceCandidatePlus (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (c : Compactification f) :=
  Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c
      (Compactification.ofIsProper f) ≪≫
    Etale.properCoincidenceIdentityOpenPlus A f

/-- The canonical proper identification of the base-changed identity-open model.
Properness of the base-changed morphism follows from the supplied cartesian square.
Source: Stacks 0F7L, base change of a proper compactification
(blueprint: cor-cbc-proper-coincidence). -/
def Etale.properCoincidenceBaseChangedPlus (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsProper f] (sq : IsPullback g' f' f g) :=
  letI : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
  Etale.properCoincidenceCandidatePlus A f' ((Compactification.ofIsProper f).ofIsPullback sq)

private lemma derivedToId_fac {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (F : C ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : F ≅ 𝟭 C)
    (K : HomotopyCategory.Plus C) :
    (Functor.mapDerivedCategoryPlusNatIso e ≪≫
      Functor.mapDerivedCategoryPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K) =
    F.mapDerivedCategoryPlusFactorsh.hom.app K ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) := by
  simpa only [Iso.trans_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh] using
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh e K

set_option backward.isDefEq.respectTransparency false in
private lemma derivedLeftAdjointId {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [IsGrothendieckAbelian C] [Abelian.HasKInjectiveResolutions C]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {F G : C ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (e : G ≅ 𝟭 C) :
    Functor.mapDerivedCategoryPlusNatIso (adj.leftAdjointIdIso e) ≪≫
      Functor.mapDerivedCategoryPlusIdIso C =
    adj.mapDerivedCategoryPlusAdjunction.leftAdjointIdIso
      (Functor.mapDerivedCategoryPlusNatIso e ≪≫ Functor.mapDerivedCategoryPlusIdIso C) := by
  let a := adj.leftAdjointIdIso e
  let aD := Functor.mapDerivedCategoryPlusNatIso a ≪≫
    Functor.mapDerivedCategoryPlusIdIso C
  let eD := Functor.mapDerivedCategoryPlusNatIso e ≪≫
    Functor.mapDerivedCategoryPlusIdIso C
  have hu : adj.mapDerivedCategoryPlusAdjunction.unit ≫
      Functor.whiskerRight aD.hom G.mapDerivedCategoryPlus = eD.inv := by
    apply (cancel_mono eD.hom).mp
    simp only [Iso.inv_hom_id]
    refine Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C) (fun K ↦ ?_)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app]
    rw [show aD.hom.app (DerivedCategory.Plus.Qh.obj K) = _ from derivedToId_fac F a K,
      show eD.hom.app (DerivedCategory.Plus.Qh.obj K) = _ from derivedToId_fac G e K,
      Functor.map_comp, Category.assoc, Category.assoc]
    erw [G.mapDerivedCategoryPlusFactorsh.hom.naturality_assoc]
    simp only [Functor.comp_map]
    erw [reassoc_of% adj.mapDerivedCategoryPlusAdjunction_unit_app_fac]
    erw [← Functor.map_comp, ← Functor.map_comp]
    have h : adj.mapHomotopyCategoryPlus.unit.app K ≫
        G.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus a.hom).app K) =
        (NatTrans.mapHomotopyCategoryPlus e.inv).app K :=
      adj.mapHomotopyCategoryPlus_unit_app_comp_id a e (fun M ↦ by
        simpa [a] using (unit_conjugateEquiv Adjunction.id adj
          (adj.leftAdjointIdIso e).hom M).symm) K
    erw [← Category.assoc, h, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategoryPlus_comp,
      e.inv_hom_id, NatTrans.mapHomotopyCategoryPlus_id]
    erw [NatTrans.id_app]
    exact CategoryTheory.Functor.map_id DerivedCategory.Plus.Qh _
  change aD = adj.mapDerivedCategoryPlusAdjunction.leftAdjointIdIso eD
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id adj.mapDerivedCategoryPlusAdjunction).injective
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom]
  apply conjugateEquiv_eq_of_unit
  intro M
  simpa using (NatTrans.congr_app hu M).symm

set_option backward.isDefEq.respectTransparency false in
private lemma properIdentityExchange
    (F : CompactSupportFormalism) [F.HasBaseChange]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsProper f] [IsProper f']
    (sq : IsPullback g' f' f g) :
    Functor.whiskerRight
        (Functor.isoWhiskerRight (F.shId X) (F.pf f) ≪≫ Functor.leftUnitor _).hom
        (F.pb g) ≫ (F.pfBaseChange g' f' f g sq.w).natTrans =
      (F.shriekBaseChange (Compactification.ofIsProper f)
          (Compactification.ofIsProper f') g' (.of_id_snd) sq).natTrans ≫
        Functor.whiskerLeft (F.pb g')
          (Functor.isoWhiskerRight (F.shId X') (F.pf f') ≪≫ Functor.leftUnitor _).hom := by
  have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F)
    (IsPullback.of_id_snd (f := g'))
  have hinv (K : F.obj X) :
      inv ((F.baseChange g' (𝟙 X') (𝟙 X) g' (by simp)).natTrans.app K) =
        (F.pb g').map ((F.shId X).hom.app K) ≫
          (F.shId X').inv.app ((F.pb g').obj K) := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [F.baseChange_id_vert g']
    simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.mk,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Functor.id_obj,
      Category.id_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp]
    erw [Category.id_comp]
    exact (F.shId X').hom_inv_id_app ((F.pb g').obj K)
  ext K
  dsimp only [Compactification.ofIsProper, CompactSupportFormalism.shriek]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.isoWhiskerRight_hom, Functor.leftUnitor_hom_app, Category.comp_id,
    Functor.whiskerLeft_app, CompactSupportFormalism.shriekBaseChange, TwoSquare.hComp,
    TwoSquare.mk, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Functor.comp_obj]
  simp only [Category.assoc, NatIso.isIso_inv_app]
  rw [hinv]
  erw [Category.comp_id, Category.comp_id]
  change (F.pb g).map ((F.pf f).map ((F.shId X).hom.app K)) ≫
      (F.pfBaseChange g' f' f g sq.w).natTrans.app K =
    (F.pfBaseChange g' f' f g sq.w).natTrans.app ((F.sh (𝟙 X)).obj K) ≫
      (F.pf f').map ((F.pb g').map ((F.shId X).hom.app K) ≫
        (F.shId X').inv.app ((F.pb g').obj K)) ≫
      (F.pf f').map ((F.shId X').hom.app ((F.pb g').obj K))
  rw [← (F.pf f').map_comp, Category.assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.id_obj]
  erw [Category.comp_id]
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] using
    ((F.pfBaseChange g' f' f g sq.w).natTrans.naturality ((F.shId X).hom.app K))

private lemma properBaseChangedComparison
    (F : CompactSupportFormalism) [F.HasProperExchange]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsProper f] [IsProper f']
    (sq : IsPullback g' f' f g) :
    (F.shriekBaseChange (Compactification.ofIsProper f)
        (Compactification.ofIsProper f') g' (.of_id_snd) sq).natTrans =
      (F.shriekBaseChangeOfIsPullback sq (Compactification.ofIsProper f)).natTrans ≫
        Functor.whiskerLeft (F.pb g')
          (F.shriekIso ((Compactification.ofIsProper f).ofIsPullback sq)
            (Compactification.ofIsProper f')).hom := by
  let c := Compactification.ofIsProper f
  let d := Compactification.ofIsProper f'
  let b := c.ofIsPullback sq
  let r : d.Refinement b :=
    { hom := b.i
      i_hom := Category.id_comp _
      hom_g := b.comm.symm }
  have hr : IsPullback d.i (𝟙 X') r.hom b.i :=
    IsPullback.of_vert_isIso_mono ⟨by simp [r, d, Compactification.ofIsProper]⟩
  have hid : IsPullback d.i (𝟙 X') (Compactification.Refinement.id d).hom d.i :=
    by
      change IsPullback d.i (𝟙 X') (𝟙 _) d.i
      exact IsPullback.of_vert_isIso ⟨by simp⟩
  have he : (F.shriekIso b d).hom = F.refinementComparison r hr := by
    rw [F.shriekIso_eq r (Compactification.Refinement.id d) hr hid]
    simp [F.refinementComparison_eq_id _ hid rfl]
  have hc : IsPullback c.i (𝟙 X) (Compactification.Refinement.id c).hom c.i :=
    by
      change IsPullback c.i (𝟙 X) (𝟙 _) c.i
      exact IsPullback.of_vert_isIso ⟨by simp⟩
  have h := F.shriekBaseChange_refinementComparison (Compactification.Refinement.id c) hc
    r hr g' (.of_id_snd) sq (pullback.fst c.g g)
    (c.isPullback_i_ofIsPullback sq) (c.isPullback_g_ofIsPullback sq).flip
    (by simp [r, b, c, Compactification.ofIsProper])
  rw [← he, F.refinementComparison_eq_id _ hc rfl] at h
  simpa only [Functor.whiskerRight_id', Category.id_comp] using h

/-- Under the identity-open identifications, the specified compact-support exchange
is the ordinary proper-base-change exchange. Consequently it is invertible.
Source: Stacks 0F7L and blueprint cor-cbc-proper-coincidence
(blueprint: cor-cbc-proper-coincidence).

Proof: use the identity-open compactification of f. Its candidate is Rf_* after the
identity-open adjunction isomorphism displayed above. Base change gives the proper
identity-open model on X', canonically compared with its displayed pullback model.
In the definition of Ex_!, the first factor is the proper unit--square--counit
exchange applied after identity extension. The second factor is the identity-open
extension base-change isomorphism. Its unit normalization cancels the identity
extension identifications. The remaining map is precisely the derived proper
exchange, with no automorphism ambiguity. The finite-torsion compact-support theorem
applies to this model, so the equal map is invertible. Equivalently apply ordinary
proper base change with the same finite ring. These constructions also cover the
empty scheme, identity base change and zero coefficient ring. -/
theorem Etale.properCoincidence_exchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsProper f] (sq : IsPullback g' f' f g) :
    (Functor.whiskerRight (Etale.properCoincidenceIdentityOpenPlus A f).hom
        (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus ≫
      Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq.toCommSq =
    Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq
        (Compactification.ofIsProper f) ≫
      Functor.whiskerLeft (Etale.upperStar (ModuleCat.{u + 1} A) g').mapDerivedCategoryPlus
        (Etale.properCoincidenceBaseChangedPlus A sq).hom) ∧
      IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq.toCommSq) := by
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
  let F := Etale.derivedPlusFormalism (ModuleCat.{u + 1} A)
  have hid (Z : Scheme.{u}) :
      Functor.mapDerivedCategoryPlusNatIso
          (Adjunction.leftAdjointIdIso
            (Etale.openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) (𝟙 Z))
            (Etale.upperStarId (ModuleCat.{u + 1} A) Z)) ≪≫
        Functor.mapDerivedCategoryPlusIdIso _ = F.shId Z := by
    exact derivedLeftAdjointId
      (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 Z))
      (Etale.upperStarId (ModuleCat.{u + 1} A) Z)
  constructor
  · have h := properIdentityExchange (Etale.derivedPlusFormalism (ModuleCat.{u + 1} A)) sq
    rw [properBaseChangedComparison (Etale.derivedPlusFormalism (ModuleCat.{u + 1} A)) sq] at h
    simp only [Etale.derivedPlusFormalism_pfBaseChange,
      Etale.derivedPlusFormalism_shriekIso] at h
    simpa only [Etale.properCoincidenceIdentityOpenPlus,
      Etale.properCoincidenceBaseChangedPlus, Etale.properCoincidenceCandidatePlus,
      hid, Iso.trans_hom, Functor.whiskerLeft_comp, Category.assoc,
      F, Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap,
      Etale.derivedPlusFormalism, Compactification.ofIsProper, TwoSquare.natTrans] using h
  · rw [← Etale.baseChange_eq_derivedBaseChangeMapPlus]
    exact Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring A
      isAddTorsion_of_finite sq

end AlgebraicGeometry

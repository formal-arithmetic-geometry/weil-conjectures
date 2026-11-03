/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Arbitrary-base-change coherence of the compact-support compositor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local instance] unbounded_has_base_change unbounded_has_proper_exchange

-- The public normalization theorem has extra geometric hypotheses; its formal proof does not.
private theorem relativeKunneth_exchange_normalization_general
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    (sq : IsPullback v' f' f v) (c : Compactification f) :
    unboundedEtaleCompactSupportExchange A sq c =
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g v).toCommSq) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A)
          (c.isPullback_i_ofIsPullback sq)).inv
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) (c.ofIsPullback sq).g) ≫
      (Functor.associator _ _ _).hom := by
  ext K
  have h := congrArg (fun η ↦ η.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K))
    (exact_exchange_transport A (IsPullback.of_hasPullback c.g v).toCommSq)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  simp only [unboundedEtaleCompactSupportExchange,
    rightDerivedLowerShriekOfCompactificationBaseChangeMap,
    derivedOpenImmersionLowerShriekBaseChangeIso, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  dsimp only [rightDerivedLowerShriekOfCompactification, rightDerivedLowerStar,
    Functor.comp_obj, Functor.comp_map] at h ⊢
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.map_comp]
  rw [← h]
  simp only [Category.assoc]
  rw [((openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (c.ofIsPullback sq).i).mapDerivedCategory).map_id]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.comp_id]
  rfl

private lemma relativeKunneth_shriek_base_change_general
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    (sq : IsPullback v' f' f v)
    (c : Compactification f) :
    ((unboundedFormalism A).shriekBaseChangeOfIsPullback sq c).natTrans =
      unboundedEtaleCompactSupportExchange A sq c := by
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange
    (F := unboundedFormalism A) (c.isPullback_i_ofIsPullback sq)
  have hh : inv ((unboundedFormalism A).baseChange v' (c.ofIsPullback sq).i c.i
      (pullback.fst c.g v) (c.isPullback_i_ofIsPullback sq).w).natTrans =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [unbounded_open_base_change]
    exact Iso.hom_inv_id _
  rw [relativeKunneth_exchange_normalization_general]
  dsimp only [CompactSupportFormalism.shriekBaseChangeOfIsPullback,
    CompactSupportFormalism.shriekBaseChange, ExchangeFormalism.shriekBaseChange,
    TwoSquare.hComp, TwoSquare.natTrans, TwoSquare.mk]
  rw [unbounded_pf_base_change, hh]
  rfl

private lemma relativeKunneth_chosen_base_change_general
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback v' f' f v) :
    ((unboundedFormalism A).lowerShriekBaseChange sq).natTrans =
      unboundedEtaleCompactSupportBaseChange A sq := by
  let B := ModuleCat.{u + 1} A
  let c := HasCompactification.compactification f
  dsimp only [CompactSupportFormalism.lowerShriekBaseChange, TwoSquare.whiskerBottom]
  rw [relativeKunneth_shriek_base_change_general, unbounded_shriek_iso]
  rw [unboundedEtaleCompactSupportExchange, unboundedEtaleCompactSupportBaseChange,
    rightDerivedLowerShriekBaseChangeMap]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  apply congrArg (fun t ↦ _ ≫ _ ≫ t)
  exact (rightDerivedLowerShriekIso A (c.ofIsPullback sq)).hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory B v').hom.app K)


private theorem relativeKunneth_exact_comp_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' Z Z' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    {vX : X' ⟶ X} {vY : Y' ⟶ Y} {vZ : Z' ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f' ≫ g')]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    (sqf : IsPullback vX f' f vY) (sqg : IsPullback vY g' g vZ)
    (sqgf : IsPullback vX (f' ≫ g') (f ≫ g) vZ) :
    Functor.whiskerRight (unboundedEtaleLowerShriekCompIso A f g).hom
        (upperStar (ModuleCat.{u + 1} A) vZ).mapDerivedCategory ≫
      unboundedEtaleCompactSupportBaseChange A sqgf =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (unboundedEtaleCompactSupportBaseChange A sqg) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleCompactSupportBaseChange A sqf)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g') ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) vX).mapDerivedCategory
        (unboundedEtaleLowerShriekCompIso A f' g').hom  := by
  have h₀ := congrArg TwoSquare.natTrans
    ((unboundedFormalism A).lowerShriekBaseChange_paste_vert sqf sqg sqgf)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.mk, TwoSquare.natTrans, Category.assoc] at h₀
  have h := (Iso.eq_inv_comp (Functor.isoWhiskerRight
    ((unboundedFormalism A).lowerShriekCompIso f g)
    ((unboundedFormalism A).pb vZ))).mp h₀
  simp only [Functor.isoWhiskerRight_hom, unbounded_chosen_comp,
    relativeKunneth_chosen_base_change_general, TwoSquare.hComp, TwoSquare.mk,
    TwoSquare.natTrans] at h
  change (_ : ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) g) ⋙
        (upperStar (ModuleCat.{u + 1} A) vZ).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) vX).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f' ≫ g'))) = _ at h
  simp only [Category.assoc] at h
  exact h

/-- Compact-support composition and arbitrary base change commute on the chosen maps.
Source: thm-sf-kunneth-relative, base-change clause.
(blueprint: lem-sf-relative-kunneth-compositor-base-change).

Proof: apply vertical pasting in the exact inverse-image compact-support formalism.
Identify its chosen tower compositor with the inverse native compositor. Conjugate the
pasting equation by the exact/left-derived inverse-image comparisons; naturality and
inverse cancellation remove the intermediate comparison on the middle scheme. -/
theorem relativeKunneth_compositor_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' Z Z' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f' ≫ g')]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c)
    (sqh : IsPullback a (f' ≫ g') (f ≫ g) c)
    (K : DerivedCategoryModule A X) :
    (L((c)^*[ModuleCat.{u + 1} A])).map
        ((rightDerivedLowerShriekCompIso A f g).inv.app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A sqh).app K =
      (rightDerivedLowerShriekBaseChangeMap A sqg).app
          ((R(f)_![ModuleCat.{u + 1} A]).obj K) ≫
        (R(g')_![ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerShriekBaseChangeMap A sqf).app K) ≫
        (rightDerivedLowerShriekCompIso A f' g').inv.app
          ((L((a)^*[ModuleCat.{u + 1} A])).obj K) := by
  have h := congr_app (relativeKunneth_exact_comp_baseChange A sqf sqg sqh) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    unboundedEtaleCompactSupportBaseChange,
    Functor.map_comp, Category.assoc] at h
  have hc : (unboundedEtaleLowerShriekCompIso A f g).hom =
      (rightDerivedLowerShriekCompIso A f g).inv := by
    simp only [unboundedEtaleLowerShriekCompIso, rightDerivedLowerShriekCompIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
      Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerRight_inv]
    rfl
  have hc' : (unboundedEtaleLowerShriekCompIso A f' g').hom =
      (rightDerivedLowerShriekCompIso A f' g').inv := by
    simp only [unboundedEtaleLowerShriekCompIso, rightDerivedLowerShriekCompIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
      Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerRight_inv]
    rfl
  rw [hc, hc'] at h
  have ht := congrArg (fun z ↦
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) c).hom.app _ ≫ z ≫
      (R(f' ≫ g')_![ModuleCat.{u + 1} A]).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a).inv.app K)) h
  simp only [Category.assoc] at ht
  rw [← (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) c).hom.naturality_assoc] at ht
  dsimp only [Functor.comp_obj] at ht
  rw [Iso.hom_inv_id_app_assoc] at ht
  rw [← (rightDerivedLowerShriekCompIso A f' g').inv.naturality] at ht
  simp only [Functor.comp_map, ← Functor.map_comp_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Iso.hom_inv_id_app_assoc, Category.id_comp, Category.comp_id] at ht
  exact ht

/-- Forward, equality-transported form of the compositor/base-change square.
Source: thm-sf-kunneth-relative, base-change clause.
(blueprint: lem-sf-relative-kunneth-compositor-base-change).

Proof: substitute the two composite-map equalities in the preceding square. Precompose
by the pullback of the forward compositor and postcompose by the new forward compositor;
the inverse comparisons cancel. -/
theorem relativeKunneth_compositorOfEq_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' Z Z' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    {h : X ⟶ Z} {h' : X' ⟶ Z'} (w : f ≫ g = h) (w' : f' ≫ g' = h')
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact f'] [QuasiCompact g']
    [QuasiCompact h] [QuasiCompact h']
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification h']
    (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c)
    (sqh : IsPullback a h' h c) (K : DerivedCategoryModule A X) :
    (L((c)^*[ModuleCat.{u + 1} A])).map
        (rightDerivedLowerShriekCompIsoApp A f g h w K).hom ≫
      (rightDerivedLowerShriekBaseChangeMap A sqg).app
        ((R(f)_![ModuleCat.{u + 1} A]).obj K) ≫
      (R(g')_![ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerShriekBaseChangeMap A sqf).app K) =
    (rightDerivedLowerShriekBaseChangeMap A sqh).app K ≫
      (rightDerivedLowerShriekCompIsoApp A f' g' h' w'
        ((L((a)^*[ModuleCat.{u + 1} A])).obj K)).hom := by
  subst h
  subst h'
  have he := relativeKunneth_compositor_baseChange A sqf sqg sqh K
  have ht := congrArg (fun z ↦
    (L((c)^*[ModuleCat.{u + 1} A])).map
      ((rightDerivedLowerShriekCompIso A f g).hom.app K) ≫ z ≫
        (rightDerivedLowerShriekCompIso A f' g').hom.app
          ((L((a)^*[ModuleCat.{u + 1} A])).obj K)) he
  have hid := (L((c)^*[ModuleCat.{u + 1} A])).map_id
    ((R(f ≫ g)_![ModuleCat.{u + 1} A]).obj K)
  simpa only [hid, rightDerivedLowerShriekCompIsoApp, rightDerivedLowerShriekCompIsoOfEq,
    eqToIso_refl, Iso.refl_trans, Iso.app_hom, Functor.comp_obj,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using ht.symm

end AlgebraicGeometry.Etale

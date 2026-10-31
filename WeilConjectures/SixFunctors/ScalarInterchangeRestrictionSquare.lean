/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleProperOpenInterchange
import all WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle
import all WeilConjectures.AlgebraicGeometry.CompactificationRefinementLocalizing

/-! # Scalar extension and the restriction exchange rectangle -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  scalarDirectImageMate
attribute [local implicit_reducible] scalarSixPull TwoSquare moduleObjectDerivedPushforward

private theorem compactSupportPullTriangleScalar {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Z W : Scheme.{u}} (i : X ⟶ Z) (h : Z ⟶ W) (j : X ⟶ W)
    (w : i ≫ h = j)
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)) :
    let kA := Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg (upperStar Λ.X) w.symm) ≪≫ upperStarComp Λ.X i h) ≪≫
      Functor.mapDerivedCategoryCompIso (upperStar Λ.X h) (upperStar Λ.X i)
    let kB := Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg (upperStar Λ'.X) w.symm) ≪≫ upperStarComp Λ'.X i h) ≪≫
      Functor.mapDerivedCategoryCompIso (upperStar Λ'.X h) (upperStar Λ'.X i)
    kB.hom.app ((scalarSixChange a W).obj N) ≫
        (scalarSixPull Λ' i).map ((scalarDirectImagePullbackData.theta a h).inv.app N) ≫
        (scalarDirectImagePullbackData.theta a i).inv.app ((scalarSixPull Λ h).obj N) =
      (scalarDirectImagePullbackData.theta a j).inv.app N ≫
        (scalarSixChange a X).map (kA.hom.app N) := by
  subst j
  dsimp only
  simp only [eqToIso_refl, Iso.refl_trans]
  have ho := IsIso.inv_eq_inv.mpr (scalarDirectImagePullbackData.composition a i h N)
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app] at ho
  change (scalarSixPullComp Λ' i h).hom.app _ ≫
      (scalarSixPull Λ' i).map ((scalarDirectImagePullbackData.theta a h).inv.app N) ≫
      (scalarDirectImagePullbackData.theta a i).inv.app ((scalarSixPull Λ h).obj N) =
    (scalarDirectImagePullbackData.theta a (i ≫ h)).inv.app N ≫
      (scalarSixChange a X).map ((scalarSixPullComp Λ i h).hom.app N)
  apply (cancel_mono ((scalarSixChange a X).map
    ((scalarSixPullComp Λ i h).inv.app N))).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  have ht := congrArg (fun z ↦ (scalarSixPullComp Λ' i h).hom.app
      ((scalarSixChange a W).obj N) ≫ z) ho
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at ht
  rw [← ht]
  rw [(scalarSixChange a X).map_id ((scalarSixPull Λ (i ≫ h)).obj N)]
  exact (Category.comp_id ((scalarDirectImagePullbackData.theta a (i ≫ h)).inv.app N)).symm


set_option maxHeartbeats 8000000 in
-- Derived pullback-compositor comparisons require additional elaboration work.
private theorem scalarInterchangePullbackCoherence
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y W : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ W) [IsOpenImmersion i]
    (c : Compactification.BoundaryCompactification (p ≫ i))
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)) :
    (scalarSixPull Λ' p).map ((scalarDirectImagePullbackData.theta a i).inv.app N) ≫
        (scalarDirectImagePullbackData.theta a p).inv.app ((scalarSixPull Λ i).obj N) ≫
        (scalarSixChange a X).map ((compositionInterchangePullback Λ.X p i c).hom.app N) =
      (compositionInterchangePullback Λ'.X p i c).hom.app ((scalarSixChange a W).obj N) ≫
        (scalarSixPull Λ' c.obj.obj.i).map
          ((scalarDirectImagePullbackData.theta a c.obj.obj.g).inv.app N) ≫
        (scalarDirectImagePullbackData.theta a c.obj.obj.i).inv.app
          ((scalarSixPull Λ c.obj.obj.g).obj N) := by
  with_unfolding_all
    let k := scalarSixPullComp Λ p i
    let k' := scalarSixPullComp Λ' p i
    let l := Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg (upperStar Λ.X) c.obj.obj.comm) ≪≫
          upperStarComp Λ.X c.obj.obj.i c.obj.obj.g) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    let l' := Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg (upperStar Λ'.X) c.obj.obj.comm) ≪≫
          upperStarComp Λ'.X c.obj.obj.i c.obj.obj.g) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    have h₁ := compactSupportPullTriangleScalar a p i (p ≫ i) rfl N
    have h₂ := compactSupportPullTriangleScalar a c.obj.obj.i c.obj.obj.g (p ≫ i)
      c.obj.obj.comm.symm N
    simp only [eqToIso_refl, Iso.refl_trans] at h₁
    change k'.hom.app _ ≫ _ ≫ _ = _ ≫ (scalarSixChange a X).map (k.hom.app N) at h₁
    change l'.hom.app _ ≫ _ ≫ _ = _ ≫ (scalarSixChange a X).map (l.hom.app N) at h₂
    have e : compositionInterchangePullback Λ.X p i c = k.symm ≪≫ l := by
      dsimp [compositionInterchangePullback, k, l, scalarSixPullComp,
        RootCoordinateFace.upperComp]
      apply Iso.ext
      simp only [Iso.trans_hom, Iso.symm_hom,
        Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
        Category.assoc]
    have e' : compositionInterchangePullback Λ'.X p i c = k'.symm ≪≫ l' := by
      dsimp [compositionInterchangePullback, k', l', scalarSixPullComp,
        RootCoordinateFace.upperComp]
      apply Iso.ext
      simp only [Iso.trans_hom, Iso.symm_hom,
        Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
        Category.assoc]
    rw [e, e']
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp]
    have hp := congrArg (fun z ↦ k'.inv.app ((scalarSixChange a W).obj N) ≫ z) h₁
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hp
    rw [← Category.assoc, hp]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
    rw [← h₂]

set_option maxHeartbeats 8000000 in
-- Identify the exact and total-derived adjunction presentations before taking mates.
/-- The normalized scalar direct-image mates commute with the restriction exchange.
Source: latest blueprint, scalar-six compact-support proof, Independence and Composition.
(blueprint: lem-sfb-scalar-interchange-restriction-square).

Proof: express the restriction map as the mate of compositionInterchangePullback. Apply the mate
rectangle to the four geometric adjunctions and inverse normalized scalar pullback squares. The
rectangle's only coherence condition is the pullback composition equation along the two
factorizations of the compactification square; equality transport identifies their composites. -/
theorem scalarInterchangeRestrictionSquare {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y W : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ W) [IsOpenImmersion i]
    (c : Compactification.BoundaryCompactification (p ≫ i))
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X c.obj.obj.Z)) :
    (scalarSixPull Λ' i).map ((scalarDirectImageMate a c.obj.obj.g).app N) ≫
      compositionInterchangeRestriction Λ'.X p i c ((scalarSixChange a c.obj.obj.Z).obj N) ≫
      (RootCoordinateFace.lower Λ'.X p).map
        ((scalarDirectImagePullbackData.theta a c.obj.obj.i).inv.app N) =
    (scalarDirectImagePullbackData.theta a i).inv.app
        ((RootCoordinateFace.lower Λ.X c.obj.obj.g).obj N) ≫
      (scalarSixChange a Y).map (compositionInterchangeRestriction Λ.X p i c N) ≫
      (scalarDirectImageMate a p).app ((scalarSixPull Λ c.obj.obj.i).obj N) := by
  with_unfolding_all
    let α := (compositionInterchangePullback Λ.X p i c).hom
    let α' := (compositionInterchangePullback Λ'.X p i c).hom
    have h := mate_rectangle
      (RootCoordinateFace.adjunction Λ.X c.obj.obj.g)
      (RootCoordinateFace.adjunction Λ.X p)
      (RootCoordinateFace.adjunction Λ'.X c.obj.obj.g)
      (RootCoordinateFace.adjunction Λ'.X p)
      (scalarDirectImagePullbackData.theta a c.obj.obj.g).inv
      (scalarDirectImagePullbackData.theta a p).inv
      (scalarDirectImagePullbackData.theta a c.obj.obj.i).inv
      (scalarDirectImagePullbackData.theta a i).inv α α'
      (scalarInterchangePullbackCoherence a p i c) N
    simpa only [scalarDirectImageMate, compositionInterchangeRestriction, α, α',
      RootCoordinateFace.lower, moduleObjectDerivedPushforward, scalarSixPull,
      ← refinementAdjunction_eq, RootCoordinateFace.adjunction,
      mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk, TwoSquare.natTrans,
      Adjunction.homEquiv_unit, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
      Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id] using h

end AlgebraicGeometry.ProEtale.CondensedRing

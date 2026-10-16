/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence
public import Sheaf.AlgebraicGeometry.PerfectOverlapIsoCancelAbstract
public import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalenceFunctor

/-! # The stage-object map after the open-inclusion comparison -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The remaining stage comparison after crossing from pullback along the
intersection inclusion to exact open restriction. Its defining expression
uses only named natural isomorphisms. -/
@[no_expose] noncomputable def perfectOverlapStageObjectTail
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (q : T ⟶ S) (h : IsPullback g pX pY q)
    (U V L : Y.Opens) (hWL : U ⊓ V ≤ L) :
    (derivedPullback (g ∣_ L) ⋙
      derivedPullback (X.homOfLE (fun _ hx ↦ hWL hx))) ⋙
      (perfectOverlapStageEquivalence g pX pY q h U V).functor ≅
    derivedPullback (Y.homOfLE hWL) ⋙
      derivedPullback (pullback.fst ((U ⊓ V).ι ≫ pY) q) :=
  let i : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ L :=
    homOfLE (fun _ hx ↦ hWL hx)
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (derivedPullback (g ∣_ L))
        (overlapOpenInclusionPullbackIso X i))
      (perfectOverlapStageEquivalence g pX pY q h U V).functor ≪≫
    perfectOverlapStageObjectIso g pX pY q h U V L hWL

/-- Component factorization of the stage-object comparison. Source: the
triangle identities for the open-inclusion comparison.

Proof: expand the definition of the tail. Functoriality combines the inverse
inclusion component with the forward component at the same object. Their
composite is the identity, leaving the original stage-object map. -/
theorem perfectOverlapStageObjectIso_hom_factor
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (q : T ⟶ S) (h : IsPullback g pX pY q)
    (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    (A : schemeDerivedCategory L.toScheme) :
    let i : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ L :=
      homOfLE (fun _ hx ↦ hWL hx)
    ((perfectOverlapStageObjectIso g pX pY q h U V L hWL).app A).hom =
      (perfectOverlapStageEquivalence g pX pY q h U V).functor.map
          ((overlapOpenInclusionPullbackIso X i).inv.app
            ((derivedPullback (g ∣_ L)).obj A)) ≫
        ((perfectOverlapStageObjectTail g pX pY q h U V L hWL).app A).hom := by
  intro i
  simpa only [perfectOverlapStageObjectTail, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app] using
    (perfectOverlapIsoWhiskerRight_inv_cancel
      (Functor.isoWhiskerLeft (derivedPullback (g ∣_ L))
        (overlapOpenInclusionPullbackIso X i))
      (perfectOverlapStageEquivalence g pX pY q h U V).functor
      (perfectOverlapStageObjectIso g pX pY q h U V L hWL) A).symm

set_option maxHeartbeats 8000000 in
-- The stage-object comparison contains nested pullback functors.
/-- The tail component consists only of the fixed derived-pullback
composition comparisons. The inclusion component has already cancelled.

Proof: Use the defining component equation for the stage object isomorphism.
Whiskering preserves composition, so its first factor is the inverse of the
inclusion comparison followed by the first fixed composition comparison.
Apply the abstract inverse-forward cancellation and retain the remaining
three composition factors. -/
theorem perfectOverlapStageObjectTail_hom_app
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (q : T ⟶ S) (h : IsPullback g pX pY q)
    (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    (A : schemeDerivedCategory L.toScheme) :
    let hW' : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ L := fun _ hx ↦ hWL hx
    let e := ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback
    let fac : e.inv ≫ (X.homOfLE hW' ≫ (g ∣_ L)) =
        pullback.fst ((U ⊓ V).ι ≫ pY) q ≫ Y.homOfLE hWL := by
      have restricted : X.homOfLE hW' ≫ (g ∣_ L) =
          (g ∣_ (U ⊓ V)) ≫ Y.homOfLE hWL := by
        apply (cancel_mono L.ι).1
        simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
        rw [← Category.assoc, Scheme.homOfLE_ι]
        rfl
      calc
        e.inv ≫ (X.homOfLE hW' ≫ (g ∣_ L)) =
            e.inv ≫ ((g ∣_ (U ⊓ V)) ≫ Y.homOfLE hWL) := by rw [restricted]
        _ = (e.inv ≫ (g ∣_ (U ⊓ V))) ≫ Y.homOfLE hWL := by
              simp only [Category.assoc]
        _ = _ := by rw [((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback_inv_fst]
    ((perfectOverlapStageObjectTail g pX pY q h U V L hWL).app A).hom =
      ((Functor.isoWhiskerRight
          (perfectHomComposition (X.homOfLE hW') (g ∣_ L))
          (derivedPullback e.inv) ≪≫
        perfectHomComposition e.inv (X.homOfLE hW' ≫ (g ∣_ L)) ≪≫
        eqToIso (congrArg (fun f ↦ derivedPullback f) fac) ≪≫
        (perfectHomComposition (pullback.fst ((U ⊓ V).ι ≫ pY) q)
          (Y.homOfLE hWL)).symm).app A).hom := by
  intro hW' e fac
  unfold perfectOverlapStageObjectTail
  simp only [NatIso.trans_app, Iso.trans_hom]
  rw [perfectOverlapStageObjectIso_hom_app g pX pY q h U V L hWL A]
  simp only [Functor.isoWhiskerRight_trans]
  simp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.symm_hom, Iso.app_hom, Category.assoc]
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Iso.symm_hom, Iso.app_hom]
  simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc]
  have hmap : (perfectOverlapStageEquivalence g pX pY q h U V).functor.map
      ((overlapOpenInclusionPullbackIso X (homOfLE hW')).hom.app
        ((derivedPullback (g ∣_ L)).obj A)) =
    (derivedPullback e.inv).map
      ((overlapOpenInclusionPullbackIso X (homOfLE hW')).hom.app
        ((derivedPullback (g ∣_ L)).obj A)) := by
    rfl
  rw [hmap]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp]
  let i := X.homOfLE hW'
  let α := overlapOpenInclusionPullbackIso X (homOfLE hW')
  let z := ((derivedPullback (g ∣_ L)).obj A)
  let β := (perfectHomComposition i (g ∣_ L)).hom.app A
  have hcancel : (derivedPullback e.inv).map (α.hom.app z) ≫
      (derivedPullback e.inv).map (α.inv.app z ≫ β) =
    (derivedPullback e.inv).map β := by
    rw [← (derivedPullback e.inv).map_comp]
    simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hcancel]

end AlgebraicGeometry

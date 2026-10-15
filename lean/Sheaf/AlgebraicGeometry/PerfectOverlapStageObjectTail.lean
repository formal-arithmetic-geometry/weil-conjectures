/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence
public import Sheaf.AlgebraicGeometry.PerfectOverlapIsoCancelAbstract

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

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Changing coefficient-square coordinates

Source: Stacks Project, Tag 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

section
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
variable
  (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g))
  (hc : ∀ {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
    Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g) =
      Functor.associator (derivedPullback g) (derivedPullback f)
          (derivedPullback h) ≪≫
        Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
          eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
            (Category.assoc h f g)))
include hc
private theorem comp_assoc {W X Y Z : Scheme.{u}}
    (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) (K : schemeDerivedCategory Z) :
    (derivedPullback h).map ((c f g).hom.app K) ≫ (c h (f ≫ g)).hom.app K =
      (c h f).hom.app ((derivedPullback g).obj K) ≫ (c (h ≫ f) g).hom.app K ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) (Category.assoc h f g)) := by
  have hcomp := congrArg (fun t ↦ t.hom.app K) (hc h f g)
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToIso.hom, eqToHom_app, Category.id_comp] using hcomp

end


end AlgebraicGeometry

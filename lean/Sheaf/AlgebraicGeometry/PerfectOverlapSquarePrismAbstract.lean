/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomCompositionPrism
public import Sheaf.AlgebraicGeometry.PerfectOverlapRestrictedComposition

/-! # Square pasting for the fixed derived-pullback comparison -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- Pasting a commuting square to a final arrow agrees with first composing
each horizontal arrow and then comparing the resulting composites.
Source: Stacks Project, Tag 0D5S.

Proof: Apply the fixed three-arrow composition prism to the two paths through
the square. The left side of that prism is the comparison along the upper path.
Its right side begins with the square comparison and then the comparison along
the lower path. Postcompose by the inverse of the latter path's final
composition comparison and cancel. The square comparison's component is the
two fixed `compositionTo` factors by its defining component equation. -/
theorem perfectOverlapSquarePrismAbstract
    {W X Y T Z : Scheme.{u}}
    (r : W ⟶ T) (iK : T ⟶ Y) (f : Y ⟶ Z)
    (iX : W ⟶ X) (j : X ⟶ Y) (g : X ⟶ Z)
    (p : T ⟶ Z) (q : W ⟶ Z)
    (hp : iK ≫ f = p) (hg : j ≫ f = g)
    (hr : r ≫ p = q) (hq : iX ≫ g = q)
    (hs : r ≫ iK = iX ≫ j)
    (A : schemeDerivedCategory Z) :
    (derivedPullback r).map ((compositionTo iK f p hp).hom.app A) ≫
        (compositionTo r p q hr).hom.app A ≫
          (compositionTo iX g q hq).inv.app A =
      (singleComplexOpenSquareComparison j r iK iX hs.symm).app
          ((derivedPullback f).obj A) ≫
        (derivedPullback iX).map ((compositionTo j f g hg).hom.app A) := by
  have H := compositionTo_prism r iK f iX j p g q hp hg hr hq hs A
  have Hhom := congrArg Iso.hom H
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at Hhom
  have Hcancel := congrArg
    (fun z => z ≫ (compositionTo iX g q hq).inv.app A) Hhom
  rw [singleComplexOpenSquareComparison_app_eq_compositionTo]
  simpa only [Iso.app_hom, Iso.app_inv, Functor.comp_obj, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id] using Hcancel

end AlgebraicGeometry

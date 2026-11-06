/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence

/-!
# Pasting of the normalized strict-tower inverse-image square

Source: Stacks, Tag 07A7; the pullback composition coherence calculation used in
(blueprint: lem-cbc-strict-tower-pullback-square-pasting).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] G gComp gCompEq squareG towers_hasDerivedCategory

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem gCompEq_refl {V W S : Scheme.{u}} (f : V ⟶ W) (k : W ⟶ S) :
    gComp B f k = gCompEq B f k (f ≫ k) rfl := by
  unfold gCompEq
  exact (Iso.refl_trans _).symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem squareG_eq {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (w : k ≫ p = r ≫ i) :
    squareG B k r p i w =
      (gCompEq B r i (k ≫ p) w.symm).symm ≪≫ gCompEq B k p (k ≫ p) rfl := by
  unfold squareG gCompEq
  exact normalizeIsoSquare (gComp B r i) (gComp B k p) (congrArg (G B) w.symm)

end AlgebraicGeometry.ProEtale.StrictTower

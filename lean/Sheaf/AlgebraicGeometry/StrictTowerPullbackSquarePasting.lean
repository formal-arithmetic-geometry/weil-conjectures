/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows

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

/-- The inverse-image comparisons of successive commutative squares paste.
Source: Stacks, Tag 07A7, and pullback-composition coherence
(blueprint: lem-cbc-strict-tower-pullback-square-pasting).
Proof: expand each square comparison into the two inverse-image compositors and
the equality of the composite scheme maps. The associativity law for these
compositors identifies both paths with the same comparison from the inverse image
of the composite map to three successive inverse images. This law holds on module
sheaves because the direct-image compositors are restriction along the unique
pullback pasting isomorphisms; their conjugate pullback compositors inherit it.
Whiskering to strict towers and exact derived localization preserve the equation.
No openness or cartesianness is required. -/
theorem squareG_pasting_inv {U U₁ U₂ X X₁ X₂ : Scheme.{u}}
    (j : U ⟶ X) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
    (g : X₁ ⟶ X) (h : X₂ ⟶ X₁) (a : U₁ ⟶ U) (b : U₂ ⟶ U₁)
    (w₁ : a ≫ j = j₁ ≫ g) (w₂ : b ≫ j₁ = j₂ ≫ h)
    (w : (b ≫ a) ≫ j = j₂ ≫ (h ≫ g)) (N : Derived B X) :
    (gComp B b a).hom.app ((G B j).obj N) ≫
        (G B b).map ((squareG B a j₁ j g w₁).inv.app N) ≫
        (squareG B b j₂ j₁ h w₂).inv.app ((G B g).obj N) =
      (squareG B (b ≫ a) j₂ j (h ≫ g) w).inv.app N ≫
        (G B j₂).map ((gComp B h g).hom.app N) := by
  sorry

end AlgebraicGeometry.ProEtale.StrictTower

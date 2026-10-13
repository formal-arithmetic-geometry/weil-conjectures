/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.EtaleOpenFreeSheafPullback

/-! # Pullback of the open identity generator
Source: Stacks Project, Tags 03F3, 01F8 and 01FB.
(blueprint: lem-weil-pbc-etale-open-free-sheaf-unit-pullback)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- The degree-zero identity generator commutes with pullback.
Source: Stacks Project, Tag 03F3 (localization), Tags 01F8/01FB (functoriality).
(blueprint: lem-weil-pbc-etale-open-free-sheaf-unit-pullback)

Proof: Apply the constant-sheaf adjunction at the terminal object of the inverse-image
open, then evaluate the homomorphism from the integers at 1. Naturality turns the left
side into the section classified by etaleOpenFreeSheafPullback, transported by the
localization comparison. By the free abelian Yoneda adjunction this is the inverse-image
unit at the identity generator, restricted along openSectionPullback. The constant-sheaf
pullback adjunct formula turns the right side into pullback of the original identity
section along morphismRestrict. The open restriction pullback unit equation identifies
these sections, including the displayed composition comparisons. The two adjunction
bijections give the morphism equality. All constructions apply also to the empty open.
-/
theorem etaleOpenFreeSheafUnit_pullback {X Y : Scheme.{u}} (g : Y ⟶ X) (W : X.Opens) :
    etaleOpenFreeSheafUnit (g ⁻¹ᵁ W) ≫
      (upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι).map
        (etaleOpenFreeSheafPullback g W) =
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (g ∣_ W)).inv.app
        (AddCommGrpCat.of (ULift ℤ)) ≫
      (upperStar AddCommGrpCat.{u + 1} (g ∣_ W)).map (etaleOpenFreeSheafUnit W) ≫
      ((upperStarComp AddCommGrpCat.{u + 1} (g ∣_ W) W.ι
          ((g ⁻¹ᵁ W).ι ≫ g) (morphismRestrict_ι g W).symm).inv ≫
        (upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι g).hom).app
          ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι)) := by sorry

end AlgebraicGeometry.Etale

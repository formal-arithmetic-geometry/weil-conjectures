/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions

/-! # Higher direct image transition compatibility

Source: Stacks Project, Tags 09Z1 and 03Q8, canonical comparison maps.
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The transition is natural in its coefficient sheaf.
Source: Stacks Tag 09Z1, canonical comparison maps; Tag 03Q8.
(blueprint: lem-sbc-higher-image-transition-naturality).

Proof: write the derived transition as the composite natural transformation formed by
the h' adjunction unit, the pullback composition comparison, and pullback of the h
adjunction counit. Each is natural, so its naturality square commutes for F[0]→G[0].
The single-complex comparison is itself natural, and applying Rh'_* and homology
preserves the commuting square. This gives the displayed equality. For identity maps
it is reflexivity, for zero maps it is the zero equality by additivity, and the argument
uses no geometric or cohomological bound assumptions.
-/
theorem higher_direct_image_transition_naturality
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S)
    (w : a ≫ h = h') (q : ℤ)
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (f : F ⟶ G) :
    (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h)_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map f)) ≫
      higherDirectImageTransition Λ a h h' w q G =
    higherDirectImageTransition Λ a h h' w q F ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h')_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            (((a)^*[ModuleCat.{u + 1} Λ]).map f))) := by sorry

end AlgebraicGeometry.Etale

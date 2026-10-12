/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Identity triangle for higher direct images

Source: Stacks Project, Tag 09Z1, canonical comparison maps, and Tag 03Q8.
(blueprint: lem-sbc-higher-image-transition-identity).
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The transition for the identity triangle becomes the identity after identifying
identity pullback with the original sheaf.
Source: Stacks Project, Tag 09Z1, canonical comparisons; Tag 03Q8.
(blueprint: lem-sbc-higher-image-transition-identity).

Proof: Expand the transition before taking homology. The inverse-image composition
comparison for `id ≫ h = h` is the inverse of the identity comparison whiskered by
`h^*`. Move this comparison past the counit by naturality, and cancel the unit and
counit of `h^* ⊣ Rh_*` by the triangle identity. The comparison between derived
identity pullback and identity, followed by the single-functor comparison and the
single-functor image of the sheaf identity comparison, is the identity. This follows
by applying the defining factorization of the exact derived functor to the complex
concentrated in degree zero. Thus the entire derived morphism is the identity.
Apply degree-q homology, which preserves identities. -/
theorem higher_direct_image_transition_identity
    (Λ : Type (u + 1)) [CommRing Λ] {S Y : Scheme.{u}} (h : Y ⟶ S)
    (q : ℤ) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    higherDirectImageTransition Λ (𝟙 Y) h h (Category.id_comp h) q F ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h)_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarId (ModuleCat.{u + 1} Λ) Y).hom.app F))) = 𝟙 _ := by sorry

end AlgebraicGeometry.Etale

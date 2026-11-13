/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions


import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition
import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitionNaturality

/-! # Composition of higher direct image triangles

## References

* Stacks Project, Tags 09Z1 and 03Q8
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The two successive transitions in a tower of commutative triangles agree with
its composite, after the ordinary pullback composition comparison.
(Stacks, Tags 09Z1 and 03Q8) -/
theorem higher_direct_image_transition_composition
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' Y'' : Scheme.{u}}
    (a : Y' ⟶ Y) (b : Y'' ⟶ Y') (h : Y ⟶ S) (h' : Y' ⟶ S) (h'' : Y'' ⟶ S)
    (wa : a ≫ h = h') (wb : b ≫ h' = h'') (q : ℤ)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (F' : Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (F'' : Sheaf Y''.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : ((a)^*[ModuleCat.{u + 1} Λ]).obj F ⟶ F')
    (g : ((b)^*[ModuleCat.{u + 1} Λ]).obj F' ⟶ F'') :
    higherDirectImageTransition Λ (b ≫ a) h h''
        (by rw [Category.assoc, wa, wb]) q F ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h'')_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) b a).hom.app F ≫
            ((b)^*[ModuleCat.{u + 1} Λ]).map f ≫ g))) =
      (higherDirectImageTransition Λ a h h' wa q F ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h')_*[ModuleCat.{u + 1} Λ]).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map f))) ≫
      (higherDirectImageTransition Λ b h' h'' wb q F' ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h'')_*[ModuleCat.{u + 1} Λ]).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map g)))  := by
  have hc := higher_direct_image_transition_core_composition Λ a b h h' h'' wa wb q F
  have hn := higher_direct_image_transition_naturality Λ b h' h'' wb q
    (((a)^*[ModuleCat.{u + 1} Λ]).obj F) F' f
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc, ← reassoc_of% hn]


end AlgebraicGeometry.Etale

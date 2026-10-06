/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Vanishing of pulled-back étale cohomology classes

For a morphism of schemes `f : X ⟶ Y` the comparison map
`AlgebraicGeometry.Etale.cohomologyMap f F n : H^n(Y_ét, F) ⟶ H^n(X_ét, f^* F)` pulls
cohomology classes back. This file records how the *vanishing* of a pulled-back class behaves:
it does not change when the coefficient sheaf is replaced by an isomorphic one, and in degree
one pulling back along `g` and then along `f` kills a class exactly when pulling back along
`f ≫ g` does. These are the statements used to say that a class "dies" on a cover.

## Main statements

- `AlgebraicGeometry.Etale.cohomologyMap_map_eq_zero_iff`: invariance under isomorphisms of
  the coefficient sheaf.
- `AlgebraicGeometry.Etale.cohomologyMap_cohomologyMap_eq_zero_iff`: pulling back in two steps
  kills a class of degree one exactly when pulling back along the composite does.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Etale

variable {X Y Z : Scheme.{u}}

/-- The map on cohomology induced by an isomorphism of sheaves is injective. -/
lemma injective_sheafHMap_of_isIso {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G) [IsIso φ] (n : ℕ) : Function.Injective (Sheaf.H.map φ n) := by
  intro a b h
  have := congrArg (Sheaf.H.map (inv φ) n) h
  simpa [Sheaf.H.map, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀] using this

/-- Replacing the coefficient sheaf by an isomorphic one does not change whether a class
vanishes after pulling back along `f`. -/
lemma cohomologyMap_map_eq_zero_iff (f : X ⟶ Y)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [IsIso φ] (n : ℕ)
    (x : Sheaf.H F n) :
    cohomologyMap f G n (Sheaf.H.map φ n x) = 0 ↔ cohomologyMap f F n x = 0 := by
  rw [cohomologyMap_map, ← map_zero (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map φ) n)]
  exact (injective_sheafHMap_of_isIso _ n).eq_iff

/-- A class of degree one on `Z` dies after pulling back along `g : Y ⟶ Z` and then along
`f : X ⟶ Y` exactly when it dies after pulling back along `f ≫ g`. -/
theorem cohomologyMap_cohomologyMap_eq_zero_iff (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (hk : f ≫ g = k) (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : Sheaf.H F 1) :
    cohomologyMap f _ 1 (cohomologyMap g F 1 x) = 0 ↔ cohomologyMap k F 1 x = 0 := by
  subst hk
  rw [cohomologyMap_apply, cohomologyMap_apply, cohomologyMap_apply]
  exact Ext.mk₀_comp_mapExactFunctor_comp_eq_zero_iff _ _ _
    (upperStarComp AddCommGrpCat.{u + 1} f g) _ _ _ x

/-- A class dies after pulling back along `f` as soon as it dies after pulling back along a
morphism `g` through which `f` factors. -/
lemma cohomologyMap_eq_zero_of_fac (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (x : Sheaf.H F 1)
    (hx : cohomologyMap g F 1 x = 0) : cohomologyMap k F 1 x = 0 := by
  rw [← cohomologyMap_cohomologyMap_eq_zero_iff f g k hk, hx, map_zero]

end AlgebraicGeometry.Etale

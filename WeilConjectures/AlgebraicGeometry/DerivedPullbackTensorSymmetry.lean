/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-!
# Derived pullback preserves the canonical tensor symmetry

Source: Stacks Project, Tag 06YU; the symmetry conjugation in step 6 of
`lem-asd-compact-projection-exchange`.
-/

@[expose] public section

universe u' u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

/-- Exact derived pullback preserves the canonical signed tensor symmetry.
Source: Stacks Project, Tag 06YU, and step 6 of `lem-asd-compact-projection-exchange`. -/
theorem derivedPullback_tensorSymmetry
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((g)^*[ModuleCat.{u + 1} Λ]).map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) Y).hom.app K).app M) ≫
      ((leftDerivedUpperStarTensorComparison _ g).app M).app K =
    ((leftDerivedUpperStarTensorComparison _ g).app K).app M ≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app
        (L((g)^*[ModuleCat.{u + 1} Λ]).obj K)).app
          (L((g)^*[ModuleCat.{u + 1} Λ]).obj M) := by
  exact leftDerivedUpperStar_map_braiding_hom_δ (ModuleCat.{u + 1} Λ) g K M

end AlgebraicGeometry.Etale

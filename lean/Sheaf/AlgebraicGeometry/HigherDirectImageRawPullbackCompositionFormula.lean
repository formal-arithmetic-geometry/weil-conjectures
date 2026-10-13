/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality
import Sheaf.AlgebraicGeometry.EtalePullbackSingleComp
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Bundled formula for composition of raw cohomology pullbacks

Source: Stacks Project, Tag 09Z1, canonical comparison maps.
(blueprint: lem-sbc-higher-image-raw-pullback-composition-formula).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The explicit raw pullback formula is compositional as a function on classes.
Source: Stacks Project, Tag 09Z1, canonical comparison maps. The proof expands the
five factors, applies derived inverse-image composition, upper-star associativity,
single-functor composition, and shift compatibility.
(blueprint: lem-sbc-higher-image-raw-pullback-composition-formula) -/
theorem higherDirectImageRawOverPullback_function_comp
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B C : Over W} (f : A ⟶ B) (g : B ⟶ C) (U : S.Etale) :
    higherDirectImageRawOverPullback Λ k G q (f ≫ g) U =
      (higherDirectImageRawOverPullback Λ k G q f U) ∘
        (higherDirectImageRawOverPullback Λ k G q g U) := by sorry

end AlgebraicGeometry.Etale

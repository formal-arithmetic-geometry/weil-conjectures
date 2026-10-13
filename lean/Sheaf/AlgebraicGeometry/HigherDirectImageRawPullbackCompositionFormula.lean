/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality
import Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackComposition
import Sheaf.AlgebraicGeometry.HigherDirectImageRestrictedCoefficientComposition

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
        (higherDirectImageRawOverPullback Λ k G q g U)  := by
  funext z
  let KC := (DerivedCategory.Plus.singleFunctor _ 0).obj
    (((C.hom)^*[ModuleCat.{u + 1} Λ]).obj G)
  let KB := (DerivedCategory.Plus.singleFunctor _ 0).obj
    (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G)
  let KA := (DerivedCategory.Plus.singleFunctor _ 0).obj
    (((A.hom)^*[ModuleCat.{u + 1} Λ]).obj G)
  let vg : D+((g.left)^*[ModuleCat.{u + 1} Λ]).obj KC ⟶ KB :=
    (((g.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) g.left C.hom B.hom
          (Over.w g).symm).inv.app G)
  let vf : D+((f.left)^*[ModuleCat.{u + 1} Λ]).obj KB ⟶ KA :=
    (((f.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
          (Over.w f).symm).inv.app G)
  have hc := higherDirectImageRestrictedCoefficient_comp Λ G f g
  have h := higherDirectImageRawTrianglePullback_comp Λ f.left g.left
    (C.hom ≫ k) (B.hom ≫ k) (A.hom ≫ k)
    (by rw [← Category.assoc, Over.w])
    (by rw [← Category.assoc, Over.w]) q KC KB KA vg vf U z
  dsimp only [vg, vf] at h
  rw [hc] at h
  simpa only [higherDirectImageRawOverPullback, Function.comp_apply,
    Over.comp_left, KC, KB, KA] using h

end AlgebraicGeometry.Etale

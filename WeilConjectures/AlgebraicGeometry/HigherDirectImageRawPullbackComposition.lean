/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverNaturality
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula

/-! # Composition of raw cohomology pullbacks

## References

* Stacks Project, Tag 09Z1
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Two raw pullbacks agree with the pullback of the composite arrow in `Over W`.
No affineness, limit, or quasi-compactness hypothesis is used. (Stacks, Tag 09Z1) -/
theorem higherDirectImageRawOverPullback_comp
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B C : Over W} (f : A ⟶ B) (g : B ⟶ C) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q C).obj (op U)) :
    higherDirectImageRawOverPullback Λ k G q (f ≫ g) U z =
      higherDirectImageRawOverPullback Λ k G q f U
        (higherDirectImageRawOverPullback Λ k G q g U z) := by
  have h := higherDirectImageRawOverPullback_function_comp Λ k G q f g U
  exact congrFun h z

end AlgebraicGeometry.Etale

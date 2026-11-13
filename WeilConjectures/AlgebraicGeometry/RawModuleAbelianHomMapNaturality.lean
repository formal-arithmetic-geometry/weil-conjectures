/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap
import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomSourceFormula
import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomTargetFormula

/-! # Naturality of the fixed raw scalar comparison

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
/-- The concrete scalar comparison commutes with the five-factor raw pullback. -/
theorem rawModuleAbelianHomMap_naturality
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale) :
    ∀ (A B : Over W) (f : A ⟶ B)
        (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)),
        rawModuleAbelianHomMap Λ k G q U A
          ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z) =
          abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) q
            (restrictedOverCoefficient
              ((sheafCompose _
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) B)
            (restrictedOverCoefficient
              ((sheafCompose _
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) A)
            ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
              (Over.w f).symm).inv.app
                ((sheafCompose _
                  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G))
            U (rawModuleAbelianHomMap Λ k G q U B z) := by
  intro A B f z
  have hs := rawModuleAbelianHomMap_source_formula Λ k G q U A B f z
  have ht := rawModuleAbelianHomMap_target_formula Λ k G q U A B f z
  have hc := rawModuleScalar_coefficient_square Λ G (q : ℤ) A B f
  exact hs.trans
    ((congrArg (fun t ↦ rawModuleScalarSourcePrefix Λ k G q U A B f z ≫ t) hc).trans ht.symm)

end AlgebraicGeometry.Etale

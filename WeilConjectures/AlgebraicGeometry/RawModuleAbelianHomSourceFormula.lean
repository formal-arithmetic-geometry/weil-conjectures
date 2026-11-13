/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourcePrefix
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientSquare
import WeilConjectures.AlgebraicGeometry.RawModuleScalarHomCompositeFormula
import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceClassFormula

/-! # The source and class factors of the raw scalar comparison

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Expand the module pullback and commute only its source and class factors.
The coefficient comparison is deliberately retained as the module coefficient tail. -/
theorem rawModuleAbelianHomMap_source_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    rawModuleAbelianHomMap Λ k G q U A
      ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z) =
    rawModuleScalarSourcePrefix Λ k G q U A B f z ≫
      ((moduleAbelianDerivedUpperStarIso Λ f.left).hom.app
          (((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G))⟦(q : ℤ)⟧) ≫
        (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus.map
          (moduleCoefficientFactor Λ G (q : ℤ) A B f) ≫
        scalarCoefficientFactor Λ A.hom G (q : ℤ)) := by
  have hs := rawModuleScalar_source_class_formula Λ k G q U A B f z
  have ht := congrArg
    (fun v ↦ v ≫
      (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus.map
        (moduleCoefficientFactor Λ G (q : ℤ) A B f) ≫
      scalarCoefficientFactor Λ A.hom G (q : ℤ)) hs
  have he := rawModuleScalar_hom_composite_formula Λ k G q U A B f z
  apply he.trans
  simpa only [Category.assoc] using ht

end AlgebraicGeometry.Etale

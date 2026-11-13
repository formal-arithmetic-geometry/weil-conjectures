/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientFactors
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceFactors

/-! # Module raw pullback factorization

## Implementation details

The module formula for the raw pullback is stated over `B` as a separate declaration, which
keeps the `unop (op B)` objects of `higherDirectImageRawOverFunctor` out of the kernel check of
the associativity step. That step is a general lemma over arbitrary categories, instantiated
with explicit arguments so that the kernel matches the factors argument by argument instead of
unfolding composites in the derived category.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- A raw triangle map whose functors are precomposed with `L` is the composite of any morphism
equal to its source, the image of the class, and the coefficient. -/
private theorem rawTriangleMap_whiskerLeft_eq_comp
    {C₀ C D E D' E' : Type*} [Category C₀] [Category C] [Category D] [Category E]
    [Category D'] [Category E'] [Preadditive D'] [Preadditive E']
    (L : C₀ ⥤ C) (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F) (U : C₀) {K : D'} {K' : E'}
    (z : (((L ⋙ H) ⋙ A).op ⋙ preadditiveYoneda.obj K).obj (op U)) (s : F.obj K ⟶ K')
    (src : B.obj (H'.obj (L.obj U)) ⟶ F.obj (A.obj (H.obj (L.obj U))))
    (hsrc : rawTriangleSource H H' P A B F c e (L.obj U) = src) :
    rawTriangleMap (L ⋙ H) (L ⋙ H') P A B F (Functor.whiskerLeft L c) e U z s =
      src ≫ F.map z ≫ s := by
  subst hsrc
  exact (Category.assoc _ _ _).symm

/-- The module formula for the raw pullback itself, stated over `B` rather than through the
functor `higherDirectImageRawOverFunctor`. -/
private theorem higherDirectImageRawOverPullback_eq_moduleFactors
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale)
    {A B : Over W} (f : A ⟶ B)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    higherDirectImageRawOverPullback Λ k G q f U z =
      moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z ≫
        moduleCoefficientFactor Λ G q A B f :=
  rawTriangleMap_whiskerLeft_eq_comp (freeSheaf Λ S)
    (upperStar (ModuleCat.{u + 1} Λ) (B.hom ≫ k)) (upperStar (ModuleCat.{u + 1} Λ) (A.hom ≫ k))
    (upperStar (ModuleCat.{u + 1} Λ) f.left)
    (DerivedCategory.Plus.singleFunctor _ 0) (DerivedCategory.Plus.singleFunctor _ 0)
    (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus
    (upperStarComp (ModuleCat.{u + 1} Λ) f.left (B.hom ≫ k) (A.hom ≫ k)
      (show f.left ≫ B.hom ≫ k = A.hom ≫ k by rw [← Category.assoc, Over.w]).symm).hom
    ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlusSingleFunctor 0).inv U z
    (moduleCoefficientFactor Λ G q A B f) _ rfl

/-- The module raw map is the composite of its source, class, and coefficient factors. -/
theorem rawModuleScalar_pullback_module_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z =
      moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z ≫
        moduleCoefficientFactor Λ G (q : ℤ) A B f) :=
  higherDirectImageRawOverPullback_eq_moduleFactors Λ k G q U f z

end AlgebraicGeometry.Etale

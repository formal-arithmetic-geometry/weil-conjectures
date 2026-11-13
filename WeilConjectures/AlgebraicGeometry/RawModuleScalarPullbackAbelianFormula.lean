/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceFactors
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientSquare

/-! # Abelian raw pullback factorization

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
/-- The abelian raw map factors independently of any module cohomology class. -/
theorem rawModuleScalar_pullback_abelian_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B) :
    ∀ (x : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) q
      (restrictedOverCoefficient ((moduleAbelianForget Λ W).obj G) B)).obj
        (op U)),
      abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) q _ _
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app ((moduleAbelianForget Λ W).obj G)) U x =
      abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) (RawModuleScalarComparison.freeAbelian S U) ≫
      (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map x ≫
      abelianCoefficientFactor ((moduleAbelianForget Λ W).obj G)
        (q : ℤ) A B f := by
  intro x
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.Etale

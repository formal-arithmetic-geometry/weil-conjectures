/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientFactors
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceFactors

/-! # Module raw pullback factorization
Source: Stacks Project, Tags 03FD and 03Q8.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The module raw map is the composite of its source, class, and coefficient factors.
Source: Stacks Project, Tags 03FD and 03Q8, explicit-map expansion in the proof of
lem-sbc-raw-module-abelian-hom-map-naturality.
(blueprint: lem-sbc-raw-scalar-pullback-module-formula).

Proof: The object and map fields of higherDirectImageRawOverFunctor give the raw
presheaf value and higherDirectImageRawOverPullbackHom. Evaluate the latter using
higherDirectImageRawOverPullbackHom_apply. Unfold higherDirectImageRawOverPullback,
higherDirectImageRawTrianglePullback, and rawTriangleMap. The source is the single
functor applied to the upperStarComp hom, followed by the inverse single comparison;
these are exactly moduleSourceFactor. The coefficient is the shift comparison followed
by the shifted higherDirectImageRawOverCoefficient. Expand that named coefficient to
its single comparison and single of the inverse upperStarComp; these are exactly
moduleCoefficientFactor. Category.assoc regroups the first two maps and retains the
middle derived image of z and the last two maps. Proof irrelevance identifies the two
proofs of the Over triangle. No scalar-forgetting square or relation to an abelian
class is used. This also covers q = 0, z = 0, and identity f. -/
theorem rawModuleScalar_pullback_module_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z =
      moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z ≫
        moduleCoefficientFactor Λ G (q : ℤ) A B f) := by
  simp only [higherDirectImageRawOverFunctor,
    higherDirectImageRawOverPullbackHom_apply, higherDirectImageRawOverPullback,
    higherDirectImageRawTrianglePullback, rawTriangleMap, moduleSourceFactor,
    rawTriangleSource, moduleCoefficientFactor, Category.assoc]; rfl

end AlgebraicGeometry.Etale

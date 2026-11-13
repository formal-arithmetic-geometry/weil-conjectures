/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceFactors
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientSquare
public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap

/-! # Concrete formulas for raw scalar comparison

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

attribute [local instance] moduleSheafCategory moduleSheafPreadditive moduleSheafAbelian
  moduleSheafHasDerivedCategory

/-- Evaluation of the explicit additive scalar Hom map. -/
theorem rawModuleScalarHom_evaluate
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A : Over W)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op A)) :
    rawModuleAbelianHomMap Λ k G q U A z =
      scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus.map z ≫
        scalarCoefficientFactor Λ A.hom G (q : ℤ) := by
  rfl

end AlgebraicGeometry.Etale

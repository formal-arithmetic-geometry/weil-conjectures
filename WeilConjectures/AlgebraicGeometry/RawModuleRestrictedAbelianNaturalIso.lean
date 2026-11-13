/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram
public import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianComplexData
import WeilConjectures.AlgebraicGeometry.RawModuleRestrictedAbelianNonnegative
import WeilConjectures.AlgebraicGeometry.RawModuleRestrictedAbelianNegative

/-! # Raw module Hom and restricted abelian cohomology

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The scalar-forgetting comparison is natural for the fixed five-factor pullback.
There are no limit, qcqs, affineness, or indexing assumptions in this comparison. -/
theorem exists_rawModule_restrictedAbelian_natural_iso
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale) :
    ∃ e : ∀ A : Over W,
      (higherDirectImageRawOverFunctor Λ k G q U).obj (op A) ≅
        restrictedOverCohomology k
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
          q A U,
      ∀ (A B : Over W) (f : A ⟶ B),
        (higherDirectImageRawOverFunctor Λ k G q U).map f.op ≫ (e A).hom =
          (e B).hom ≫ restrictedOverCohomologyMap k
            ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
            q f U := by
  classical
  by_cases hq : 0 ≤ q
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    exact exists_rawModule_restrictedAbelian_nonnegative Λ k G p U
  · exact exists_rawModule_restrictedAbelian_negative Λ k G q U (lt_of_not_ge hq)

end AlgebraicGeometry.Etale

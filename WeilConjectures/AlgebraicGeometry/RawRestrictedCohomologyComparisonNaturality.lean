/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
import WeilConjectures.AlgebraicGeometry.RestrictedComparisonGeneratorPullback

/-! # Pullback compatibility of restricted derived-Hom evaluation

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit evaluation map commutes with the explicit raw pullback.
This asserts compatibility of a constructed map, independently of invertibility. -/
theorem rawRestrictedCohomologyComparison_naturality {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F') (U : S.Etale)
    (t : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)) :
    rawAffineRestrictedCohomologyMap a h h' w p F F' φ U
        (rawRestrictedCohomologyComparison h p F U t) =
      rawRestrictedCohomologyComparison h' p F' U
        (abelianHigherDirectImageRawPullback a h h' w p F F' φ U t) := by
  let G := (upperStar AddCommGrpCat.{v + 1} h).obj
    (RawRestrictedComparison.freeSheaf S U)
  let G' := (upperStar AddCommGrpCat.{v + 1} h').obj
    (RawRestrictedComparison.freeSheaf S U)
  let e : (upperStar AddCommGrpCat.{v + 1} a).obj G ≅ G' :=
    ((upperStarComp AddCommGrpCat.{v + 1} a h h' w.symm).app
      (RawRestrictedComparison.freeSheaf S U)).symm
  let x := (RawRestrictedComparison.zeroIso
    ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U) G).inv
      (RawRestrictedComparison.generator h U)
  have square := RawRestrictedComparison.restrictedDerivedEvaluation_pullback
    a h h' w p G G' e F F' φ U t
  have at_x := congrArg (fun f ↦ f x) square
  simp only [AddCommGrpCat.comp_apply] at at_x
  have gen := RawRestrictedComparison.restrictedComparison_generator_pullback a h h' w U
  change RawRestrictedComparison.transportZero a h h' w G G' e.hom U x = _ at gen
  rw [gen] at at_x
  change rawAffineRestrictedCohomologyMap a h h' w p F F' φ U
      ((RawRestrictedComparison.shiftIso h p F U).hom
        ((RawRestrictedComparison.Hzero h U).map t x)) = _
  exact at_x

end AlgebraicGeometry.Etale

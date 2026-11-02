/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassReductionPullback

/-! # The unit normalization of scalar extension and geometric pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The scalar/pullback square preserves the full adjunction unit.

Source: blueprint latest, diagonal coefficient changes (3), ordinary source cones.
(blueprint: lem-diagonal-scalar-pullback-unit).

Proof: the scalar/pullback square is the inverse conjugate of the identity square
of the two right adjoints. The unit identity for conjugate transformations identifies
its composite with the unit of the first composite adjunction with the unit of the
second. Expand the composite units. This applies to every integral sheaf and every
scheme map, including the empty scheme. -/
theorem diagonalScalarPullback_unit (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (M : DiagonalAb S) :
    (diagonalScalarAdjunction l S).unit.app M ≫ (diagonalForget l S).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l]))
          f).homEquiv _ _ ((diagonalClassScalarPullback l f).hom.app M)) =
      (upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M ≫
        (lowerStar Ab.{u + 1} f).map ((diagonalScalarAdjunction l X).unit.app
          ((upperStar Ab.{u + 1} f).obj M)) := by
  let a := (upperStarLowerStarAdjunction Ab.{u + 1} f).comp
    (diagonalScalarAdjunction l X)
  let b := (diagonalScalarAdjunction l S).comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
  have h := unit_conjugateEquiv_symm a b (𝟙 _) M
  change a.unit.app M ≫ 𝟙 _ = b.unit.app M ≫
    (diagonalForget l S).map ((lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).map
      ((diagonalClassScalarPullback l f).hom.app M)) at h
  erw [Category.comp_id] at h
  simpa only [a, b, Adjunction.comp_unit_app, Adjunction.homEquiv_unit,
    Functor.map_comp, Category.assoc] using! h.symm

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

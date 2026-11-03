/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorCoefficientTensor
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorClosedComposition
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits
/-! # The fixed coefficient projection in the successor calculation

Source: the coefficient multiplication and projection-formula calculation in the
zero-section proof of the current blueprint.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

/-- The coefficient splitting followed by section projection is ordinary closed
composition in degree zero. No arbitrary supported class or boundary enters.
Source: the coefficient/projection step of the zero-section argument.
(blueprint: lem-pur-coordinate-successor-coefficient-projection).

Proof: identify the pulled-back old support and newest divisor with the tail
intersection and the last section. After these identifications, restriction of
constant coefficients identifies cup multiplication with the ordinary projection
map: the latter is adjoint to tensor pullback followed by the counit. The
restrictions are epic and tensor preserves epimorphisms, so the coefficient
square commutes. Pass through the canonical derived-single tensor comparison.
For the closed section, transport the projection from its chosen compactification
to ordinary proper direct image, using the open-to-direct-image comparison and
composition of right-derived functors. The section identity cancels the inverse
image compositor, and the canonical coefficient unit cancels the left tensor
factor. The remaining map is exactly the ordinary lowerStar compositor,
conjugated by the closed-single comparisons, which defines the right side. -/
theorem coordinate_successor_coefficient_projection (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    letI : IsNoetherianRing (setting P n).Coefficient :=
      isNoetherian_of_finite (setting P n).Coefficient (setting P n).Coefficient
    let := zero_exact P n B aB r
    successorCoefficientTensor P n B aB r ≫
      sectionProjectionRaw (setting P n).Coefficient (lastSection B r) (lastProjection B r)
        (Scheme.Hom.toIteratedAffineLine_comp_over (𝟙 _) (fun _ ↦ 0))
        (unit P n (iteratedAffineLine B r))
        ((cupSingle (setting P n) (iteratedAffineLine B r)).obj
          ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B r)).obj
            ((setting P n).constant B)))
        (coefficientUnitIso P n (iteratedAffineLine B r)) =
      successorClosedComposition P n B aB r := by sorry

end AlgebraicGeometry.ProEtale.AffineZeroPurity

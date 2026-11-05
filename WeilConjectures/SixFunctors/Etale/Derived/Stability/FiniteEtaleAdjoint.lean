/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-!
# The right adjoint of the direct image along a finite étale morphism

For a finite étale morphism `e : V ⟶ X` the direct image `e_*` of étale sheaves is exact, being
both a left adjoint (of `e^*`, `AlgebraicGeometry.Etale.lowerStarUpperStarAdjunctionOfIsFinite`)
and a right adjoint (of `e^*`). Consequently `Re_! ≅ Re_* ≅ D(e_*)`, and `D(e_*) ⊣ D(e^*)` on the
derived categories (`prop-exc-finite-etale-adjoint`).

The blueprint states the proposition on the small pro-étale sites; the pro-étale direct image along
a finite étale morphism is not available in the library, and the statement is made on the small
étale sites, where the exceptional inverse image of the library lives.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {V X : Scheme.{u}} (e : V ⟶ X) [IsFinite e] [_root_.AlgebraicGeometry.Etale e]

/-- The direct image along a finite étale morphism preserves finite limits, being right adjoint
to the pullback. -/
instance preservesFiniteLimits_lowerStar_of_isFinite_of_etale :
    PreservesFiniteLimits (e)_*[A] :=
  have : PreservesLimitsOfSize.{0, 0} (e)_*[A] :=
    (Etale.upperStarLowerStarAdjunction A e).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _

end Etale

end AlgebraicGeometry

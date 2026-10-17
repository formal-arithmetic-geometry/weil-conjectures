/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The derived completion is a linear triangulated functor

Let `(C, J)` be an essentially small site and `E` a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`. The
derived completion `D(J, 𝒪_E) ⥤ D_comp(J, 𝒪_E)`
(`DerivedCategoryDerivedCompleteIntegral.completion`) is left adjoint to the inclusion of the
triangulated subcategory of derived complete objects, which is an `𝒪_E`-linear triangulated
functor. Hence the derived completion commutes with the shifts, is triangulated and is
`𝒪_E`-linear. In particular `𝒪_E`-linear triangulated functors between the derived categories
induce, after composition with the inclusion and the derived completion, `𝒪_E`-linear
triangulated functors between the integral stages, which pass to the rational stages
(`CategoryTheory.Rationalization.map`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace DerivedCategoryDerivedCompleteIntegral

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E]

/-- The inclusion `D_comp(J, 𝒪_E) ⥤ D(J, 𝒪_E)` commutes with the shifts. -/
noncomputable instance commShift_ι : (ι J l E).CommShift ℤ :=
  inferInstanceAs ((DerivedCategory.derivedCompleteIntegral J l E).ι.CommShift ℤ)

/-- The inclusion `D_comp(J, 𝒪_E) ⥤ D(J, 𝒪_E)` is triangulated. -/
instance isTriangulated_ι : (ι J l E).IsTriangulated :=
  inferInstanceAs ((DerivedCategory.derivedCompleteIntegral J l E).ι.IsTriangulated)

/-- The inclusion `D_comp(J, 𝒪_E) ⥤ D(J, 𝒪_E)` is `𝒪_E`-linear. -/
instance linear_ι : (ι J l E).Linear (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  inferInstanceAs ((DerivedCategory.derivedCompleteIntegral J l E).ι.Linear
    (Shrink.{u + 1} (PadicAlgCl.integers l E)))

/-- The derived completion commutes with the shifts, as the left adjoint of the inclusion. -/
noncomputable instance commShift_completion : (completion J l E).CommShift ℤ :=
  (completionAdjunction J l E).leftAdjointCommShift ℤ

instance commShift_completionAdjunction : (completionAdjunction J l E).CommShift ℤ :=
  (completionAdjunction J l E).commShift_of_rightAdjoint ℤ

/-- The derived completion is triangulated, as the left adjoint of a triangulated functor. -/
instance isTriangulated_completion : (completion J l E).IsTriangulated :=
  (completionAdjunction J l E).isTriangulated_leftAdjoint

/-- The derived completion is `𝒪_E`-linear, as the left adjoint of an `𝒪_E`-linear functor. -/
instance linear_completion :
    (completion J l E).Linear (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  (completionAdjunction J l E).left_adjoint_linear

end DerivedCategoryDerivedCompleteIntegral

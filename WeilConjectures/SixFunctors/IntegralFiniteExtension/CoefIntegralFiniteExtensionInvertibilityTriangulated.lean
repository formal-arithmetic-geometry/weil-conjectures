/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionTriangulatedPrecomp
/-! Auxiliary reduction for finite-extension triangulation.
Source: current blueprint, lem-coef-integral-finite-extension.proof.md, paragraph 1
(blueprint: lem-sf-integral-finite-extension-invertibility). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
-- STATEMENT-DISPUTED (old version): an arbitrary coherent shift need not be exact.
/-- Triangulatedness descends from the derived quotient for the same shift comparison.
Source: the localization presentation of distinguished triangles
(blueprint: lem-sf-integral-finite-extension-triangulated-isTriangulated). -/
theorem comparison_invertibility_triangulated_isTriangulated
    (c : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ)
    (h : letI := c
      (DerivedCategory.Qh ⋙ integralScalarExtensionOfUniverses l E L ι X).IsTriangulated) :
    letI := c
    (integralScalarExtensionOfUniverses l E L ι X).IsTriangulated := by
  letI := c
  letI := h
  exact Functor.isTriangulated_of_precomp (DerivedCategory.Qh (C := _))
    (integralScalarExtensionOfUniverses l E L ι X)

/-- The strict finite-free scalar functor admits a shift making it triangulated.
Source: finite-free Roos total-limit triangulation and localization of the
K-flat representative functor. (blueprint: lem-sf-integral-finite-extension-triangulated)
-/
theorem comparison_invertibility_triangulated :
    ∃ (_ : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ),
      (integralScalarExtensionOfUniverses l E L ι X).IsTriangulated := by
  obtain ⟨c, h⟩ := comparison_precomp_triangulated l E L ι X
  exact ⟨c, comparison_invertibility_triangulated_isTriangulated l E L ι X c h⟩
end WeilConjectures.IntegralFiniteExtension

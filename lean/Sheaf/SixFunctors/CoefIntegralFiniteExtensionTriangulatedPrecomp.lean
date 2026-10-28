module

public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore

/-! Precomposition reduction for finite-extension triangulation.
Source: current blueprint, lem-coef-integral-finite-extension.proof.md, paragraphs 1-5
(blueprint: lem-sf-integral-finite-extension-triangulated-precomp).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})

/-- The derived-quotient precomposition of strict finite-free scalar extension is
triangulated for each coherent shift. This is the chain-level Roos cone and
localization argument before descent from the derived quotient to the ambient
functor. Source: finite-free Roos total-limit triangulation and localization of the
K-flat representative functor. (blueprint: lem-sf-integral-finite-extension-triangulated-precomp)
-/
theorem comparison_precomp_triangulated
    (c : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ) :
    let _ := c
    (DerivedCategory.Qh ⋙ integralScalarExtensionOfUniverses l E L ι X).IsTriangulated := by
  sorry

end WeilConjectures.IntegralFiniteExtension

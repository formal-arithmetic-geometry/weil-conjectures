module
public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore
import Sheaf.SixFunctors.CoefIntegralFiniteExtensionTriangulatedPrecomp
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
/-- The strict finite-free scalar functor is triangulated for every coherent shift.
The proof expands the Roos cone of `1 - s` on flat-term K-flat representatives,
checks the signed shift and mapping-cone comparison, and descends these data through
the derived localization universal property.
Source: finite-free Roos total-limit triangulation and localization of the
K-flat representative functor. (blueprint: lem-sf-integral-finite-extension-triangulated)
-/
theorem comparison_invertibility_triangulated_isTriangulated
    (c : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ) :
    (integralScalarExtensionOfUniverses l E L ι X).IsTriangulated := by
  let T := integralScalarExtensionOfUniverses l E L ι X
  letI := c
  have hcomp : (DerivedCategory.Qh ⋙ T).IsTriangulated :=
    comparison_precomp_triangulated l E L ι X c
  letI := hcomp
  exact Functor.isTriangulated_of_precomp (DerivedCategory.Qh (C := _)) T

/-- The strict finite-free scalar functor admits a shift making it triangulated.
Source: finite-free Roos total-limit triangulation and localization of the
K-flat representative functor. (blueprint: lem-sf-integral-finite-extension-triangulated)
-/
theorem comparison_invertibility_triangulated :
    ∃ (_ : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ),
      (integralScalarExtensionOfUniverses l E L ι X).IsTriangulated := by
  obtain ⟨c⟩ := (integralScalarExtensionWellDefined l E L ι X).2.choose_spec.choose_spec.2.1
  exact ⟨c, comparison_invertibility_triangulated_isTriangulated l E L ι X c⟩
end WeilConjectures.IntegralFiniteExtension

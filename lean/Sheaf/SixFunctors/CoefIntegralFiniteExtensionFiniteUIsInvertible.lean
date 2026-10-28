module
public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore
/-! Invertibility of the finite counit comparison used by the integral extension map.
Source: current blueprint, lem-coef-integral-finite-extension.proof.md, paragraph 2.
(blueprint: lem-sf-integral-finite-extension-finite-u-is-invertible)
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
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
/-- The finite counit comparison is invertible at every normalized quotient level.

This is the finite-free counit calculation underlying the reduction proof: the
coefficient extension is finite free, and the exceptional dualizing counit mate
and its normalized realization are isomorphisms. Once this finite-level
calculation is available, the reduction equation for `u` is a composite of
isomorphisms.
(blueprint: lem-sf-integral-finite-extension-finite-u-is-invertible)
-/
theorem finiteU_isIso (n : ℕ) :
    IsIso (finiteU l E L ι X D n) := by
  sorry
end WeilConjectures.IntegralFiniteExtension

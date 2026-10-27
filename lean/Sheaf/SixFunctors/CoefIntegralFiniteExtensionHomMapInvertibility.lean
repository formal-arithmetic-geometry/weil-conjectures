module
public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore

/-! The finite-free evaluation transpose is invertible.
The statement isolates the middle factor in the completed comparison `v`.
Source: current blueprint, lem-coef-integral-finite-extension.proof.md, paragraph 5
(blueprint: lem-sf-integral-finite-extension-hom-map-invertibility).
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
  (a : IntegralHom.TensorPresentation.{u, u} X
    (completedIntegralCommRingSheafUnrestricted l E X))
  (b : IntegralHom.TensorPresentation.{u, u} X
    (completedIntegralCommRingSheafUnrestricted l L X))
  (K M : IntegralVerdier.Ambient l E X)
/-- The evaluation transpose is an isomorphism by the finite-free basis calculation.
Source: finite-free basis calculation for the scalar-extended evaluation transpose.
The inverse is obtained by expanding the target internal Hom in a finite basis of the
completed coefficient extension; the tensor-Hom identities show both composites are
identities. This argument is independent of completeness of `K` and `M` and of the
chosen normalized tensor presentations.
(blueprint: lem-sf-integral-finite-extension-hom-map-invertibility)
-/
theorem homMap_isIso :
    IsIso (homMap X (completedCoefficientMap l E L ι X) a b K M) := by
  sorry
end WeilConjectures.IntegralFiniteExtension

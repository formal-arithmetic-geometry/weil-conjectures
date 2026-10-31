/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionInvertibilityTriangulated
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionUInvertibility
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionVInvertibility

/-! # Canonical integral finite-extension comparisons
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-coef-integral-finite-extension).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
variable (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)
/-- Finite-free scalar extension is triangulated and its canonical dualizing and
internal-Hom maps are invertible.
(blueprint: lem-sf-integral-finite-extension-invertibility). -/
theorem comparison_invertibility
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X)) :
    (∃ (_ : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ),
      (integralScalarExtensionOfUniverses l E L ι X).IsTriangulated) ∧
    IsIso (u l E L ι X D hl wE wL) ∧
    (∀ K M : sfIntegralConstructibleCategory l E X,
      IsIso (v l E L ι X a b K.obj M.obj K.property.1 M.property.1)) := by
  refine ⟨comparison_invertibility_triangulated l E L ι X, ?_, ?_⟩
  · exact comparison_invertibility_u l E L ι X D hl wE wL
  · intro K M
    exact comparison_invertibility_v l E L ι X a b K.obj M.obj K.property.1 M.property.1
end WeilConjectures.IntegralFiniteExtension

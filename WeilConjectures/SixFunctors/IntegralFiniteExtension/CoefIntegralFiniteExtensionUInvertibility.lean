/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionUReductionIsInvertible
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionUReconstruction
/-! Auxiliary reduction for dualizing invertibility.
Source: current blueprint, lem-coef-integral-finite-extension.proof.md, paragraphs 2-3
(blueprint: lem-sf-integral-finite-extension-invertibility). -/
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
  (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)
/-- The canonical finite-extension dualizing comparison is invertible.
Source: finite-level counit invertibility, normalized DVR effectivity, and coherent
reduction comparison identify the total-limit map with `u`.
(blueprint: lem-sf-integral-finite-extension-u-invertibility)
-/
theorem comparison_invertibility_u :
    IsIso (u l E L ι X D hl wE wL) := by
  apply comparison_invertibility_u_of_reductions l E L ι X D hl wE wL
  exact comparison_reduction_isIso_u l E L ι X D hl wE wL
end WeilConjectures.IntegralFiniteExtension

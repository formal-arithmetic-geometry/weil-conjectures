/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SmoothPurity.PurStrictScalar.CompletedScalarExactLocalization

/-! # The universal-counit API for completed scalar comparison

(blueprint: lem-pur-completed-scalar-transport-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Completed scalar extension has the exact termwise derived model, normalized
by its computation counit on every complex.
Source: Stacks 06YY and the exact completed scalar model.
(blueprint: lem-pur-completed-scalar-transport-counit).
Proof: take completedTensorModel and its completedTensorModel_counit equation.
The preservation instances in that construction agree with those supplied here
by proof irrelevance. No choice of an unnormalized derived model is needed. -/
theorem derivedScalarTransport (W : Scheme.{u})
    [PreservesFiniteLimits (pbcExtend (completedCoefficientMap l E F i W))]
    [PreservesFiniteColimits (pbcExtend (completedCoefficientMap l E F i W))] :
    ∃ e : pbcDerivedExtend (completedCoefficientMap l E F i W) ≅
        (pbcExtend (completedCoefficientMap l E F i W)).mapDerivedCategory,
      ∀ P : CochainComplex (integralTowerModules l E W) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcExtend (completedCoefficientMap l E F i W)).mapDerivedCategoryFactors.hom.app P =
            pbcComplexCounit (completedCoefficientMap l E F i W) P := by
  exact ⟨PurStrictScalar.completedTensorModel l E F i W,
    PurStrictScalar.completedTensorModel_counit l E F i W⟩

end WeilConjectures.CompactSupportCondensedRealization

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-! # Exact model for integral scalar extension

 Finite freeness
identifies total derived tensor with the exact functor applied to complexes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (Y : Scheme.{u})

/-- The finite integral coefficient inclusion on the pro-etale site. -/
noncomputable abbrev integralConstructibleCoefficientMap :=
  coefficientMap (finiteCoefficientIntegersPointMap ℓ h) Y

/-- The exact tensor functor induces a functor on the unbounded derived categories. -/
noncomputable def integralOrdinaryDerivedScalar :=
  letI : PreservesFiniteLimits
      (Mod.extendScalars (integralConstructibleCoefficientMap ℓ h Y)) :=
    ((cartesianCoefficients_finiteFree ℓ h).2.2 Y).1
  (Mod.extendScalars (integralConstructibleCoefficientMap ℓ h Y)).mapDerivedCategory

/-- Exact tensor and total derived tensor are canonically isomorphic.

Proof: finite freeness gives exactness; apply uniqueness of total left derived functors. -/
noncomputable def integralScalarExactDerivedComparison :
    (Mod.extendScalars (integralConstructibleCoefficientMap ℓ h Y)).leftDerivedFunctor ≅
      integralOrdinaryDerivedScalar ℓ h Y := by
  letI : PreservesFiniteLimits
      (Mod.extendScalars (integralConstructibleCoefficientMap ℓ h Y)) :=
    ((cartesianCoefficients_finiteFree ℓ h).2.2 Y).1
  exact Functor.leftDerivedFunctorIsoMapDerivedCategory
    (Mod.extendScalars (integralConstructibleCoefficientMap ℓ h Y))

end AlgebraicGeometry.ProEtale

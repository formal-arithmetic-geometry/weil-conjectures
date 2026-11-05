/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations

/-! The naturality clause for the specified rational Hom comparison.
Source: blueprint common-stage paragraph (blueprint: lem-zl-specified-hom-scalar-evaluation).
This is the rationalized naturality calculation for arbitrary localized arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u

attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralDerivedInternalHom WeilConjectures.integralScalarExtension
  WeilConjectures.sfRationalScalarExtension
  WeilConjectures.scalarHomOrdinary

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules TensorProduct
namespace WeilConjectures

attribute [local irreducible] rationalDerivedInternalHom rationalHomScalarComparison
attribute [local implicit_reducible] rationalHomScalarPair

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

end WeilConjectures

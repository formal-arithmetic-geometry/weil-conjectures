/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteTypeIntegralHeartBound

/-! # The continuous and spectral integral coefficient presentations -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Continuous integral coefficients and spectral integral coefficients on ULift E
are isomorphic as condensed ring objects.

Source: the proved normed_point_iso in FiniteTypeIntegralHeartBound; current blueprint
sk-lem-finite, integral-to-rational coefficient convention.
(blueprint: lem-sf-finite-point-integral-coefficient-iso).

Proof in words. Uniqueness of the extension absolute value identifies the spectral norm
on ULift E with the given norm on E. The lift equivalence therefore identifies their
valuation rings and is an isometry on them. Postcomposition of continuous functions by
this equivalence and its inverse gives inverse continuous-function ring maps on each
profinite test space. They commute with restriction and preserve multiplication and one
pointwise. Forget to abelian sheaves to obtain the stated ring-object isomorphism.
This is precisely the already proved normed_point_iso, reused here. -/
theorem finite_point_integral_coefficient_iso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    Nonempty (Mon.mk (integralCoeff.{u} ℓ E) ≅
      Mon.mk (DerivedNakayama.integerRing ℓ (ULift.{u} E))) := by
  exact normed_point_iso.{u} ℓ E

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
public import WeilConjectures.SmoothPurity.Supporting.RationalizationKaroubi
public import WeilConjectures.SmoothPurity.AlgebraicallyClosedCoefficients.AlgebraicallyClosedCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.InvertibleTensorScalarExtensionDefinitionsSupplement
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLinePowerFlat
import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineDerivedScalarComparison
import WeilConjectures.AlgebraicGeometry.Completed.CompletedLineDerived
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLocallyFreeLineModels
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSingleSupport

import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.SmoothPurity.Supporting.FirstRootCoefficientScalarComparison
import WeilConjectures.SmoothPurity.Supporting.Scalar.OrdinaryScalarTensorLineTransport
import WeilConjectures.SmoothPurity.Scalar.ScalarSemilinearDualExt

/-! # Coefficient Tate twists

Source: blueprint `sec-smooth-purity/sk-def-sf-admissible/def-coefficient-twists-detailed.md`,
order 1505; current main-20261015 source: `sec-proetale-coefficients/sk-def-sp-tate-twist/`,
order 1864 (blueprint: def-coefficient-twists-detailed).

The intrinsic rational and common-stage functors are provided by
`WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted`;
this module supplies their shared signed lines and ordinary tensor/scalar comparison.

## Main definitions and statements

- `WeilConjectures.coefficientTateTwists`
- `WeilConjectures.coefficientTwistPower`
- `WeilConjectures.coefficientTwistLine`
- `WeilConjectures.coefficientTwistLine_exact`
- `WeilConjectures.IsCanonicalTwistScalarMaps`
- `WeilConjectures.twistSheafScalarComparison`

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

universe d u v c
set_option synthInstance.maxSize 2048

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted
attribute [-instance] integralOperationsCommHasDerivedCategory
attribute [-instance] scalarSiteSmall scalarSiteSheafify scalarSiteLocallyBijective

attribute [local instance 3000] integralTowerHasDerivedCategory

variable (X : Scheme.{u})

variable (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic ℓ) E]
  [FiniteDimensional (Padic ℓ) E] (S : Scheme.{u})
  [∀ x : S, Invertible (ℓ : S.residueField x)]

section ScalarComparison

variable (L : Type u) [Field L] [Algebra (Padic ℓ) L]
  [FiniteDimensional (Padic ℓ) L] (ι : E →ₐ[Padic ℓ] L)

end ScalarComparison

variable (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω]
  [IsAlgClosure (Padic ℓ) Ω]

end WeilConjectures

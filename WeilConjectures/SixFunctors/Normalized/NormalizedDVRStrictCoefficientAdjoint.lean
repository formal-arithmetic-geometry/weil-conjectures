/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRFlatCokernel
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.LinearScalarCone.LinearScalarCone
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeAdjoint
import all WeilConjectures.SmoothPurity.Integral.IntegralPrincipalConeQuotientAugmentation
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Normalized adjoints of strict DVR coefficient maps

Source: Stacks Tags 06YS, 06YY, 03EK and 05RT; blueprint DVR effectivity,
proof paragraphs 3--4. (blueprint: lem-coef-normalized-dvr-strict-coefficient-adjoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

end WeilConjectures

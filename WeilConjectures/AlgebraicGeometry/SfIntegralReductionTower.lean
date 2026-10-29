/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.IntegralReductionTowerUnrestricted

/-!
# Canonical reduction towers without a finite-field datum

Source: Bhatt--Scholze, Definition 3.5.2, p. 24; Stacks Tags 03EK and 06YY
(auxiliary; not a blueprint node).
The index n means the positive exponent n+1. All scalar extensions are the published
universal derived scalar extensions, with their specified K-flat comparisons.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{u})

local instance (priority := 4000) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{u} _

/-- The corresponding locally bijective criterion in the same coefficient size.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
noncomputable instance (priority := 3000) sfAbBijective (Y : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Y

attribute [local irreducible] sfReductionTransition

attribute [local irreducible] sfComparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] sfDerivedReductionTransition

attribute [local irreducible] sfReductionRepresentativeComparison sfDerivedReductionUnit
end WeilConjectures

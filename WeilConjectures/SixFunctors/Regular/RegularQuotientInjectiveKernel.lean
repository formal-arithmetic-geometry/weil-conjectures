/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Regular.RegularQuotientTraceData
public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularScalarInjectiveDivisibility
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import all WeilConjectures.AlgebraicGeometry.Adic.AdicReductionTriangle
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralScalarRegular

/-! # The actual ordinary quotient kernel and injective divisibility

Source: Stacks Tags 03D7, 06YP and 079P; the normalized right-exact tensor sequence and evaluation
of the ordinary coinduction adjunction.
(blueprint: lem-sf-regular-quotient-injective-kernel). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale SheafOfModules SheafOfModules.RegularQuotientCone
namespace WeilConjectures

attribute [-instance] PrincipalKoszulStrictReplacement.siteSmall
  PrincipalKoszulStrictReplacement.abSheafify PrincipalKoszulStrictReplacement.abLocallyBijective
  integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  scalarReductionSourceDerived scalarReductionTargetDerived
  GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard

private local instance (T : Scheme.{u}) : EssentiallySmall.{u+1} T.ProEt :=
  essentiallySmallSelf.{0,u,u+1} _
private local instance (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u,u} T
private local instance (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
  integralCoefficientAbLocallyBijective.{u,u} T
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)

end WeilConjectures

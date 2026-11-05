/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteQuotientEtaleOriginCore
import all WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteQuotientEtaleOriginCore
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import all WeilConjectures.AlgebraicGeometry.Adic.AdicLisseRelativeRestriction
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation

/-! # The comparison morphism for finite quotient origin transport

Source: Stacks Project, Tag 09C6.
(blueprint: lem-weil-pbc-lisse-finite-quotient-etale-origin-transport-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance] FiniteQuotientOriginProof.scalar_additive
  FiniteQuotientOriginProof.relative_additive FiniteQuotientOriginProof.scalar_equivalence
  FiniteQuotientOriginProof.relative_equivalence

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteStageNormalizedAdjunction
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteStageNormalizedChange
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteStageNormalizedCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin

/-! # Assembly of the finite-coefficient exceptional adjunction system

Source: current blueprint reduction-exceptional, Locality and Charts, and
field-extension towers (blueprint: lem-pur-finite-coefficient-adjoint-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints
attribute [local irreducible] etaleUpper etaleAdjunction
  projectionAtWitness refinementAtWitness ProEtale.pbcFixedScalarExtension
  ProEtale.pbcFixedScalarExtensionComp ProEtale.normalizedOriginScalarUnit
  ProEtale.compactSupportSiteComparison
  ProEtale.derivedComparisonAdjunction

end AlgebraicGeometry.FiniteCoefficientAdjoints

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientOperationEncoding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperExchange
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperExchange
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientPullbackEncoding
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange

/-! # Finite coefficient encoding of the canonical exchange mate

This is the change of presentation of the exchange arrow. It requires neither
properness nor boundedness, and asserts no invertibility of the exchange.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

attribute [local irreducible] coefficientEncoding Encoding.fixedDerived Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  CondensedRing.upperStar CondensedRing.lowerStar ProEtale.upperStar ProEtale.lowerStar
  CondensedRing.derivedUpperStarLowerStarAdjunction ProEtale.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarComp ProEtale.leftDerivedUpperStarComp
  ProEtale.derivedBaseChangeMap

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
variable {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R]

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-!
# Canonical open-square exchange on the small pro-etale site

Source: Weil blueprint, trace formula, order 2367; Stacks Project, Tags 03S6 and 04J0
(blueprint: lem-trf-open-square-exchange).

All functors act on the published intrinsic constant-ring module categories.
The comparison is fixed as the inverse of the open-adjunction mate; the data below
include restriction normalization, both identity laws and both pasting laws.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

-- Use the equivalence API without expanding the concrete realization equivalence.
attribute [local irreducible] sfIntrinsicModuleEquivalence

-- First prove transport and mate coherence with abstract categories.
section TransportCalculus

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
  [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃]

variable {C₄ D₄ : Type*} [Category C₄] [Category D₄]

variable {C₅ C₆ D₅ D₆ : Type*} [Category C₅] [Category C₆]
  [Category D₅] [Category D₆]

end TransportCalculus

-- Check exact descent on the homotopy-category localization.
section ExactLocalizationCalculus

variable {C₁ C₂ D₁ D₂ : Type*}
  [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  [Abelian C₁] [Abelian C₂] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₁] [HasDerivedCategory D₂]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end ExactLocalizationCalculus

-- Apply the existing exact-square pasting theorems in both orientations.
section DerivedPasting

variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  (F₀₁ : C₀ ⥤ C₁) (F₁₂ : C₁ ⥤ C₂) (F₀₂ : C₀ ⥤ C₂)
  (G₀₁ : D₀ ⥤ D₁) (G₁₂ : D₁ ⥤ D₂) (G₀₂ : D₀ ⥤ D₂)
  (U₀ : C₀ ⥤ D₀) (U₁ : C₁ ⥤ D₁) (U₂ : C₂ ⥤ D₂)
  [F₀₁.Additive] [F₁₂.Additive] [F₀₂.Additive]
  [G₀₁.Additive] [G₁₂.Additive] [G₀₂.Additive]
  [U₀.Additive] [U₁.Additive] [U₂.Additive]
  [PreservesFiniteLimits F₀₁] [PreservesFiniteColimits F₀₁]
  [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
  [PreservesFiniteLimits F₀₂] [PreservesFiniteColimits F₀₂]
  [PreservesFiniteLimits G₀₁] [PreservesFiniteColimits G₀₁]
  [PreservesFiniteLimits G₁₂] [PreservesFiniteColimits G₁₂]
  [PreservesFiniteLimits G₀₂] [PreservesFiniteColimits G₀₂]
  [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end DerivedPasting

attribute [local irreducible] sfIntrinsicOpenMate sfIntrinsicOpenAdjunction
  sfIntrinsicPullback sfIntrinsicExtensionByZero sfIntrinsicSquarePullback
  sfIntrinsicPullbackComp sfIntrinsicPullbackId sfIntrinsicOpenComp sfIntrinsicOpenId

attribute [local semireducible] sfIntrinsicOpenId

attribute [local irreducible] sfIntrinsicOpenId

attribute [local irreducible] sfMateIso sfExchange sfIntrinsicDerivedOpenMate
  sfIntrinsicDerivedOpenUnit sfIntrinsicDerivedSquarePullback
  sfIntrinsicDerivedPullbackComp sfIntrinsicDerivedOpenComp
  sfIntrinsicDerivedPullbackId sfIntrinsicDerivedOpenId

end AlgebraicGeometry.Scheme

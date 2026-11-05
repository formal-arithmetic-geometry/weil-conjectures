/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientOperationEncoding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientHeartPullbackComposition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Derived.DerivedExactCube

/-! # Composition-compatible coefficient encoding of inverse images

This is the inverse-image part of normalized coefficient transport. It involves
neither direct images nor exchange morphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

open CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  {U₀ : C₀ ⥤ C₂} {U₁ : C₀ ⥤ C₁} {U₂ : C₁ ⥤ C₂}
  {V₀ : D₀ ⥤ D₂} {V₁ : D₀ ⥤ D₁} {V₂ : D₁ ⥤ D₂}
  {F₀ F₀' : C₀ ⥤ D₀} {F₁ F₁' : C₁ ⥤ D₁} {F₂ F₂' : C₂ ⥤ D₂}

variable {U₀' : C₀ ⥤ C₂} {U₁' : C₀ ⥤ C₁} {U₂' : C₁ ⥤ C₂}
  {V₀' : D₀ ⥤ D₂} {V₁' : D₀ ⥤ D₁} {V₂' : D₁ ⥤ D₂}

end

section
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  (U₀ : C₀ ⥤ C₂) (U₁ : C₀ ⥤ C₁) (U₂ : C₁ ⥤ C₂)
  (V₀ : D₀ ⥤ D₂) (V₁ : D₀ ⥤ D₁) (V₂ : D₁ ⥤ D₂)
  (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
  [U₀.Additive] [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [U₁.Additive] [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [U₂.Additive] [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [V₀.Additive] [PreservesFiniteLimits V₀] [PreservesFiniteColimits V₀]
  [V₁.Additive] [PreservesFiniteLimits V₁] [PreservesFiniteColimits V₁]
  [V₂.Additive] [PreservesFiniteLimits V₂] [PreservesFiniteColimits V₂]
  [F₀.Additive] [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]

attribute [local implicit_reducible] Functor.mapHomologicalComplex

end

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

-- Retain the original finite-discrete interface, although the normalized encoding suffices.

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback

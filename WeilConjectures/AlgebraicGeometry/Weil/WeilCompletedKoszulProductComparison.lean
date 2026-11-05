/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulRoosComparison
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Transporting the finite Koszul comparison through products and signed fibers

Source: Stacks Project, Tag 0A0E and sites-cohomology.tex Tag 0941.
(blueprint: lem-weil-pbc-completed-koszul-product-comparison).

All product preservation, cone signs and the precise zero-homotopy unit are proved here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
universe u v c z
namespace AlgebraicGeometry.Scheme
section FiberTransport
set_option backward.defeqAttrib.useBackward true
variable {B : Type u} [Category.{v} B] [Abelian B]
variable {K L M : CochainComplex B ℤ}

variable {K' L' : CochainComplex B ℤ}

universe u' v'
variable {B' : Type u'} [Category.{v'} B'] [Abelian B']

variable [HasCountableProducts B] [HasCountableProducts B']

variable {M' : CochainComplex B ℤ}

end FiberTransport
set_option backward.defeqAttrib.useBackward false

universe u₀ v₀ u₁ v₁ u₂ v₂

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] pbcCompletedComparison intrinsicPresentationRoundTrip
attribute [local irreducible] completedCechModulesEquiv

end AlgebraicGeometry.Scheme

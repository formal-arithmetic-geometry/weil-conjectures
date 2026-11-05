/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.CondensedActionModule
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarResolution
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Condensed.Equivalence
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-! # Internal profinite actions and compatible bar models

Source: the formal internal-bar expansion of paragraph (3) of the main-20261015
six-functors direct-image proof (blueprint: def-sfb-condensed-equivariant-bar-data).
The action is on all continuous generalized elements and is compatible with restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.CondensedBar

variable (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {A G}

attribute [instance] Profinite.CondensedAction.Invariants.additive

attribute [instance] InternalFunctions.additive

attribute [instance] ScalarAction.additive

section Derived
variable [ActionAbelian A G] [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Modules A)]

end Derived

section Scalar
variable {A A' : Ring.{u}} (a : A ⟶ A')
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [ActionAbelian A G] [ActionAbelian A' G]
  [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [IsGrothendieckAbelian.{u + 1} (Equivariant A' G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A' G)]
  [HasDerivedCategory.{u + 2} (Modules A)] [HasDerivedCategory.{u + 2} (Modules A')]

end Scalar

end CategoryTheory.CondensedBar

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import
  WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Counits in an exact square of derived adjunctions

Source: Stacks Project, Derived Categories, Tags 09T5 and 070Y; exact-square extraction
of tower normalization, steps 6--8 (blueprint: lem-weil-pbc-exact-square-derived-counit).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA uAp uB uBp vA vAp vB vBp wA wAp wB wBp

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type uA} {Ap : Type uAp} {B : Type uB} {Bp : Type uBp}
  [Category.{vA} A] [Category.{vAp} Ap] [Category.{vB} B] [Category.{vBp} Bp]
  [Abelian A] [Abelian Ap] [Abelian B] [Abelian Bp]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wAp} Ap]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wBp} Bp]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

-- Adjoining a contractible summand makes a resolution monomorphic without changing
-- its homotopy type. No degreewise injectivity or enough-injectives assumption is used.

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end CategoryTheory

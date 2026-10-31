/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-!
# Ring and module inverse images at a topos point

Source: Stacks Project, Sites, Proposition 00YV; Modules on Sites, Section 03D2;
Cohomology on Sites, Tag 0DEN (blueprint: def-sfb-ringed-site-point).

The operation graphs are tested on every sheaf T, including the products of operand
sheaves. They specify the finite-product transport, rather than an arbitrary lift.
No object is selected from an existence theorem: all data remain explicit in the
presentation, and the criterion will hold for every such presentation.
-/

@[expose] public section
set_option autoImplicit false

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

attribute [instance] RingedSitePoint.modules_additive

namespace PointTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open MonoidalCategory CartesianMonoidalCategory
open Functor.LaxMonoidal

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}

private noncomputable abbrev base (R : Sheaf J CommRingCat.{w}) :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R

variable (F : Sheaf J (Type w) ⥤ Type w)

omit [EssentiallySmall.{w} C] in
omit [EssentiallySmall.{w} C] in
omit [EssentiallySmall.{w} C] in
omit [EssentiallySmall.{w} C] in
omit [EssentiallySmall.{w} C] in
variable {F}

omit [EssentiallySmall.{w} C] in
end PointTransport

open PointTransport

end CategoryTheory

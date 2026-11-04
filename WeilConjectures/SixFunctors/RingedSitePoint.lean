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
public import WeilConjectures.CategoryTheory.Sites.RingedSitePoint

/-!
# Ring and module inverse images at a topos point

Source: Stacks Project, Sites, Proposition 00YV; Modules on Sites, Section 03D2;
Cohomology on Sites, Tag 0DEN (blueprint: def-sfb-ringed-site-point).

The operation graphs are tested on every sheaf T, including the products of operand
sheaves. They specify the finite-product transport, rather than an arbitrary lift.
No object is selected from an existence theorem: all data remain explicit in the
presentation, and the criterion will hold for every such presentation.
-/

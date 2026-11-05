/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.AlgebraicGeometry.DerivedNormalizationArrows

/-! # Universal arrows for derived coefficient normalization

Source: Stacks Project, Tags 06YY, 07A6 and 06Y5, derived extension and its adjunction
(blueprint: def-weil-pbc-derived-normalization-arrows).

A normalization isomorphism can equivalently be supplied by its universal arrow to
restriction of scalars. This encoding retains its specific arrow, and avoids choosing
an additional model of the total derived tensor functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R S : Type (u + 1)} [CommRing R] [CommRing S]

section Pullback

variable {D : Type (u + 1)} [Category.{u} D] [EssentiallySmall.{u + 1} D]
  (F : C ⥤ D) (K : GrothendieckTopology D) [F.IsContinuous J K]

-- Keep the existing essentially-small instance binders in the public signature.

end Pullback

end CategoryTheory

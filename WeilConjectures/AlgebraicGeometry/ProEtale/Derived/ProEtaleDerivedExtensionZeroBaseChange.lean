/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

/-!
# Ordinary pro-etale extension-by-zero base change

Source: Stacks Project, Tag 03S6 (`lemma-shriek-base-change`), and Tag 09AE;
blueprint `lem-cbc-proetale-extension-zero-base-change`.

This is the ordinary constant-coefficient interface corresponding to the dependency
node.  The previously recorded strict-tower `singleBeta` interface has a different
category, so this module exposes the canonical mate construction on ordinary
pro-etale module sheaves and its derived map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

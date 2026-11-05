/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.SiteExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact

/-!
# Extension by zero and restriction on a localized site

Source: literature/stacks-project/sites-modules.tex, Modules on Sites, Section 03DH
and Lemmas 03DI--03DJ (blueprint: lem-weil-pbc-site-restriction-injectives).
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

end CategoryTheory

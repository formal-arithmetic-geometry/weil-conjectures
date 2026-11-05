/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Slice-site localization for ringed sheaves

Source: Stacks Project, sites.tex, Tags 0791 and 04J4, and sites-modules.tex,
Tag 04IE (blueprint: lem-weil-pbc-ringed-sheaf-slice-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits DirectSum Opposite

namespace CategoryTheory

end CategoryTheory
end

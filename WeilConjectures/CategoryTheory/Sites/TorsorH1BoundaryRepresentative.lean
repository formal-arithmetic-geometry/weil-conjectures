/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import WeilConjectures.CategoryTheory.Sites.ZariskiTorsorRepresentativeExists

/-!
# Torsor classes as boundaries of the representative extension

Source: literature/stacks-project/cohomology.tex, Lemma 02FQ
(cohomology-lemma-torsors-h1), construction of the extension and its boundary of one
(blueprint: lem-sc-torsor-h1-boundary-representative).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace CategoryTheory.Sheaf

end CategoryTheory.Sheaf

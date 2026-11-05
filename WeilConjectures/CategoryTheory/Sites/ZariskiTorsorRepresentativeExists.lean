/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.CategoryTheory.Sites.ZariskiTorsorFreeExtension

/-!
# A representative extension of a Zariski torsor

Source: Stacks Project, Cohomology of Sheaves, Lemma 02FQ, first construction.
(blueprint: lem-sc-zariski-torsor-representative-exists)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace CategoryTheory.Sheaf

end CategoryTheory.Sheaf

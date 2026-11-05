/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Sheafification of cohomology over open subsets

Source: Stacks Project, Cohomology, Lemma 20.32.3, Tag 0BKJ
(blueprint: lem-pc-ringed-space-sheafification-cohomology).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

noncomputable section

-- Resolved section cohomology inverts quasi-isomorphisms via the homotopy category.

-- Exact abelian sheafification commutes with homology; its counit recovers a sheaf.

end

end AlgebraicGeometry.RingedSpace

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.Topology.OpenModuleDerivedSections
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Detecting zero direct-image cohomology on the affine basis

Source: Stacks Project, Tag 08D5, proof of (2); Tag 079V, K-injective computation.
(blueprint: lem-pc-direct-image-homology-affine-detection).
-/

@[expose] public section

universe u wX wS wAb

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

end AlgebraicGeometry

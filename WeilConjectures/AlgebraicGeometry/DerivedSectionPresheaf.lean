/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-! # The unbounded derived section cohomology presheaf

Source: Stacks Project, Cohomology, Tag 0D5X
(blueprint: def-pc-derived-section-presheaf).

Resolve on the source, then take direct image as a presheaf of modules and its
cohomology. Evaluation on an open is exact in the presheaf category, so this is
precisely the presheaf of cohomology of derived sections, including its restriction
maps and its module structure. It does not take cohomology in the sheaf category.
-/

@[expose] public section

universe a b

open CategoryTheory

namespace AlgebraicGeometry

end AlgebraicGeometry

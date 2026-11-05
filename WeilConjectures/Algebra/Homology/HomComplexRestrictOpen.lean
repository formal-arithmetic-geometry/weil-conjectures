/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Algebra.Homology.HomComplexRestrictOpenDifferential
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Hom complexes commute with open restriction

Source: Stacks Project, Cohomology, Tag 08DL, construction of internal Hom;
Cohomology on Sites, Section 0A8X.
(blueprint: lem-sc-hom-complex-restrict-open).
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace CategoryTheory

end CategoryTheory

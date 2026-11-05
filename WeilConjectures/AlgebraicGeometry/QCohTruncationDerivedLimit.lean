/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.TruncationDerivedLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedFunctorDerivedLimit

/-! # Reconstruction of quasi-coherent complexes by lower truncations

Source: Stacks Project, Tags 08D3, 08D4 and 08U1
(blueprint: lem-pc-qcoh-truncation-derived-limit).

Both conclusions use specified Roos triangles: the map to the product is fixed to be
induced by the canonical truncation projections. Products are in the ambient derived
categories, rather than in the full subcategory of quasi-coherent complexes.
-/

@[expose] public section

universe u w w'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

import WeilConjectures.AlgebraicGeometry.AffineBasisLowerTailSectionsReconstruction
import WeilConjectures.AlgebraicGeometry.AffineBasisLowerTailSectionsStep
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import WeilConjectures.CategoryTheory.DerivedLimitEventuallyIso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

/-! # Derived sections vanish above a lower tail with basis-acyclic homology

Source: Stacks Project, Tag 0BKT (cohomology-over-U-trivial), applied to the
strictly lower tail; Tags 071B and 0D64 for its tower reconstruction.
(blueprint: lem-sc-affine-basis-derived-sections-lower-tail-vanishing).
-/

@[expose] public section

universe u wC wD
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

end AlgebraicGeometry

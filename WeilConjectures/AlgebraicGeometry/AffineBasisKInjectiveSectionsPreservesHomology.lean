/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

import WeilConjectures.AlgebraicGeometry.DerivedLowerTruncationCycleFormula
import WeilConjectures.CategoryTheory.LeftExactUpperTruncationComparison
import WeilConjectures.AlgebraicGeometry.AffineBasisDerivedSectionsLowerTailVanishing
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # K-injective section homology from affine-basis acyclicity

Source: Stacks Project, Tag 08C2, singleton cover; Tag 071B, compatible resolution tower.
(blueprint: lem-sc-affine-basis-kinjective-sections-preserves-homology).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

end AlgebraicGeometry

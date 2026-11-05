/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Local truncation comparison for unbounded direct image

Source: Stacks Project, perfect.tex, Tag 08D5, final paragraph
(blueprint: lem-pc-derived-direct-image-affine-truncation-comparison).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

-- The site equivalence transports quasi-coherent presentations; compare the proved helper
-- in Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian.

end AlgebraicGeometry

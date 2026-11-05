/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSplitTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Naturality component for the shifted K-injective comparison

Source: Stacks Project, Tag 079V.
(blueprint: lem-pc-direct-image-kinjective-comparison-shift-aux)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 8

noncomputable section
namespace AlgebraicGeometry.RingedSpace

-- Every homotopy-category object maps to a K-injective by a quasi-isomorphism.

-- Associators align the shift structures on the intermediate composite functors.

end AlgebraicGeometry.RingedSpace

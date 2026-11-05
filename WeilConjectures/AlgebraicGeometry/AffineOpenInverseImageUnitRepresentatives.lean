/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import WeilConjectures.AlgebraicGeometry.AffineOpenInverseImageFiniteLocalLifts
import WeilConjectures.AlgebraicGeometry.AffineOpenInverseImageCompatibleRefinement
import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Unit representatives of inverse-image sections -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace


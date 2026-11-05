/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.AlgebraicGeometry.EtaleFiniteCoverFactorizationDescent

/-! # Descent of a representing etale cover in an affine open system

Source: Stacks Project, Tags 0EYL and 03Q6, finite objects, maps and cover descent.
(blueprint: lem-weil-pbc-affine-open-representing-cover-descent). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


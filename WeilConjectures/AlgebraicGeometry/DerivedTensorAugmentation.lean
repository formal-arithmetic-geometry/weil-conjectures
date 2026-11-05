/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal

/-! # Derived tensor augmentations on schemes

Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YU; Derived Categories
of Schemes, Tag 08EH (blueprint: def-sc-derived-tensor-augmentation).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Pseudo-coherent complexes on schemes

Source: Stacks Project, Cohomology of Sheaves, Tag 08CB, and Derived Categories of Schemes,
Tags 08E5 and 08E7 (blueprint: def-pur-pseudo-coherent-complex).

We use the scheme-local characterization by bounded-above complexes of finite free modules.
Restriction is to the localized site of an open, using the same module category and derived
category as `schemeDerivedCategory`.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme

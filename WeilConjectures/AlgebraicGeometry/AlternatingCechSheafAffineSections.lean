/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex

/-! # Global sections of the increasing-tuple sheaf complex

Source: Stacks Project, Tag 01FM, signed faces and intersection sections.
(blueprint: lem-pc-s3-alternating-cech-sheaf-affine-sections).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

open Opposite Limits TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section

end

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Underived models for the open counit computation

Source: Stacks Project, Cohomology, Tags 08FE and 08BV.
(blueprint: def-pc-derived-mayer-vietoris-open-counit-model).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

end AlgebraicGeometry

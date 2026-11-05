/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.AlgebraicGeometry.RelativeMVConePresentation
import WeilConjectures.CategoryTheory.DerivedCategory.ConeDiagramSESPresentation

/-! # Chain-level relative Mayer--Vietoris presentation

Source: Stacks Project, Cohomology, Tags 08BV, 08HY and 08HZ.
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProperBaseChange.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.DeligneLaumon.ImmersiveSystemSourceLocalFractions
import WeilConjectures.AlgebraicGeometry.ClosedPointResidueField

/-! # First jets of an immersive linear system at the source

Source: the finite-cover Bertini proof, paragraph 3; Stacks Tags 01NE and 01NF.
(blueprint: lem-zl-immersive-system-source-first-jets).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

end AlgebraicGeometry

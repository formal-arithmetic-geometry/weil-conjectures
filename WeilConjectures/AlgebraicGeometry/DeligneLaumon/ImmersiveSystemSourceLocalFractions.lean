/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProperBaseChange.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.MvPolynomial.CommRing
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProperBaseChange.ProjectiveSpaceHomOfGeneratingSections
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartSections
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-! # Local fractions in the ratios of an immersive generating system

Source: the finite-cover Bertini proof, paragraph 3; Stacks Tags 01NE and 01NF.
(blueprint: lem-zl-immersive-system-source-local-fractions).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

open Scheme.Modules ProjectiveSpace in
end AlgebraicGeometry

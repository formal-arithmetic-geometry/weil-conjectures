/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProperBaseChange.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.RingTheory.Ideal.Cotangent
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.DeligneLaumon.ImmersiveSystemSourceFirstJets
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
import WeilConjectures.PointCount
import Mathlib.LinearAlgebra.Dimension.Finite
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-! # Independent first jets from an immersive linear system

Source: the finite-cover Bertini proof, paragraph 3, and Stacks Tags 01NE, 01NF, 0B2G.
(blueprint: lem-zl-immersive-system-local-cotangent-pair).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

set_option linter.unusedVariables false in
end AlgebraicGeometry

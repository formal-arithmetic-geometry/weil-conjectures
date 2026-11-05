/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
public import WeilConjectures.Algebra.Homology.NormalizedHomComplexGlobalCochains
import WeilConjectures.Algebra.Homology.HomTensorDifferential

/-! # Normalized tensor-Hom comparison on ordinary cochains

Source: Stacks Project, Cohomology on Sites, Tags 0A90 and 0A8Z.
(blueprint: lem-pc-normalized-tensor-hom-cochains).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CochainComplex.HomComplex
namespace AlgebraicGeometry

end AlgebraicGeometry

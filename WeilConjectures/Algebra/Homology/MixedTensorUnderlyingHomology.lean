/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-! # Underlying additive homology of mixed total tensors

Source: Stacks Project, Tag 06Y6, the ordinary balanced tensor identifications.
(blueprint: new-lem-pc-mixed-tensor-underlying-homology).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace RingTensorCohomology

open MonoidalCategory
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end RingTensorCohomology

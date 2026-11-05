/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # Universal scalar extension computed by a fixed second-factor resolution

Source: Stacks Project, Tags 064L and 06Y6.
(blueprint: new-lem-pc-universal-balanced-tensor-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace RingTensorCohomology

end RingTensorCohomology

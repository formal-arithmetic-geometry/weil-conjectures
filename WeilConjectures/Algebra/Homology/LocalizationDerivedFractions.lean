/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.Algebra.Homology.BaseTensorUnitCohomologyModel

/-! # Fractions before transport to tensor cohomology models

Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-localization-derived-fractions).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace RingTensorCohomology

end RingTensorCohomology

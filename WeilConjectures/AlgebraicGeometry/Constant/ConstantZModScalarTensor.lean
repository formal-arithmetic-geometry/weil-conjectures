/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistLocallyFree
public import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # Absolute tensor and scalar extension from a constant cyclic ring

Source: the finite-level tensor comparison in the Tate-twist construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme

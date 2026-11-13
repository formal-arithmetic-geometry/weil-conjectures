/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Stalk

/-! # Compatibility of canonical stalk maps with nested open inclusions
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Opens

/-- Canonical maps from the ambient stalk spectrum commute with nested inclusions. -/
theorem fromSpecStalkOfMem_homOfLE {Y : Scheme.{u}}
    (y : Y) (V : Y.Opens) (hyV : y ∈ V) (U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U) :
    U.fromSpecStalkOfMem y hyU ≫ Y.homOfLE hUV = V.fromSpecStalkOfMem y hyV := by
  apply (cancel_mono V.ι).1
  simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]

end AlgebraicGeometry.Scheme.Opens

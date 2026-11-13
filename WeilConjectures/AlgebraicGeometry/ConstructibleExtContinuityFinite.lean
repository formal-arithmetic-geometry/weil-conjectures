/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantModelExtContinuity
/-! Finite-coefficient arbitrary-scheme Ext continuity.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
theorem continuousMap_ext_continuity
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    [MonObj (Profinite.continuousMapRingObj E)]
    [IsCommMonObj (Profinite.continuousMapRingObj E)]
    (X : Scheme.{u}) :
    ConstantModelExtContinuity (Profinite.continuousMapRingObj E) X := by
  sorry
end AlgebraicGeometry.ProEtale

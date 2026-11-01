/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarExact

/-! # Exactness of copower scalar extension at a geometric point -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Scalar extension preserves finite-colimit. The copower adjunction and split vector-space
sequences give the finite-colimit conclusion (blueprint: lem-a1-condensed-point-scalar-colimits). -/
theorem condensed_point_scalar_colimits :
    PreservesFiniteColimits (condensedPointScalarExtension ℓ k) := by
  have : (condensedPointScalarExtension ℓ k).IsLeftAdjoint :=
    (condensedPointScalarAdjunction ℓ k).isLeftAdjoint
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing

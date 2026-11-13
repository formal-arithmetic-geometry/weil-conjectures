/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.SmoothPurity.SeparablyClosedTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SixFunctors.EllCohomologicalDimensionComparison
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldFiniteTorsionCohomologicalDimension

/-!
# Cohomological dimension of the base field

Source: Stacks Project, Tags 03QQ and 010T. The dimension and its local prime-power torsion
convention are those of `cohomologicalDimension`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.ProEtale

open CategoryTheory

/-- The `ℓ`-cohomological dimension of an algebraically closed field is zero, and
that of a finite field is at most one. There is no restriction on the characteristic.

Source: Stacks Project, Tags 03QQ and 010T. -/
theorem cohomologicalDimension_baseField (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (K : Type u) [Field K] :
    (IsAlgClosed K → cohomologicalDimension ℓ hℓ (Spec (.of K)) = 0) ∧
      (Finite K → cohomologicalDimension ℓ hℓ (Spec (.of K)) ≤ 1)  := by
  constructor
  · intro hK
    have hsep : IsSepClosed K := inferInstance
    have htor :=
      AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed K
    have hcmp := (ellCohomologicalDimension_etale_comparison ℓ hℓ
      (Spec (.of K)) (X := Spec (.of K)) (Y := Spec (.of K)) (𝟙 _) 0).2.2.2 htor
    exact le_antisymm hcmp bot_le
  · intro hK
    have htor :=
      AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_one_of_finite_baseField K
    let g : Spec (.of K) ⟶ Spec (.of K) := 𝟙 _
    exact (ellCohomologicalDimension_etale_comparison ℓ hℓ
      (Spec (.of K)) (X := Spec (.of K)) (Y := Spec (.of K)) g 1).2.2.2 htor

end AlgebraicGeometry.ProEtale

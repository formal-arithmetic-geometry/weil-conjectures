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

The `ℓ`-cohomological dimension of an algebraically closed field is zero and that of a finite
field is at most one. The dimension and its local
prime-power torsion convention are those of `cohomologicalDimension`.

## References

* Stacks Project, Tags 03QQ and 010T
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.ProEtale

open CategoryTheory

/-- The `ℓ`-cohomological dimension of an algebraically closed field is zero, and
that of a finite field is at most one. There is no restriction on the characteristic.
-/
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

/-- A finite or algebraically closed field has finite `ℓ`-cohomological dimension: it is `0`
in the algebraically closed case and at most `1` in the finite case
(`AlgebraicGeometry.ProEtale.cohomologicalDimension_baseField`). -/
theorem cohomologicalDimension_baseField_lt_top (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (K : Type u) [Field K] (hK : Finite K ∨ IsAlgClosed K) :
    cohomologicalDimension ℓ hℓ (Spec (.of K)) < ⊤ := by
  rcases hK with hK | hK
  · exact lt_of_le_of_lt ((cohomologicalDimension_baseField ℓ hℓ K).2 hK) WithTop.one_lt_top
  · rw [(cohomologicalDimension_baseField ℓ hℓ K).1 hK]
    exact WithTop.coe_lt_top (0 : ℕ)

/-- Over a finite or algebraically closed field `K`, a finite-type morphism `g : X ⟶ Y` of
finite-type `K`-schemes has finite relative `ℓ`-cohomological dimension `cd_ℓ(g) < ∞`: the
base field has finite `ℓ`-cohomological dimension
(`AlgebraicGeometry.ProEtale.cohomologicalDimension_baseField`), so the relative finiteness
theorem for finite-type morphisms over a field of finite cohomological dimension
(`AlgebraicGeometry.ProEtale.relativeCohomologicalDimension_lt_top_of_finiteType`) applies. -/
theorem relativeCohomologicalDimension_lt_top_of_finiteType_of_baseField
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) {K : Type u} [Field K] (hK : Finite K ∨ IsAlgClosed K)
    {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of K))]
    [LocallyOfFiniteType g] [QuasiCompact g] :
    @relativeCohomologicalDimension ℓ hℓ X Y g inferInstance
      (@QuasiSeparated.of_quasiSeparatedSpace X Y g
        (@IsLocallyNoetherian.quasiSeparatedSpace X
          (LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))))) < ⊤ :=
  relativeCohomologicalDimension_lt_top_of_finiteType ℓ hℓ
    (cohomologicalDimension_baseField_lt_top ℓ hℓ K hK) g

end AlgebraicGeometry.ProEtale

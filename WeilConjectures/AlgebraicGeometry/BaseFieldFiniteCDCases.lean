/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import all WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SmoothPurity.SeparablyClosedTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SixFunctors.EllCohomologicalDimensionComparison

/-! # The two permitted base-field finiteness inputs

Source: current blueprint `sk-lem-base-field-cd` and its separably closed torsion
argument; expert field scope Houyi DM #1449.
(blueprint: lem-route-base-field-cd-lt-top-gap).

The finite case is the imported `BaseFieldFiniteCD.of_finite`. The separably closed
case below uses the same zero-dimensional comparison as the first branch of
`cohomologicalDimension_baseField`, with precisely the hypothesis that branch needs.
Neither case is a new typeclass, a Fact wrapper, or a claim about arbitrary fields.
-/

@[expose] public section
set_option autoImplicit false

universe u

namespace AlgebraicGeometry.ProEtale

open CategoryTheory

/-- A separably closed field has zero ell-cohomological dimension.

Source: `sk-lem-base-field-cd`, trivial-Galois-group argument;
`lem-sf-separably-closed-torsion-cd` and `det-cd-etale-comparison`.
(blueprint: lem-route-base-field-cd-lt-top-gap)

Proof: positive torsion etale cohomology vanishes over a separably closed field.
The etale/pro-etale comparison bounds the dimension by zero; nonnegativity gives equality.
The proof is also valid in characteristic ell and on the empty cohomology groups. -/
theorem cohomologicalDimension_baseField_of_isSepClosed
    (ℓ : ℕ) (hℓ : ℓ.Prime) (K : Type u) [Field K] [IsSepClosed K] :
    cohomologicalDimension ℓ hℓ (Spec (.of K)) = 0 := by
  have htor := Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed K
  have hcmp := (ellCohomologicalDimension_etale_comparison ℓ hℓ
    (Spec (.of K)) (X := Spec (.of K)) (Y := Spec (.of K)) (𝟙 _) 0).2.2.2 htor
  exact le_antisymm hcmp bot_le

/-- A separably closed field has finite cohomological dimension.

Source: current blueprint `sk-lem-base-field-cd`, separably closed argument in its proof;
expert field scope Houyi DM #1449 (blueprint: lem-route-base-field-cd-lt-top-gap).

Proof: use the separably closed numerical dimension lemma, then `0 < top`.
No characteristic restriction is needed for this numerical assertion. -/
theorem BaseFieldFiniteCD.of_isSepClosed (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [IsSepClosed k] : BaseFieldFiniteCD ℓ k := by
  unfold BaseFieldFiniteCD
  rw [cohomologicalDimension_baseField_of_isSepClosed ℓ Fact.out k]
  exact WithTop.coe_lt_top 0

end AlgebraicGeometry.ProEtale

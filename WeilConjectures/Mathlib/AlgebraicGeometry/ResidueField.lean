/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Global functions on `Spec κ(x)`

The canonical morphism `Spec κ(x) ⟶ X` of `AlgebraicGeometry.Scheme.fromSpecResidueField` acts
on global functions by evaluation at `x`, once `Γ(Spec κ(x), 𝒪)` is identified with `κ(x)`.

## Main results

- `AlgebraicGeometry.Scheme.fromSpecResidueField_appTop`: the map on global functions induced by
  `Spec κ(x) ⟶ X` is the evaluation `AlgebraicGeometry.Scheme.Γevaluation` at `x`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- **The morphism `Spec κ(x) ⟶ X` is evaluation at `x` on global functions.** Composed with
the identification `Γ(Spec κ(x), 𝒪) ≅ κ(x)`, the map on global functions induced by
`X.fromSpecResidueField x` is `X.Γevaluation x`. -/
lemma fromSpecResidueField_appTop (X : Scheme.{u}) (x : X) :
    (X.fromSpecResidueField x).appTop ≫ (ΓSpecIso (X.residueField x)).hom = X.Γevaluation x := by
  rw [fromSpecResidueField, Hom.comp_appTop, fromSpecStalk_appTop]
  simp [Γevaluation, evaluation, ← ΓSpecIso_inv_naturality]

end AlgebraicGeometry.Scheme

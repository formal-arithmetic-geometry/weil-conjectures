/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Global functions on `Spec κ(x)`, and the non-vanishing locus of a global function

The canonical morphism `Spec κ(x) ⟶ X` of `AlgebraicGeometry.Scheme.fromSpecResidueField` acts
on global functions by evaluation at `x`, once `Γ(Spec κ(x), 𝒪)` is identified with `κ(x)`.
We also record that the basic open subset of a global function is its non-vanishing locus, so
that a global function is a unit exactly when it vanishes nowhere.

## Main results

- `AlgebraicGeometry.Scheme.fromSpecResidueField_appTop`: the map on global functions induced by
  `Spec κ(x) ⟶ X` is the evaluation `AlgebraicGeometry.Scheme.Γevaluation` at `x`.
- `AlgebraicGeometry.Scheme.Γevaluation_eq_zero_iff_notMem_basicOpen`: a global function
  evaluates to zero at `x` exactly when `x` is outside its basic open subset.
- `AlgebraicGeometry.Scheme.isUnit_iff_forall_Γevaluation_ne_zero`: a global function is a unit
  exactly when it evaluates to a non-zero element of every residue field.
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

/-- **A global function evaluates to zero at `x` exactly when `x` is outside its basic open
subset.** This is `AlgebraicGeometry.Scheme.evaluation_eq_zero_iff_notMem_basicOpen` over the top
open. -/
@[simp]
lemma Γevaluation_eq_zero_iff_notMem_basicOpen (X : Scheme.{u}) (x : X) (s : Γ(X, ⊤)) :
    X.Γevaluation x s = 0 ↔ x ∉ X.basicOpen s :=
  X.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) x trivial s

lemma Γevaluation_ne_zero_iff_mem_basicOpen (X : Scheme.{u}) (x : X) (s : Γ(X, ⊤)) :
    X.Γevaluation x s ≠ 0 ↔ x ∈ X.basicOpen s := by
  simp

/-- **A global function is a unit exactly when it vanishes nowhere**, that is when its image in
every residue field is non-zero. -/
lemma isUnit_iff_forall_Γevaluation_ne_zero (X : Scheme.{u}) (s : Γ(X, ⊤)) :
    IsUnit s ↔ ∀ x : X, X.Γevaluation x s ≠ 0 := by
  rw [X.isUnit_iff_basicOpen_eq_top]
  simp [eq_top_iff, SetLike.le_def]

end AlgebraicGeometry.Scheme

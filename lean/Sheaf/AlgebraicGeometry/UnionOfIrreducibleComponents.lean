/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
/-!
# Unions of boundary components

Source: ILO, Travaux de Gabber, Expose VIII, 4.1.2, Remark 4.2.2(i), and Lemma 4.2.9,
printed pp. 117--121 (blueprint: def-trf-union-of-irreducible-components).
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace AlgebraicGeometry
/-- Every irreducible component of `H` is an irreducible component of `B`.
Source: ILO, Exposé VIII, Remark 4.2.2(i) (blueprint: def-trf-union-of-irreducible-components). -/
def IsUnionOfIrreducibleComponents {X : Scheme.{u}}
    (H B : X.IdealSheafData) : Prop :=
  ∀ Z : Set X, IsIrreducible Z → IsClosed Z →
    ((Z ⊆ (H.support : Set X)) ∧
      (∀ Z' : Set X, IsIrreducible Z' → IsClosed Z' →
        Z ⊆ Z' → Z' ⊆ (H.support : Set X) → Z' = Z)) →
    ((Z ⊆ (B.support : Set X)) ∧
      (∀ Z' : Set X, IsIrreducible Z' → IsClosed Z' →
        Z ⊆ Z' → Z' ⊆ (B.support : Set X) → Z' = Z))
end AlgebraicGeometry

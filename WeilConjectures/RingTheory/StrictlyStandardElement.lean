/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Elementary standard and strictly standard elements

## Main definitions

* `Algebra.IsElementaryStandardElement`: one initial Jacobian minor divides the element.
* `Algebra.IsStrictlyStandardElement`: the element is a linear combination of all minors.

## Implementation details

The relation conditions use the lift `P.σ a` in the polynomial ring. Changing the lift changes
its product with a relation by an element of the square of the relation ideal, so membership in
the indicated ideal does not depend on the choice. In the strictly standard case the columns of
each minor are ordered increasingly.

## References

* [Stacks, Tag 07C7]
-/

@[expose] public section

universe u v

namespace Algebra

open MvPolynomial

/-- An element is elementary standard when one finite presentation has an initial Jacobian
minor dividing it and its remaining relations satisfy the ideal-square condition. -/
def IsElementaryStandardElement {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] [FinitePresentation R A] (a : A) : Prop :=
  ∃ (n m c : ℕ) (P : Presentation R A (Fin n) (Fin m))
    (hc : c ≤ min n m) (a' : A),
    a = a' * Matrix.det (fun i j : Fin c =>
      aeval P.val (pderiv (Fin.castLE (le_trans hc (min_le_left n m)) i)
        (P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j)))) ∧
    ∀ j : Fin m, c ≤ j.val →
      P.σ a * P.relation j ∈
        Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = P.relation k} +
          (Ideal.span (Set.range P.relation)) ^ 2

/-- An element is strictly standard when it is a linear combination of all Jacobian minors
of a finite presentation and its remaining relations satisfy the ideal-square condition. -/
def IsStrictlyStandardElement {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] [FinitePresentation R A] (a : A) : Prop :=
  ∃ (n m c : ℕ) (P : Presentation R A (Fin n) (Fin m))
    (hc : c ≤ min n m) (a' : {s : Finset (Fin n) // s.card = c} → A),
    a = ∑ s : {s : Finset (Fin n) // s.card = c}, a' s *
      Matrix.det (fun j i : Fin c =>
        aeval P.val (pderiv (s.val.orderEmbOfFin s.property i)
          (P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j)))) ∧
    ∀ j : Fin m, c ≤ j.val →
      P.σ a * P.relation j ∈
        Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = P.relation k} +
          (Ideal.span (Set.range P.relation)) ^ 2

end Algebra

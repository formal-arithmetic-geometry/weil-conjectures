/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u

namespace WeilConjectures.DerivedTotalResolution

variable {R : Type u} [Ring R]

/-- Every total element in a left half-plane bicomplex has a finite column expansion.
Source: Stacks Project, Homology, Tag 09IZ, proof, finite-support representation.
(blueprint: aux-total-resolution-cycle-finite-support)

Proof. In degree n the categorical coproduct of the modules K^(p,q), p+q=n,
is isomorphic to their algebraic direct sum. Transport the given element across
this isomorphism. Its nonzero coordinates form a finite set. A positive column
is zero by h_positive, so all nonzero coordinates have p <= 0. Choose r bounding
all the natural numbers -p in this finite set (r=0 for the empty set). Define
x_i to be the coordinate in bidegree (-i,n+i), using zero when absent. The direct
sum reconstruction formula gives exactly the displayed finite sum. This uses
neither a cycle condition nor horizontal exactness. -/
theorem total_resolution_element_finite_support
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (n : ℤ)
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (z : (K.total (ComplexShape.up ℤ)).X n) :
    ∃ r : ℕ, ∃ x : ∀ i : ℕ, (K.X (-(i : ℤ))).X (n + (i : ℤ)),
      z = ∑ i ∈ Finset.range (r + 1),
        K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n (x i) := by
  sorry

end WeilConjectures.DerivedTotalResolution

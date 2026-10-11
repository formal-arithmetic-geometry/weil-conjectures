/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.RingTheory.StrictlyStandardElement
public import Mathlib.RingTheory.FiniteStability

/-!
# Base change of elementary and strictly standard elements

Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07CC
(blueprint: lem-weil-pbc-strictly-standard-base-change).

Mathlib writes the base change as `R' ⊗[R] A`, with its canonical left `R'`-algebra
structure. Tensor commutativity identifies `1 ⊗ a` with the source's `a ⊗ 1`
in `A ⊗[R] R'` as an `R'`-algebra.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- Elementary standard and strictly standard elements remain so under arbitrary base change.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07CC
(blueprint: lem-weil-pbc-strictly-standard-base-change).

Proof:
1. Choose the presentation and integer `c` witnessing the given standardness
   (def-weil-pbc-strictly-standard-element). Base change the presentation, keeping the
   same numbers of variables and relations and the same `c`
   (def-weil-pbc-finitely-presented-algebra, lem-weil-pbc-presentation-base-change).
   The resulting algebra is finitely presented
   (lem-weil-pbc-finite-presentation-base-change-composition).
2. The new presentation map composed with the coefficient map equals the old presentation
   map followed by the tensor inclusion: both maps agree on coefficients and variables
   (def-weil-pbc-mv-polynomial-ring). In particular a polynomial lift of `a` maps to a lift
   of `1 ⊗ a`, and the relation ideals map into the new relation ideals.
3. Partial derivatives commute with the coefficient map
   (lem-weil-pbc-partial-derivative-coefficient-map,
   def-weil-pbc-polynomial-partial-derivative). The determinant's Leibniz formula then
   shows that every Jacobian minor maps to the corresponding new minor.
4. Apply the tensor inclusion to the elementary standard multiple identity, respectively
   the strictly standard sum identity. This gives the first condition of
   def-weil-pbc-strictly-standard-element with the base-changed coefficients.
5. Apply the coefficient map to each expression of a lifted element times a remaining
   relation in the ideal of the first `c` relations plus the square of the relation ideal.
   The resulting expression satisfies the second condition in the new presentation.
   Independence of the polynomial lift is part of def-weil-pbc-strictly-standard-element.
   These witnesses establish both conclusions. -/
theorem standardElements_baseChange
    {R : Type u} {A : Type v} {R' : Type w}
    [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    [FinitePresentation R A] (a : A) :
    (IsElementaryStandardElement (R := R) a →
      IsElementaryStandardElement (R := R') (1 ⊗ₜ[R] a : R' ⊗[R] A)) ∧
    (IsStrictlyStandardElement (R := R) a →
      IsStrictlyStandardElement (R := R') (1 ⊗ₜ[R] a : R' ⊗[R] A)) := by
  sorry

end Algebra

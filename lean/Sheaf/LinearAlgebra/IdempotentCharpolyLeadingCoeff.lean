/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.LinearAlgebra.IdempotentCharpoly

/-! # Idempotent leading coefficient of a summand determinant

Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), characteristic-polynomial
paragraph, with the finite-projective local calculation made explicit.
(blueprint: lem-weil-pbc-idempotent-charpoly-leading-coeff)
-/

@[expose] public section

universe u v

namespace Matrix

/-- The leading coefficient of the determinant on a commuting idempotent summand
is itself idempotent.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), characteristic-polynomial paragraph.
(blueprint: lem-weil-pbc-idempotent-charpoly-leading-coeff)

Proof: split the ambient finite free module into the images of P and 1-P. Both
summands are finite projective. Choose and refine finite standard free covers for
these two modules. On each nonzero cover localization an adapted basis identifies
1-P+(X-T)P with the block diagonal matrix diag(X-T_image,1), so its determinant is
monic of degree r, the rank of the image of P. Let d be the natural degree of the
original determinant. Degree cannot increase under localization, so r ≤ d. Its
coefficient at d is therefore 1 if r=d, and 0 if r<d. Thus the image of the original
leading coefficient is idempotent on every member of the cover. On a zero
localization the same equation holds trivially. Apply injectivity on the standard
cover to the element leadingCoeff²-leadingCoeff to conclude the equation over A.
For the zero ring the equation is automatic. -/
theorem isIdempotentElem_idempotentCharpoly_leadingCoeff
    {A : Type u} [CommRing A] {n : Type v} [Fintype n] [DecidableEq n]
    (T P : Matrix n n A) (hP : P * P = P) (hTP : T * P = P * T) :
    IsIdempotentElem (idempotentCharpoly T P).leadingCoeff := by sorry

end Matrix

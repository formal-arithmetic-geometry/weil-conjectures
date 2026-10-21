/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem

/-! # Arbitrary base change for the normalized finite projective-line system -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- The normalized unit and Kummer decompositions satisfy their canonical exchange squares.
Source: det-sp-p1-trace, proof paragraphs 1--2, arbitrary-base-change clauses.
(blueprint: lem-sp-p1-base-change-normalized)

Proof: the normalized Kummer arrow is the scalar Kummer boundary of O(1).
Kummer naturality and the canonical pullback identification of O(1) identify
its inverse image with the specified normalized arrow over the new base.
The two components of the ordinary untwisted decomposition commute with
exchange: the unit by the mate triangle identity, and the tensor-Chern adjunct
by pullback of the Chern arrow, tensor naturality, and normalized evaluation.
Comparison pullback is exact and its pullback square is the derived image of
the site square. Taking mates carries these two component identities to the
pro-etale direct-image square; biproduct extensionality gives the first formula.
The same calculation with the shifted positive line gives the square for the
twisted decomposition. Precompose with its pulled-back isomorphism and cancel.
The second projection of the source comparison is the pulled-back second
projection followed by the constant comparison. Thus the inverse decomposition
followed by that projection satisfies the claimed trace square. All exchange
arrows here are the specified mates, so no choice of an exchange isomorphism
is made, and the argument permits every base morphism, including non-Noetherian
bases, the empty scheme, and the zero coefficient ring. -/
theorem spP1BaseChange_of_normalized (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
    (d : SpP1DecompositionFamily A N hA)
    (hnorm : SpP1NormalizedDecompositions A N hN hA c b d) :
    SpP1BaseChange A N hN hA b d := by
  sorry

end AlgebraicGeometry.ProEtale

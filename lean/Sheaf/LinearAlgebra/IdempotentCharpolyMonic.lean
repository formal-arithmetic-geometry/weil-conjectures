/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.LinearAlgebra.IdempotentCharpoly
public import Mathlib.RingTheory.Jacobson.Ideal

/-! # Monicity of the determinant on an idempotent summand

Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), constant-rank argument.
(blueprint: lem-weil-pbc-idempotent-charpoly-monic)
-/

@[expose] public section

universe u v

namespace Matrix

/-- A commuting idempotent summand has a monic determinant polynomial when its
reduction modulo a Jacobson ideal is monic.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1).
(blueprint: lem-weil-pbc-idempotent-charpoly-monic)

Proof: the image of P and the image of 1-P split the ambient finite free module.
They are finite projective, hence free on a finite standard cover. In a basis adapted
to this splitting, the determinant defining `idempotentCharpoly T P` is the ordinary
characteristic polynomial of T on the image of P, multiplied by the determinant of
an identity matrix. Consequently it is monic of degree equal to the rank of that image
on every such localization. This rank is locally constant on Spec A. If A is nonzero,
A/I is nonzero because I lies in the Jacobson radical. Write n for the degree of the
assumed monic reduction. At every prime containing I the adapted determinant, reduced
to the residue field, has degree equal to the rank, while the monic reduction has
degree n; hence the rank is n. The closed locus where the rank differs from n must be
empty: otherwise it contains a maximal ideal, and every maximal ideal contains I.
Thus every nonzero cover localization has rank n. On zero localizations the polynomial
is zero, equal to every monic expansion. Locally the coefficients above n vanish and
the coefficient at n is one. Injectivity of the standard-cover localization map
makes these coefficient statements hold in A, proving monicity. If A is the zero
ring, its only polynomial is monic by the definition of leading coefficient. -/
theorem idempotentCharpoly_monic_of_map_monic
    {A : Type u} [CommRing A] {n : Type v} [Fintype n] [DecidableEq n]
    (I : Ideal A) (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (T P : Matrix n n A) (hP : P * P = P) (hTP : T * P = P * T)
    (hmonic : ((idempotentCharpoly T P).map (Ideal.Quotient.mk I)).Monic) :
    (idempotentCharpoly T P).Monic := by
  sorry

end Matrix

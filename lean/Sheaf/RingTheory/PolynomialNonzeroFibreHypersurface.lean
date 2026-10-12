/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# A hypersurface presentation of a nonzero polynomial fibre

Source: Stacks Project, More on Algebra, proof of Lemma 07PU, second paragraph,
with the characteristic-zero separability argument in the proof of Proposition 07PV.
(blueprint: lem-weil-pbc-polynomial-nonzero-fibre-hypersurface)
-/

@[expose] public section

universe u v

namespace Polynomial

/-- A nonzero polynomial prime over zero gives a hypersurface after inverting the
nonzero base elements, and its equation has invertible derivative in that quotient.
Source: Stacks Project, More on Algebra, proof of Lemma 07PU, second paragraph,
and proof of Proposition 07PV, regular-base characteristic-zero case.
(blueprint: lem-weil-pbc-polynomial-nonzero-fibre-hypersurface)

Proof:
Let K be the fraction field of A. Since r contracts to zero, its extension to K[X]
is prime; since localization of the domain A[X] is injective, it is nonzero.
The principal ideal domain K[X] gives an irreducible generator g. Clear its finitely
many coefficient denominators and the denominator expressing g in the extended ideal
to obtain f in r whose image generates r K[X]. Multiplication by the resulting
nonzero scalar does not change this ideal. The contraction of (g) is r.
The quotient K[X]/(g) is a field and is the residue field of r: localizing A[X]/r
at nonzero constants already gives this field, so inverting all other nonzero
classes changes nothing. Thus, for any A[X]-algebra S, tensoring with this field
identifies r.Fiber S with R/(image f), where R inverts the nonzero constants in S.
In characteristic zero the irreducible g is separable, hence g and g' are coprime.
The scalar multiple representing f is also coprime to its derivative. A Bezout
identity in K[X] descends to R/(image f) and supplies an inverse for image(f').
These statements also hold for the zero S-algebra: all rings in the presentation
are zero, and zero is a unit in the zero ring. No choice of a ring construction is
made from this existence statement; R is the explicit localization below. -/
theorem nonzero_fibre_hypersurface_presentation
    (A : Type u) [CommRing A] [IsDomain A] [CharZero A]
    (S : Type v) [CommRing S] [Algebra (Polynomial A) S]
    (r : Ideal (Polynomial A)) [r.IsPrime] (hr : r ≠ ⊥)
    (hrA : r.comap (C : A →+* Polynomial A) = ⊥) :
    let M := Submonoid.map
      ((algebraMap (Polynomial A) S).comp C).toMonoidHom (nonZeroDivisors A)
    let R := Localization M
    ∃ f : Polynomial A,
      Nonempty (r.Fiber S ≃+* R ⧸ Ideal.span ({algebraMap (Polynomial A) R f} : Set R)) ∧
      IsUnit (Ideal.Quotient.mk (Ideal.span ({algebraMap (Polynomial A) R f} : Set R))
        (algebraMap (Polynomial A) R (derivative f))) := by sorry

end Polynomial

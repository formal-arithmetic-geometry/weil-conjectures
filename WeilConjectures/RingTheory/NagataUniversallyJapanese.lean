/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.FiniteOverNagata
import WeilConjectures.RingTheory.PolynomialNagata
import WeilConjectures.RingTheory.NagataDomainN2

/-!
# Nagata rings are universally Japanese

A Nagata ring is universally Japanese: every finite type domain over it is N-2.

## Implementation details

A finite type algebra is a quotient of `MvPolynomial (Fin n) R`, which is Nagata by induction on
`n`; the one-variable step reduces prime quotients to injective monogenic extensions of Nagata
domains. Nagata transfers along the surjective presentation by `finite_over_nagata_is_nagata`,
and a Nagata domain is N-2 by `isN2_of_isNagataRing_domain`.

## References

* [Stacks, Tag 0334] ((1) implies (3))
-/

@[expose] public section

universe u

private theorem isNagataRing_of_surjective (A B : Type u) [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (hA : IsNagataRing A) :
    IsNagataRing B := by
  let : Algebra A B := f.toAlgebra
  let : Module.Finite A B := Module.Finite.of_surjective (Algebra.linearMap A B) hf
  exact (finite_over_nagata_is_nagata A B hA).1

private theorem isNagataRing_mvPolynomial (R : Type u) [CommRing R]
    (hR : IsNagataRing R) (n : ℕ) : IsNagataRing (MvPolynomial (Fin n) R) := by
  induction n with
  | zero =>
      exact isNagataRing_of_surjective R _
        (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm.toRingHom
        (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm.surjective hR
  | succ n ih =>
      exact isNagataRing_of_surjective (Polynomial (MvPolynomial (Fin n) R)) _
        (MvPolynomial.finSuccEquiv R n).symm.toRingHom
        (MvPolynomial.finSuccEquiv R n).symm.surjective
        (isNagataRing_polynomial _ ih)

/-- A Nagata ring is universally Japanese: every finite type domain algebra is N-2.
-/
theorem isUniversallyJapanese_of_isNagataRing (R : Type u) [CommRing R]
    (hR : IsNagataRing R) : IsUniversallyJapanese R := by
  intro S _ _ _ _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  have hS := isNagataRing_of_surjective (MvPolynomial (Fin n) R) S f.toRingHom hf
    (isNagataRing_mvPolynomial R hR n)
  exact isN2_of_isNagataRing_domain S hS

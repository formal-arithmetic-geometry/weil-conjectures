/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing

import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# A finite coefficient model for a polynomial residue field extension

Source: Stacks Project, More on Algebra, Tag 07PU, first paragraph.
-/

@[expose] public section

universe u

namespace Polynomial

/-- A finite extension of a nonzero polynomial residue field above zero has a finite
coefficient model inside the extension field. Its evaluation prime has that extension
as residue field, compatibly with the original polynomial map.
Source: Stacks Project, More on Algebra, Tag 07PU, first paragraph.
(blueprint: lem-weil-pbc-polynomial-residue-finite-coefficient-model)

Proof:
Let K be the fraction field of A. Localization at the nonzero elements of A carries
r to a nonzero prime of K[X]. A nonzero prime of the PID K[X] is maximal, and its
quotient is finite over K, by reducing powers of X modulo a monic generator.
Localization preserves the residue field, so kappa(r), and then L, is finite over K.
Scale a finite K-basis of L by a common nonzero element of A so all basis elements
are integral over A. Let B be their A-subalgebra in L. Finite integral generation
makes B finite over A. Clearing denominators of the coordinates of each element of
L expresses it as a quotient of elements of B, so L is a fraction field of B.
Evaluate B[X] in L with X equal to the image of X under A[X] to kappa(r) to L.
Let s be the kernel. It is prime since L is a field and contracts to zero in B
since B is a subalgebra of L. A nonzero polynomial in r stays nonzero under the
injective coefficient map A[X] to B[X] and lies in s, so s is nonzero.
The quotient B[X]/s embeds in L and contains B. Since L is the fraction field of
B, it is also the fraction field of this quotient: every element is a quotient
of elements of B. Uniqueness of fraction fields identifies kappa(s) with L.
This identification is a B-algebra equivalence and agrees with evaluation on
B[X], hence on the mapped polynomials from A[X]. Transporting the fraction-field
structure along this equivalence proves the last required structure. -/
theorem exists_finite_coefficient_model
    (A : Type u) [CommRing A] [IsDomain A]
    (r : Ideal (Polynomial A)) [r.IsPrime] (hr : r ≠ ⊥)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥)
    (L : Type u) [Field L] [Algebra r.ResidueField L] [Module.Finite r.ResidueField L] :
    letI : Algebra A L :=
      ((algebraMap r.ResidueField L).comp
        ((algebraMap (Polynomial A) r.ResidueField).comp Polynomial.C)).toAlgebra
    ∃ B : Subalgebra A L, Module.Finite A B ∧
      ∃ (s : Ideal (Polynomial B)) (hs : s.IsPrime),
        letI := hs
        s ≠ ⊥ ∧ s.comap (Polynomial.C : B →+* Polynomial B) = ⊥ ∧
          IsFractionRing B s.ResidueField ∧
          ∃ e : s.ResidueField ≃ₐ[B] L,
            ∀ f : Polynomial A,
              e (algebraMap (Polynomial B) s.ResidueField
                (Polynomial.map (algebraMap A B) f)) =
                algebraMap r.ResidueField L (algebraMap (Polynomial A) r.ResidueField f) := by
  sorry

end Polynomial

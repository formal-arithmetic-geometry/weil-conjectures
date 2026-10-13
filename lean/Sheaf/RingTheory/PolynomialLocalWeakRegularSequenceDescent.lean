/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence

/-! # Finite-coefficient descent for localized weakly regular sequences

Source: Stacks Project, Algebra, Tag 00SV, filtered-colimit paragraphs of the proof,
and Tag 00DB (exactness of filtered colimits).
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

/-- Weak regularity in polynomial local rings passes from all finite type coefficient
subrings containing a fixed finite type subring to the full coefficient ring.
Source: Stacks Project, Algebra, Tag 00SV, filtered-colimit paragraphs of the proof;
Tag 00DB supplies preservation of injective multiplication maps.
(blueprint: lem-weil-pbc-polynomial-local-weak-regular-sequence-descent).

Proof: Index by the finite type integer subrings `B` containing `R₀`, ordered by inclusion.
This is a nonempty directed set: `R₀` is one stage and adjoining the finite generating sets
of two stages yields a common stage. Every finite set of coefficients of `R` occurs in
some stage by adjoining it to the generators of `R₀`. Contract `Q` to each polynomial
ring over `B`; contraction preserves primality and makes all localization maps compatible.
Every fraction in `R[x]_Q` comes from a stage containing the coefficients of its numerator
and denominator. A fraction that becomes zero is killed by a polynomial outside `Q`;
adjoining its coefficients makes the fraction zero at a later stage. Thus these polynomial
local rings have colimit `R[x]_Q`. For each prefix of the given list the same holds for
the prefix quotient: clear denominators in an expression of ideal membership and adjoin
the finitely many coefficients of the expression and its killing denominator.
Multiplication by the next equation on these quotient modules is compatible with the
transition maps and injective at every stage by `hstage`. Exactness of filtered colimits
of abelian groups (00DB) preserves injectivity. Under the quotient identifications this
is exactly `IsSMulRegular` on each successive quotient of `R[x]_Q`, hence weak regularity.
No properness conclusion is claimed; for an empty list weak regularity is automatic.
The proof does not assume flatness of any coefficient-subring inclusion.
-/
theorem isWeaklyRegular_polynomial_local_of_finiteType_subrings
    {R : Type u} [CommRing R] (R₀ : Subring R)
    (hR₀ : Algebra.FiniteType ℤ R₀) {n c : ℕ}
    (f₀ : Fin c → MvPolynomial (Fin n) R₀)
    (Q : Ideal (MvPolynomial (Fin n) R)) [Q.IsPrime]
    (hstage : ∀ (B : Subring R) (hB : R₀ ≤ B), Algebra.FiniteType ℤ B →
      IsWeaklyRegular
        (Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype)))
        ((List.ofFn (fun i ↦ MvPolynomial.map (Subring.inclusion hB) (f₀ i))).map
          (algebraMap (MvPolynomial (Fin n) B)
            (Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype)))))) :
    IsWeaklyRegular (Localization.AtPrime Q)
      ((List.ofFn (fun i ↦ MvPolynomial.map R₀.subtype (f₀ i))).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q))) := by sorry

end RingTheory.Sequence

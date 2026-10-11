/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Local regularity of equations of a relative global complete intersection

Source: Stacks Project, Algebra, Lemma Tag 00SV, assertion (1)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-local-regular-sequence).
-/

@[expose] public section

universe w

namespace Algebra

/-- The equations of a relative global complete intersection presentation form a regular
sequence in the polynomial local ring at the inverse image of any prime of its quotient.
Source: Stacks Project, Algebra, Lemma Tag 00SV, assertion (1)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-local-regular-sequence).

Proof:
1. When `R` is Noetherian, the polynomial ring is free, hence flat over `R`, and Noetherian.
Localizing at the inverse image prime gives a flat local map from the localization of `R` at
its contraction (`lem-weil-pbc-flat-local-ring-maps`, polynomial freeness and the finite-type
Noetherian lemma).
2. Polynomial scalar extension and the fibre-prime correspondence identify its closed fibre
with a localization of a polynomial ring over the residue field. Base change preserves the
specified complete intersection presentation (00SS); its fibre has dimension `n - c`.
The field-case lemma 00SC gives regularity of the equations in this fibre local ring
(`lem-weil-pbc-global-complete-intersection-local-regular-sequence` and the natural fibre-local
ring isomorphism).
3. Grothendieck's regular-sequence lemma 00MG lifts this regularity through the flat local map
(`lem-weil-pbc-grothendieck-regular-sequence-flat`). For `c = 0` the local ring is nonzero.
4. For arbitrary `R`, descend the coefficients and the complete intersection presentation to
a finite type integer subalgebra by 00SU. Enlarge it through all finitely generated subrings
of `R`; these are Noetherian, and 00SS preserves the complete intersection condition.
5. Localize each polynomial ring at the contracted prime. Their filtered colimit is the
specified polynomial local ring: each fraction has finitely many coefficients; a relation
vanishing in the colimit already vanishes after adjoining the coefficients of a denominator
that kills it. The same argument identifies every partial quotient with its filtered colimit.
6. At each Noetherian stage multiplication by the next equation on the preceding partial
quotient is injective. Exactness of filtered colimits (00DB,
`lem-weil-pbc-filtered-colimit-abelian-groups-exact`) preserves this injectivity. The final
quotient is the localization of the given quotient at its prime, so is nonzero. These are
exactly the two conditions in `RingTheory.Sequence.IsRegular`. -/
theorem isRegular_localization_of_relativeGlobalCompleteIntersection
    {R : Type w} [CommRing R] {n c : ℕ}
    (relations : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation relations)
    (q : Ideal (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range relations))) [q.IsPrime] :
    RingTheory.Sequence.IsRegular
      (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span (Set.range relations)))))
      (List.ofFn fun i : Fin c ↦
        algebraMap (MvPolynomial (Fin n) R)
          (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span (Set.range relations)))))
          (relations i)) := by
  sorry

end Algebra

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Ideal.Span
import WeilConjectures.RingTheory.KoszulConormalBasis
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Koszul regularity under an equal-length change of generators

Source: Stacks Project, More on Algebra, Tag 066A,
lemma-independence-of-generators, part (3)
(blueprint: lem-sfb-koszul-equal-length-generators).
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

/-- Equal-length tuples generating the same ideal are simultaneously Koszul-regular.
Source: Stacks Project, More on Algebra, Tag 066A,
lemma-independence-of-generators, part (3)
(blueprint: lem-sfb-koszul-equal-length-generators).

Proof:
1. Put I = (a) = (b) and B = A/I. Assuming a is Koszul-regular,
   `lem-sc-koszul-conormal-basis` identifies B^r with I/I^2 using the classes of a.
2. Write b_j = sum_i c_ij a_i and let t(e_j) = sum_i c_ij e_i. The linear
   functionals alpha(e_i) = a_i and beta(e_i) = b_i satisfy alpha composed with
   t = beta. Modulo I, the matrix C of t is surjective: the classes of b generate
   I/I^2, which the preceding basis identifies with B^r.
3. By `lem-weil-pbc-finite-module-surjective-endomorphism-bijective`, this
   surjective endomorphism of the finite free B-module B^r is bijective. Taking
   determinants of its inverse shows that det(C) is a unit modulo I. This remains
   valid for the zero quotient ring and for r = 0, whose determinant is 1.
4. Apply `lem-sfb-koszul-substitution-unit-mod-ideal`: the exterior powers of t
   give a quasi-isomorphism from K(b) to K(a). By
   `def-weil-abstract-derived-category`, quasi-isomorphisms preserve homology,
   so positive homology of K(b) vanishes. The recorded definition
   `def-weil-pbc-koszul-regular-sequence` gives Koszul regularity of b.
   Exchange a and b for the reverse implication.
-/
theorem isKoszulRegular_iff_of_span_eq
    {A : Type u} [CommRing A] {r : ℕ} (a b : Fin r → A)
    (hspan : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    IsKoszulRegular a ↔ IsKoszulRegular b := by
  sorry

end RingTheory.Sequence

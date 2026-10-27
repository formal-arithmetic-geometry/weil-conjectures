module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.Height

/-!
# A birational dimension-one local overring

Source: Stacks Project, Algebra, Tag 00P8, lemma-dominate-by-dimension-1,
clauses (1) and (2), with the fraction-field consequence of the inclusions.
(blueprint: lem-sfb-local-domain-birational-dimension-one).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace IsLocalRing

/-- A nonfield Noetherian local domain admits a dominating Noetherian local
subalgebra of dimension one inside its specified fraction field.

Source: Stacks Project, Algebra, Tag 00P8, lemma-dominate-by-dimension-1,
clauses (1) and (2).
(blueprint: lem-sfb-local-domain-birational-dimension-one).

Proof:
1. Choose finitely many generators of the maximal ideal of B using
   `def-weil-pbc-noetherian-ring`. Remove zero entries; the resulting list is
   nonempty because the maximal ideal is nonzero.
2. By `lemma-nagata-local-domain-valuation-dominates`, choose a valuation
   subring A of K dominating B. Using `def-trf-valuation-ring`, choose a
   nonzero generator a such that every generator x has x/a in A. For a finite
   list, retain a when x/a is in A, and otherwise replace a by x; the previous
   quotients remain in A since then a/x is in A. Also a is in the maximal ideal of A.
3. Form S = B[x/a] inside K over these finitely many generators. It is contained
   in A and is Noetherian by `lem-weil-pbc-finite-type-algebra-noetherian`.
   The extended maximal ideal of B is aS, since x = a(x/a) and a belongs to that ideal.
4. The ideal aS is proper, since a is a nonunit of A. Choose a prime q minimal
   over aS using `lem-weil-pbc-minimal-prime-over-proper-ideal`. Its contraction
   to B contains the maximal ideal and is proper, so equals the maximal ideal.
5. Apply `lem-weil-pbc-noetherian-height-quotient-bound` to the single element a.
   The height of q/(a) in S/(a) is zero: a smaller prime would pull back to a
   prime between (a) and q, contradicting minimality. Thus the height of q is at
   most one. Since S is a domain and q contains the nonzero a, the chain
   (0) strictly below q gives the reverse inequality.
6. Define R as the actual subring of K consisting of s/t with s in S and
   t in S outside q. Cross multiplication identifies it with S localized at q
   (`def-weil-pbc-localization-at-prime`). Its maximal ideal consists of the
   fractions whose numerators lie in q; fractions outside it have inverses.
   It is a nonzero integral domain as a subring of K.
7. By `lem-weil-pbc-localization-noetherian`, R is Noetherian. By
   `lem-weil-pbc-localization-dimension-chains-below-prime`, its dimension is
   the height of q, hence one.
8. A fraction b/1 for b in B belongs to the maximal ideal of R precisely when
   b lies in q, equivalently in the maximal ideal of B. Every element of K
   remains a fraction of elements of R since B is contained in R. Cross
   multiplication in the subring of K gives the injectivity required for its
   fraction field to be K with the prescribed embedding.
-/
theorem exists_birational_dimension_one_subalgebra
    (B : Type u) (K : Type v) [CommRing B] [IsDomain B] [IsLocalRing B]
    [IsNoetherianRing B] [Field K] [Algebra B K] [IsFractionRing B K]
    (hB : IsLocalRing.maximalIdeal B ≠ ⊥) :
    ∃ (R : Subalgebra B K) (_ : IsNoetherianRing R) (_ : IsLocalRing R),
      ringKrullDim R = 1 ∧
      (IsLocalRing.maximalIdeal R).comap (algebraMap B R) = IsLocalRing.maximalIdeal B ∧
      IsFractionRing R K := by
  sorry

end IsLocalRing

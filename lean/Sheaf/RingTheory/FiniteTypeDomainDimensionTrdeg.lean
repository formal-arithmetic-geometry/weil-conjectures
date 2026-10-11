import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Dimension of a finite type domain over a field

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00P0
(blueprint: lem-weil-pbc-finite-type-domain-dimension-trdeg).

## Main statement

The Krull dimension of a finite type domain `S` over a field `k` equals the
transcendence degree of its fraction field, and localization at a maximal
ideal has the same dimension.
-/

universe u v

/--
Dimension of a finite type domain over a field equals the transcendence degree
of its fraction field, with the same dimension at every maximal localization.
Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00P0
(blueprint: lem-weil-pbc-finite-type-domain-dimension-trdeg).

Proof route: write the finite type domain as a quotient of a polynomial ring;
the finite type domain local-dimension lemma gives a finite common dimension
for all maximal localizations. Noether normalization supplies an injective
finite map from a polynomial ring in `d` variables, and integrality preserves
Krull dimension; the polynomial-ring localization computes this dimension as
`d`. After localizing the finite module at the nonzero elements of the
polynomial subring, the resulting finite-dimensional domain is a field, hence
is the fraction field of the original domain. Thus the fraction field is
algebraic over the rational function field in the normalization variables;
those variables are a transcendence basis, so `Algebra.trdeg` is `d`, equal to
the ring dimension and to every maximal-localization dimension. This follows
the proof dependencies `lem-weil-pbc-finite-type-domain-dimension-local-ring`,
`lem-weil-pbc-noether-normalization-field`,
`lem-weil-pbc-finite-algebra-is-integral`,
`lem-weil-pbc-integral-injective-dimension-equal`,
`lem-weil-pbc-polynomial-ring-maximal-localization-dimension`,
`lem-weil-pbc-finite-dimensional-domain-is-field`,
`def-weil-pbc-transcendence-basis`, and
`def-kun-transcendence-degree`.
-/
theorem finiteType_domain_ringKrullDim_eq_trdeg
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S] :
    ∃ d : ℕ,
      ringKrullDim S = (d : WithBot ℕ∞) ∧
      Algebra.trdeg k (FractionRing S) = (d : Cardinal) ∧
      ∀ (m : Ideal S) [m.IsMaximal],
        ringKrullDim (Localization.AtPrime m) = (d : WithBot ℕ∞) := by
  sorry

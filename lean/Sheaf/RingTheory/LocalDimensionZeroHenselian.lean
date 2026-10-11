import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Local rings of dimension zero are henselian

Source: Stacks Project, Algebra, Lemma Tag 06RS (blueprint:
lem-weil-pbc-local-dimension-zero-henselian).

A local ring whose Krull dimension is zero is henselian: Mathlib's `HenselianLocalRing`
(the henselian local rings of `def-weil-pbc-henselian-terminology`), together with the
node's idempotent-lifting condition written inline, as in the landed sibling
`isStrictlyHenselianLocalRing_of_ringKrullDim_eq_zero`.
-/

universe u v

/-- A local ring of Krull dimension zero is henselian
(blueprint: lem-weil-pbc-local-dimension-zero-henselian).
Source: Stacks Project, Algebra, Lemma Tag 06RS, with Tag 04GG (10) implies (1).

The hypothesis that `m` is the only prime of `R` is `ringKrullDim R = 0`
(`def-weil-pbc-krull-dimension-ring`), equivalent for a local ring. The conclusion is
`HenselianLocalRing R` (`def-weil-pbc-henselian-terminology`) together with the node's
wording: for every finite `R`-algebra `B`, every idempotent of `B ⧸ mB` lifts uniquely to an
idempotent of `B`.

Proof: (1) By `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`, a finite
`R`-algebra `B` has finitely many prime ideals, all maximal and over the unique prime of `R`;
their intersection is nil. The zero algebra is included, with no primes.
(2) By `lem-weil-pbc-product-of-localizations-at-maximal`, `B` is the product of its
localizations at these maximal ideals, as an `R`-algebra.
(3) Reduction modulo the extended maximal ideal is computed factorwise. In each local
factor the extended ideal lies in its maximal ideal, so the quotient is nonzero and local.
(4) The only idempotents of a local ring are zero and one, so idempotents on both sides of
reduction are the same zero/one vectors and reduction is bijective on them. This is the
idempotent-lifting condition; it is equivalent to `HenselianLocalRing R` by
`lem-weil-pbc-henselian-local-root-lifting`. -/
theorem isHenselianLocalRing_of_ringKrullDim_eq_zero
    (R : Type u) [CommRing R] [IsLocalRing R] (hdim : ringKrullDim R = 0) :
    HenselianLocalRing R ∧
      ∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Module.Finite R B],
        ∀ e : B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B),
          IsIdempotentElem e →
            ∃! b : B, IsIdempotentElem b ∧
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B)) b = e := by
  sorry
